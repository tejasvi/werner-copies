"""Anchor-relative metric and fixed selection from the analytic centre at a reference node n_ref.
  L_t = n^{F_t} Ri_t chol(D_t)  (so that Y = L^{-1} Zhat L^{-T} = I at n_ref), rounded to Lnum/Lden (Lden = 2^E).
  Selection: pivoted QR on [equality columns | relative Gram columns] at n_ref.
Usage: select_rel.py n_ref ac.pkl blocks_cache.pkl cols.npz out_rel.pkl"""
import sys, pickle, time, math
sys.path.insert(0, '<ROOT>/dim')
import numpy as np
import scipy.linalg as sla

n = int(sys.argv[1]); ac = pickle.load(open(sys.argv[2], 'rb')); blocks, meta, Rinv = pickle.load(open(sys.argv[3], 'rb'))
cols = np.load(sys.argv[4]); outp = sys.argv[5]
t0 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
types = pickle.load(open('<ROOT>/dim/runs/exact_types2_k3_d6.pkl', 'rb'))
FTP = pickle.load(open('<ROOT>/dim/uni/ftpoly.pkl', 'rb'))
kept = list(ac['type_index'])
assert kept == list(meta)
F = {}
for ti in kept:
    t = types[ti]
    labs = FTP[t['cut']]['labels']
    F[ti] = sum(labs[li][0] for li in t['st'])
Fmax = max(F.values())
L, Lnum = {}, {}
E = 96
mx = 0.0
for ti, Ri, Dm in zip(kept, Rinv, ac['D']):
    C = np.linalg.cholesky((Dm + Dm.T) / 2)
    L[ti] = float(n) ** F[ti] * (Ri @ C)
    mx = max(mx, np.abs(L[ti]).max())
Eexp = max(0, E - int(math.floor(math.log2(mx))))
Lden = 2 ** Eexp
for ti in kept:
    Lnum[ti] = [[int(round(x * Lden)) for x in row] for row in L[ti]]
log('F range %d..%d; L max entry %.3e; Lden = 2^%d' % (min(F.values()), Fmax, mx, Eexp))
# relative Gram columns at n_ref from the W-basis columns
Gf, idx, Lf = cols['Gf'], cols['idx'], cols['Lf']
pos = {}
for j, (ti, a, b) in enumerate(idx):
    pos.setdefault(int(ti), {})[(int(a), int(b))] = j
relcols, relidx = [], []
for ti in kept:
    Lt = np.array(Lnum[ti], dtype=float) / Lden
    r = Lt.shape[0]
    P = pos[ti]
    ents = sorted(P)
    Gt = Gf[:, [P[e] for e in ents]]
    sc = float(n) ** (-2 * F[ti])
    for a in range(r):
        for b in range(a, r):
            Eab = np.zeros((r, r)); Eab[a, b] = 1; Eab[b, a] = 1
            M = sc * (Lt @ Eab @ Lt.T)
            coef = np.array([M[c, d] for (c, d) in ents])     # off-diagonal: column of E_cd + E_dc
            relcols.append(Gt @ coef)
            relidx.append((ti, a, b))
R = np.array(relcols).T
log('relative Gram columns %s' % (R.shape,))
cn = np.linalg.norm(Lf, axis=0); cn[cn == 0] = 1
Ln = Lf / cn
QL, RL, pL = sla.qr(Ln, mode='economic', pivoting=True)
dL = np.abs(np.diag(RL)); rL = int((dL > 1e-9 * dL[0]).sum())
selL = pL[:rL].tolist()
QLb = QL[:, :rL]
Rp = R - QLb @ (QLb.T @ R)
QG, RG, pG = sla.qr(Rp, mode='economic', pivoting=True)
dG = np.abs(np.diag(RG)); rG = int((dG > 1e-9 * dG[0]).sum())
selG = pG[:rG].tolist()
log('selected %d equality + %d relative Gram columns (pivot ratio %.2e .. %.2e)' % (rL, rG, dG[rG - 1] / dG[0], dG[rG] / dG[0] if rG < len(dG) else 0))
S = np.hstack([Ln[:, selL], R[:, selG]])
sv = np.linalg.svd(Rp[:, selG], compute_uv=False)
log('selected relative Gram block (equality span projected out): sigma max %.3e min %.3e' % (sv[0], sv[-1]))
lidx = cols['lidx']
sel_eq = [(int(lidx[j][0]), tuple(int(x) for x in lidx[j][1:])) for j in selL]
sel_gram = [relidx[j] for j in selG]
pickle.dump(dict(n_ref=n, kept=kept, F=F, Fmax=Fmax, Lnum=Lnum, Lden=Lden, sel_eq=sel_eq, sel_gram=sel_gram,
                 sigma_gram=(sv[0], sv[-1])), open(outp, 'wb'), protocol=4)
log('saved %s' % outp)
