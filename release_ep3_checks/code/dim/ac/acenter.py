"""Analytic centre of the optimal dual face at local dimension n (polynomial data, fixed face N):
    max sum_t log det D_t   s.t.   c = sum_t F_t^*(D_t) + E^T lam .
Computed through the self-concordant dual  psi(nu) = c^T nu - sum_t log det F_t(nu)  on {E nu = 0}, with the
gauge (left kernel: lineality Lin and the primal optimum y*) fixed by Lin^T nu = 0, tr^T nu = const.
Stationarity: D_t = F_t(nu)^{-1}.  Start: nu0 = y_ipm / mu_ipm from a polysdp2 node solution.
Usage: acenter.py n node.pkl out.pkl"""
import sys, pickle, time, os
sys.path.insert(0, '<ROOT>/dim')
sys.path.insert(0, '<ROOT>/dim/uni')
import numpy as np
import scipy.linalg as sla
from relax import Relaxation
from polysdp2 import PolyTE, build_reduced_blocks, sdp_data
from ipm import IPM

n = float(sys.argv[1]); node = pickle.load(open(sys.argv[2], 'rb')); outp = sys.argv[3]
nu_start = pickle.load(open(sys.argv[4], 'rb'))['nu_ac'] if len(sys.argv) > 4 else None
t0 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
R = Relaxation(3, 5, verbose=False)
types = pickle.load(open('<ROOT>/dim/runs/exact_types2_k3_d6.pkl', 'rb'))
Ns = node['N']
drop = {(t['kind'], t['f'], t['cut'], t['st'], t['ai'], t['irrep']) for t in types
        if t['kind'] == 'src' and t['f'] == '22' and t['cut'] == (0, 2) and t['st'] == (5, 5, 5) and t['ai'] == 2 and t['irrep'] == 'triv'}
cache = '<ROOT>/dim/ac/blocks_n%g.pkl' % n
if os.path.exists(cache):
    blocks, meta, Rinv = pickle.load(open(cache, 'rb'))
else:
    TE = PolyTE(R, types, n, scaled=False)
    blocks, meta, Rinv = build_reduced_blocks(TE, types, Ns, drop)
    pickle.dump((blocks, meta, Rinv), open(cache, 'wb'), protocol=4)
assert list(meta) == list(node['type_index'])
c, tr, E, Esv = sdp_data(R, n)
H0 = np.zeros((R.N, R.N))
for idx, F in blocks:
    A = F.reshape(F.shape[0], -1)
    H0[np.ix_(idx, idx)] += A @ A.T
Et0 = np.vstack([E, tr[None, :]])
U_, s_, Vt_ = np.linalg.svd(Et0, full_matrices=True)
Zt = Vt_[int((s_ > s_.max() * 1e-10).sum()):].T
wz, Vz = np.linalg.eigh(Zt.T @ H0 @ Zt)
Lin = Zt @ Vz[:, :106]
log('blocks %d, lineality eigs %.1e .. %.1e | next %.1e' % (len(blocks), wz[0] / wz.max(), wz[105] / wz.max(), wz[106] / wz.max()))
ipm = IPM(c, np.vstack([E, tr[None, :], Lin.T]), np.zeros(1), blocks, verbose=False)
Eg = np.vstack([E, tr[None, :], Lin.T])       # constraints kept on nu: E nu = 0, tr nu = const, Lin^T nu = 0
mu = sum(np.sum(S * D) for S, D in zip(node['S'], node['D'])) / sum(D.shape[0] for D in node['D'])
nu = node['y'] / mu
nu = nu - Lin @ (Lin.T @ nu)
# E nu should be ~0 already (E y = 0); project
nu = nu - E.T @ np.linalg.lstsq(E @ E.T, E @ nu, rcond=None)[0]


def psi_parts(nu):
    Ms = ipm.M(nu)
    val = c @ nu
    chols = []
    for Mt in Ms:
        L = np.linalg.cholesky((Mt + Mt.T) / 2)
        val -= 2 * np.log(np.diag(L)).sum()
        chols.append(L)
    return val, Ms, chols


def ls_start(Dlist):
    """nu with F_t(nu) ~ D_t^{-1} (least squares), gauge tr^T nu = 0, Lin^T nu = 0, E nu = 0 (no y* component)."""
    Dinv = [np.linalg.inv((Dm + Dm.T) / 2) for Dm in Dlist]
    b = ipm.Fstar(Dinv)
    al = np.trace(H0) / R.N / (np.sum(Eg * Eg) / Eg.shape[0])
    Hc0 = sla.cho_factor(H0 + al * (Eg.T @ Eg), lower=True)
    HiE0 = sla.cho_solve(Hc0, Eg.T)
    Hb = sla.cho_solve(Hc0, b)
    w0 = np.linalg.solve(Eg @ HiE0, Eg @ Hb)
    return Hb - HiE0 @ w0


if os.environ.get('AC_LS_START'):
    src = pickle.load(open(os.environ['AC_LS_START'], 'rb'))
    nu1 = ls_start(src['D'])
    try:
        psi_parts(nu1)
        nu = nu1
        nu_start = None
        log('least-squares start (gauge tr nu = 0) accepted; |nu| %.3e' % np.linalg.norm(nu))
    except np.linalg.LinAlgError:
        log('least-squares start not PD')
if nu_start is not None:
    nu1 = nu_start - Lin @ (Lin.T @ nu_start)
    nu1 = nu1 - E.T @ np.linalg.lstsq(E @ E.T, E @ nu1, rcond=None)[0]
    try:
        psi_parts(nu1)
        nu = nu1
        log('continuation start accepted')
    except np.linalg.LinAlgError:
        log('continuation start not PD; using IPM start')
val, Ms, chols = psi_parts(nu)
log('start: psi %.6e, mu_ipm %.3e' % (val, mu))
prev_dec = np.inf
hist_dec = []
for it in range(60):
    Sinv = [sla.cho_solve((L, True), np.eye(L.shape[0])) for L in chols]
    Sinv = [(A + A.T) / 2 for A in Sinv]
    g = c - ipm.Fstar(Sinv)
    Sc = [np.linalg.cholesky(A) for A in Sinv]
    H = ipm.schur(Sc, Sc)
    H = (H + H.T) / 2
    alpha = np.trace(H) / R.N / (np.sum(Eg * Eg) / Eg.shape[0])
    Ha = H + alpha * (Eg.T @ Eg)
    Hc = sla.cho_factor(Ha, lower=True)
    HiE = sla.cho_solve(Hc, Eg.T)
    Sm = Eg @ HiE
    Smf = sla.cho_factor((Sm + Sm.T) / 2, lower=True)

    def kkt_solve(r1, r2):
        # solve [H Eg^T; Eg 0][x; w] = [r1; r2] via Ha = H + alpha Eg^T Eg (exact for the KKT solution)
        b1 = r1 + alpha * (Eg.T @ r2)
        Hb = sla.cho_solve(Hc, b1)
        w_ = sla.cho_solve(Smf, Eg @ Hb - r2)
        return Hb - HiE @ w_, w_

    dnu, w = kkt_solve(-g, np.zeros(Eg.shape[0]))
    for _ in range(3):                       # iterative refinement with the exact H
        r1 = -g - H @ dnu - Eg.T @ w
        r2 = -(Eg @ dnu)
        ddn, dw = kkt_solve(r1, r2)
        dnu = dnu + ddn; w = w + dw
    dec = np.sqrt(max(dnu @ (H @ dnu), 0))
    step = 1.0 if dec < 0.25 else 1.0 / (1.0 + dec)
    # damped phase: backtrack on psi; quadratic phase (dec < 0.25): full Newton steps (psi differences are
    # below float resolution there), only feasibility is checked
    while True:
        try:
            nval, nMs, nch = psi_parts(nu + step * dnu)
            if dec < 0.25 or nval <= val + 1e-12 * abs(val) or step < 1e-6:
                break
        except np.linalg.LinAlgError:
            pass
        step *= 0.5
    nu = nu + step * dnu
    val, Ms, chols = nval, nMs, nch
    # dual residual with D = F(nu)^{-1}, lam from least squares on E rows
    Dm = [sla.cho_solve((L, True), np.eye(L.shape[0])) for L in chols]
    r = c - ipm.Fstar(Dm)
    lam = np.linalg.lstsq(E.T, r, rcond=None)[0]
    res = np.abs(r - E.T @ lam).max() / (1 + np.abs(c).max())
    log('it %2d  decrement %.3e  step %.3f  psi %.10e  dual residual %.2e' % (it, dec, step, val, res))
    hist_dec.append(dec)
    if dec < 1e-11 or (dec < 3e-5 and len(hist_dec) > 4 and dec > 0.7 * min(hist_dec[-4:-1])):
        break
    prev_dec = dec
Dm = [(A + A.T) / 2 for A in Dm]
ev = [np.linalg.eigvalsh(A) for A in Dm]
per = sorted(w_.min() / w_.max() for w_ in ev)
log('analytic centre: per-block margin worst %.3e  p1 %.3e  median %.3e' % (per[0], per[len(per) // 100], per[len(per) // 2]))
out = dict(node)
out.update(D=Dm, nu_ac=nu, lam_ac=lam, Z_exact_basis=[Ri @ D @ Ri.T for Ri, D in zip(Rinv, Dm)], acenter=True, n=n)
pickle.dump(out, open(outp, 'wb'), protocol=4)
log('saved %s' % outp)
