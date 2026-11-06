"""End-to-end sanity check of the word-level conventions on PHYSICAL points at finite n (audit item 6).

Physical rank-2 points with product structure C = C1 (x) u2 v2^* (x) u3 v3^* (x) u4 v4^*, lifted isometrically
(A^* A = I/2, ||b|| = 1), twirled over U(n)^4 x U(2).  Their twirled word coefficients factorise
x = x^(anc,site1) (x) x^(2) (x) x^(3) (x) x^(4), computed exactly from replica overlaps and the Gram pseudo-inverses.
Checks at n in {4, 50, 1000, 1.25e9}:
  (1) 16 n^16 c(x) = q_4(t, C) ||a||^4      (objective functional, family 31)
  (2) 16 n^16 tau(x) = ||a||^6 ||b||^2      (trace functional)
  (3) max_w |x_w| <= LK(n) tau(x)           (trace-slack coefficient bound)
  (4) every equality functional vanishes on x
  (5) every src-key term <Q, M_key(x)> >= 0 and the total block term >= 0 (validity of the raw block data at n)
"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))   # python -I does not add the script dir
import common
import os, sys, pickle, itertools
import numpy as np
from relax import P4, I4, TAU, P0, SWAP03, FAMILIES
from local import compose, inverse, ncycles
from exact import ExactLocal
FTP = common.load_ftp()
from exact_blocks import WM2

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
t = 79 / 160; nu = 1e-4
NW = 24
nc = np.array([ncycles(q) for q in P4]); ncs = np.array([ncycles(compose(SWAP03, q)) for q in P4])
REPL = {'31': 'aaab', '22': 'aabb', '13': 'bbba'}   # a at slot 3 for X13 (Stiefel slot 3; marginal order (3,0,2))


def perm_apply_axes(T, sig, axes):
    """permute the replica axes: output axis axes[i] takes input axis axes[sig^{-1}(i)] (P_sig |x1..x4> = |x_{sig^-1(1)}..>)"""
    inv = inverse(sig)
    perm = list(range(T.ndim))
    for i in range(4):
        perm[axes[i]] = axes[inv[i]]
    return np.transpose(T, perm)


def gvec_site(vecs):
    """g_sig = <phi|P_sig|phi> for phi = vecs[0] (x) .. (x) vecs[3] (real vectors)"""
    Phi = np.einsum('i,j,k,l->ijkl', *vecs)
    return np.array([np.sum(Phi * perm_apply_axes(Phi, sig, [0, 1, 2, 3])) for sig in P4])


def gmat_joint(vecs):
    """vecs[i] has shape (2, m) (ancilla x site-1); returns g[sig_a, sig_1]"""
    Phi = np.einsum('ab,cd,ef,gh->abcdefgh', *vecs)          # axes: (a0,s0,a1,s1,a2,s2,a3,s3)
    g = np.zeros((24, 24))
    for ia, sa in enumerate(P4):
        Ta = perm_apply_axes(Phi, sa, [0, 2, 4, 6])
        for i1, s1 in enumerate(P4):
            g[ia, i1] = np.sum(Phi * perm_apply_axes(Ta, s1, [1, 3, 5, 7]))
    return g


def Ghat(n):
    return np.array([[float(n) ** (ncycles(compose(inverse(v), w)) - 4) for w in P4] for v in P4])


Ga = np.array([[2.0 ** ncycles(compose(inverse(v), w)) for w in P4] for v in P4])
Gap = np.linalg.pinv(Ga)

# point: site 1 + ancilla carry the rank-2 structure; sites 2..4 rank one
m = 3
U = np.linalg.qr(rng.standard_normal((m, 2)))[0] / np.sqrt(2)           # columns u^(0) perp u^(1), norm 1/sqrt2 -> A^*A = I/2
V = rng.standard_normal((m, 2)); V /= np.linalg.norm(V)
us = [None] + [x / np.linalg.norm(x) for x in rng.standard_normal((3, 2))]
vs = [None] + [x / np.linalg.norm(x) for x in rng.standard_normal((3, 2))]
a1 = U.T.copy(); b1 = V.T.copy()                                     # shape (2, m): row r = column r
C1 = U @ V.T
na2 = np.sum(a1 ** 2); nb2 = np.sum(b1 ** 2)                         # ||a||^2 = 1 (A^*A = I/2 trace), ||b||^2 = 1
q1 = lambda X: np.sum(X ** 2) - t * np.trace(X) ** 2
q4 = q1(C1) * np.prod([q1(np.outer(us[l], vs[l])) for l in (1, 2, 3)])
print('point: ||a||^2 = %.6f, ||b||^2 = %.6f, q_4(t,C) = %.6e' % (na2, nb2, q4))

PB = pickle.load(open(common.W('prep_blocks.pkl'), 'rb')); blocks = PB['blocks']
PE = pickle.load(open(common.W('prep_eq.pkl'), 'rb'))
PERM = dict(id=np.arange(NW), PA=np.array([I4[compose(compose(TAU, q), TAU)] for q in P4]),
            PB=np.array([I4[compose(q, P0)] for q in P4]), **{'G2' + f: np.array([I4[WM2[f](q)] for q in P4]) for f in FAMILIES})
ANC = {}
keys = {}
for b in blocks:
    M = b['M']; nraw = b['n']; k0 = (b['cut'], b['st'], b['ai'])
    if b['kind'] == 'src':
        parts = [((b['f'], 'id'), M, M, 1.0)]
    else:
        pn = {'31': 'PA', '13': 'PA', '22': 'PB'} if b['kind'] == 'gram' else {f: 'G2' + f for f in FAMILIES}
        M1, M2 = M[:nraw], M[nraw:]
        parts = [(('31', pn['31']), M1, M1, 1.0), (('13', pn['13']), M2, M2, 1.0), (('22', pn['22']), M1, M2, 2.0)]
    for kk, X, Y, w in parts:
        key = k0 + kk
        keys[key] = keys.get(key, 0) + w * (X @ Y.T)
    if b['cut'] not in ANC:
        la = ExactLocal(2, 4, b['cut']); ANC[b['cut']] = (np.array(la.FT, dtype=float), la.off)

for n in (4, 50, 1000, 1.25e9):
    s = 1.0 / n
    Gh = Ghat(n); Ghi = np.linalg.inv(Gh)
    LK = 16 * np.abs(Gap).sum(axis=1).max() * np.abs(Ghi).sum(axis=1).max() ** 4
    X = {}
    for f in FAMILIES:
        pat = REPL[f]
        g1 = gmat_joint([a1 if ch == 'a' else b1 for ch in pat])
        xs = [Gap @ g1 @ Ghi.T]                                       # joint (anc, site1): scaled coefficients xhat
        for l in (1, 2, 3):
            xs.append(Ghi @ gvec_site([us[l] if ch == 'a' else vs[l] for ch in pat]))
        X[f] = xs
    # (1),(2) objective and trace (family 31)
    zf = lambda w: sum(((nc == 4 - j) - t * (ncs == 4 - j)) * s ** j for j in range(4))
    yf = sum((nc == 4 - j) * s ** j for j in range(4))
    za = 2.0 ** ncs; zat = 2.0 ** nc
    xa1, x2, x3, x4 = X['31']
    cval = (za @ xa1 @ zf(0)) * (x2 @ zf(0)) * (x3 @ zf(0)) * (x4 @ zf(0))      # = 16 n^16 c(x) / n^16 ... scaled
    tval = (zat @ xa1 @ yf) * (x2 @ yf) * (x3 @ yf) * (x4 @ yf)
    TrX = na2 ** 3 * nb2
    print('n=%-8.3g (1) 16n^16 c(x) = %.12e vs q4*||a||^4 = %.12e  rel.err %.1e' % (n, cval, q4 * na2 ** 2, abs(cval - q4 * na2 ** 2) / abs(q4)))
    print('           (2) 16n^16 tau(x) = %.12e vs ||a||^6||b||^2 = %.12e' % (tval, TrX))
    # (3) coefficient bound (scale-free): max |xhat_w| <= LK * TrX / 16 ... in the verifier's normalisation |x_w| <= LK tau(x)
    for f in FAMILIES:
        xa1f, y2, y3, y4 = X[f]
        mx = np.abs(xa1f).max() * np.abs(y2).max() * np.abs(y3).max() * np.abs(y4).max()
        assert mx <= LK * TrX / 16 * (1 + 1e-9), ('coef bound fails', f, mx, LK * TrX / 16)
    print('           (3) max|x_w| <= LK(n) tau(x) for all families: OK (LK(n) = %.4f)' % LK)
    # (4) equality functionals on x
    worst = 0.0
    for grp in PE['groups']:
        vals = []
        for f, so, Ea, sg, o, nrow in grp:
            a_eq, b_eq = PE['site_eq'][so]
            site = a_eq + s * b_eq                                    # scaled partial trace, exactly linear in s
            xa1f, y2, y3, y4 = X[f]
            # E_f(x)[rows] = sum_w x_w (x)_l site[:, w_l] (x) Ea[:, w_a]; x factorises (anc, site1) (x) site2..4
            J = np.einsum('ab,ia,jb->ji', xa1f, Ea, site)            # (site1 rows 6, anc rows nE)
            v2, v3, v4 = site @ y2, site @ y3, site @ y4
            vals.append(sg * np.einsum('ji,k,l,m->jklmi', J, v2, v3, v4))
        tot = sum(vals)
        worst = max(worst, np.abs(tot).max())
        print('             group', [(g[0], g[1]) for g in grp], 'max|E| = %.3e' % np.abs(tot).max())
    print('           (4) max |E(x)| over all equality rows = %.3e' % worst)
    # (5) block terms
    neg_src, tot_blk, n_src = 0, 0.0, 0
    for key, Q in keys.items():
        cut, st, ai, f, pname = key
        coef, off, labels = FTP[cut]['coef'], FTP[cut]['off'], FTP[cut]['labels']
        Ps = []
        for li in st:
            ff = labels[li][0]
            rows = slice(off[li], off[li + 1])
            Ps.append(sum(np.array(coef[2 * ff - j, rows], dtype=float) * s ** j for j in range(2 * ff + 1)))
        FTa, offa = ANC[cut]
        PA_ = FTa[offa[ai]:offa[ai + 1]]
        pm = PERM[pname]
        xa1f, y2, y3, y4 = X[f]
        # raw block = sum_w x_w (x)_l P_l[:, pi(w_l)] (x) P_anc[:, pi(w_a)]  (factorised)
        B1 = np.einsum('ab,ia,jb->ij', xa1f, PA_[:, pm], Ps[0][:, pm])          # (anc rows, site1 rows) joint
        b2, b3, b4 = Ps[1][:, pm] @ y2, Ps[2][:, pm] @ y3, Ps[3][:, pm] @ y4
        dims = [int(round(np.sqrt(len(v)))) for v in (Ps[0][:, 0], b2, b3, b4, PA_[:, 0])]
        # assemble full raw block entries in the verifier's (site0..site3, anc) ordering
        T = np.einsum('ij,k,l,m->jklmi', B1, b2, b3, b4)                       # rows (site0, s1, s2, s3, anc) pair-indices
        Tm = T.reshape([d * d for d in dims])
        # pairs (a_l, b_l) -> matrix over (a_0..a_4),(b_0..b_4)
        Tm = Tm.reshape(sum([[d, d] for d in dims], []))
        order = [2 * i for i in range(5)] + [2 * i + 1 for i in range(5)]
        Mb = Tm.transpose(order).reshape(Q.shape)
        val = float(np.sum(Q * Mb))
        tot_blk += val
        if pname == 'id':
            n_src += 1
            if val < -1e-12 * max(1.0, np.abs(Q).sum() * np.abs(Mb).max()):
                neg_src += 1
    print('           (5) src keys with <Q,M(x)> < 0: %d of %d; total block term %.6e (must be >= 0)' % (neg_src, n_src, tot_blk))
