"""Exact residues mod p of the word-level residual polynomial coefficients R0, R1 (orbit sums) for the t = 79/160,
s = 0 certificate, as an independent re-implementation (audit).

The certificate used here is the verifier's certificate after harmless fixed-point rounding, which keeps it valid:
  * multiplier factors M (any real M gives an exactly PSD Q = M M^T) rounded to 2^-60;
  * equality multipliers lam (any lam is admissible) rounded to 2^-60;
  * the float local matrices S3FT, A3FT, LA4FT of the equality rows (any common left factor of a vanishing contrast is
    admissible, used consistently in paired terms) rounded to 2^-40;
  * nu = gamma' = 1/10000 exactly.
All data are then rationals with denominators dividing Dden = 2^261 * 5^4. Arithmetic: residues in [0, p), p < 2^20, held in
float64; every product/sum stays below 2^53, so float64 BLAS matmuls are exact.
Usage: exact_worker.py p out.pkl [nchunk chunk]   (nchunk/chunk split the multiplier keys; objective/trace/equality on chunk 0)
"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))   # python -I does not add the script dir
import common
import os, sys, pickle, time
import numpy as np
from fractions import Fraction
from relax import P4, I4, TAU, P0, SWAP03, FAMILIES
from local import compose, ncycles
from exact import ExactLocal
FTP = common.load_ftp()
from exact_blocks import WM2

t00 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t00, s), flush=True)
p = int(sys.argv[1]); outp = sys.argv[2] if os.path.isabs(sys.argv[2]) else common.W(sys.argv[2])
nchunk = int(sys.argv[3]) if len(sys.argv) > 3 else 1
chunk = int(sys.argv[4]) if len(sys.argv) > 4 else 0
FP = float(p)
assert p < 2 ** 20
NW = 24; SH5 = (NW,) * 5
F_M, F_L, F_T = 60, 60, 40
inv2 = pow(2, p - 2, p)
POW2 = np.array([pow(2, k, p) for k in range(1200)], dtype=float)


def md(x):
    r = np.fmod(x, FP)
    return np.where(r < 0, r + FP, r)


def res_int_float(y):
    """residue of integer-valued float array y (any magnitude)"""
    y = np.asarray(y, dtype=float)
    out = np.empty_like(y)
    small = np.abs(y) < 2.0 ** 52
    out[small] = md(y[small])
    if np.any(~small):
        m, e = np.frexp(y[~small])
        mi = np.ldexp(m, 53)                   # integer-valued, |mi| < 2^53
        sh = e - 53
        assert sh.min() >= 0 and sh.max() < 1200
        out[~small] = md(md(mi) * POW2[sh])
    return out


def fixed(x, F):
    """residue of the fixed-point numerator round(x * 2^F) (the value is numerator * 2^-F)"""
    return res_int_float(np.round(np.ldexp(np.asarray(x, dtype=float), F)))


def rres(fr):
    fr = Fraction(fr)
    return float(fr.numerator % p * pow(fr.denominator % p, p - 2, p) % p)


c2M = float(pow(inv2, 2 * F_M, p))     # Q = w * X Y^T * 2^-120
# ---------------- data ----------------
PB = pickle.load(open(common.W('prep_blocks.pkl'), 'rb'))
blocks = PB['blocks']; t_ = Fraction(PB['t']); assert t_ == Fraction(79, 160)
SITE = {}
for c, P in FTP.items():
    SITE[c] = (P['coef'], P['off'], P['labels'])
ANC = {}
for b in blocks:
    c = b['cut']
    if c not in ANC:
        la = ExactLocal(2, 4, c)
        ANC[c] = (np.array(la.FT, dtype=object), la.off)


def site_res(c, li):
    coef, off, labels = SITE[c]
    f = labels[li][0]
    rows = slice(off[li], off[li + 1])
    a = np.array([int(x) for x in coef[2 * f, rows].ravel()], dtype=float).reshape(coef[2 * f, rows].shape)
    if 2 * f >= 1:
        bb = np.array([int(x) for x in coef[2 * f - 1, rows].ravel()], dtype=float).reshape(a.shape)
    else:
        bb = np.zeros_like(a)
    return md(a), md(bb), bool(np.any(bb != 0))


PERM = dict(id=np.arange(NW), PA=np.array([I4[compose(compose(TAU, q), TAU)] for q in P4]),
            PB=np.array([I4[compose(q, P0)] for q in P4]), **{'G2' + f: np.array([I4[WM2[f](q)] for q in P4]) for f in FAMILIES})

# fold blocks into keys exactly as the certificate does (gram roles 31/13/22 with weights 1/1/2)
keys = {}
for b in blocks:
    M = b['M']; nraw = b['n']; k0 = (b['cut'], b['st'], b['ai'])
    if b['kind'] == 'src':
        parts = [((b['f'], 'id'), M, M, 1)]
    else:
        pn = {'31': 'PA', '13': 'PA', '22': 'PB'} if b['kind'] == 'gram' else {f: 'G2' + f for f in FAMILIES}
        M1, M2 = M[:nraw], M[nraw:]
        parts = [(('31', pn['31']), M1, M1, 1), (('13', pn['13']), M2, M2, 1), (('22', pn['22']), M1, M2, 2)]
    for kk, X, Y, w in parts:
        keys.setdefault(k0 + kk, []).append((X, Y, w))
klist = sorted(keys.keys(), key=lambda k: str(k))
mine = klist[chunk::nchunk]
log('p=%d: %d keys total, %d in chunk %d/%d' % (p, len(klist), len(mine), chunk, nchunk))


def contract(Q, mats):
    dims = [int(round(np.sqrt(Mx.shape[0]))) for Mx in mats]
    L_ = len(dims)
    T = Q.reshape(dims + dims)
    order = []
    for i in range(L_):
        order += [i, L_ + i]
    T = T.transpose(order).reshape([d * d for d in dims])
    for Mx in mats:
        T = md(np.tensordot(T, Mx, axes=([0], [0])))
    return T


acc = {f: [np.zeros(SH5), np.zeros(SH5)] for f in FAMILIES}
for ik, key in enumerate(mine):
    cut, st, ai, f, pname = key
    Q = None
    for X, Y, w in keys[key]:
        Xr = fixed(X, F_M); Yr = fixed(Y, F_M)
        q = md(md(Xr @ Yr.T) * float(w * c2M % p))
        Q = q if Q is None else md(Q + q)
    sd = [site_res(cut, li) for li in st]
    FTa, offa = ANC[cut]
    anc = md(np.array([int(x) for x in FTa[offa[ai]:offa[ai + 1]].ravel()], dtype=float).reshape(FTa[offa[ai]:offa[ai + 1]].shape))
    a = [x[0] for x in sd]; bb = [x[1] for x in sd]; hasb = [x[2] for x in sd]
    R0 = contract(Q, a + [anc])
    R1 = np.zeros(SH5)
    for l in range(4):
        if hasb[l]:
            R1 = md(R1 + contract(Q, [bb[l] if m == l else a[m] for m in range(4)] + [anc]))
    pm = PERM[pname]
    if pname != 'id':
        ix = np.ix_(pm, pm, pm, pm, pm)
        R0 = R0[ix]; R1 = R1[ix]
    acc[f][0] = md(acc[f][0] - R0)      # block terms enter rho with a minus sign
    acc[f][1] = md(acc[f][1] - R1)
    if ik % 200 == 0:
        log('key %d/%d' % (ik, len(mine)))
log('block terms done')

if chunk == 0:
    # objective (+, weight 1/16) and trace (-nu/16) on family 31: site factor sum_j z_j s^j
    nc = np.array([ncycles(q) for q in P4]); ncs = np.array([ncycles(compose(SWAP03, q)) for q in P4])
    tr = rres(t_)
    z0 = md((nc == 4) - tr * (ncs == 4)); z1 = md((nc == 3) - tr * (ncs == 3))
    y0 = (nc == 4).astype(float); y1 = (nc == 3).astype(float)
    za = md(np.array([2.0 ** x for x in ncs])); zat = md(np.array([2.0 ** x for x in nc]))

    def outer5(v0, v1, v2, v3, v4):
        T = md(np.multiply.outer(v0, v1))
        for v in (v2, v3, v4):
            T = md(np.multiply.outer(T, v))
        return T
    for (s0v, s1v, av, w) in ((z0, z1, za, rres(Fraction(1, 16))), (y0, y1, zat, rres(-Fraction(1, 10000) / 16))):
        T0 = md(outer5(s0v, s0v, s0v, s0v, av) * w)
        T1 = np.zeros(SH5)
        for l in range(4):
            T1 = md(T1 + outer5(*[s1v if m == l else s0v for m in range(4)], av))
        T1 = md(T1 * w)
        acc['31'][0] = md(acc['31'][0] + T0); acc['31'][1] = md(acc['31'][1] + T1)
    log('objective/trace done')
    # equality terms
    PE = pickle.load(open(common.W('prep_eq.pkl'), 'rb')); EM = pickle.load(open(common.W('prep_eqmats.pkl'), 'rb'))
    lam_r = fixed(PE['lam'], F_L)                                       # value = lam_r * 2^-60
    S3n = np.round(np.ldexp(EM['S3FT'], F_T)); A3n = np.round(np.ldexp(EM['A3FT'], F_T)); LA4n = np.round(np.ldexp(EM['LA4FT'], F_T))
    i2T = float(pow(inv2, F_T, p))
    for grp in PE['groups']:
        for f, so, Ea_float, sg, o, nrow in grp:
            slot, order = so
            if order is None:      # Stiefel contrast: LA4 (I - 1/2 embed dm2) = LA4n (2I - E D) 2^-(F_T+1)
                K = 2 * np.eye(24) - EM[('embed', slot)] @ EM[('dm2', slot, None)]
                Ea = md(md(res_int_float(LA4n) @ md(K)) * float(i2T * inv2 % p))
            else:                  # marginal: A3 dm2(slot, order) = A3n dm2 2^-F_T
                Ea = md(md(res_int_float(A3n) @ md(EM[('dm2', slot, order)])) * i2T)
            a_eq = md(md(res_int_float(S3n) @ md(EM[('dms', so, 0)])) * i2T)
            b_eq = md(md(res_int_float(S3n) @ md(EM[('dms', so, 1)])) * i2T)
            nE = Ea.shape[0]
            Lam = md(lam_r[o:o + nrow] * float(pow(inv2, F_L, p))).reshape((6,) * 4 + (nE,))

            def con(core, ms):
                T = core
                for Mx in ms:
                    T = md(np.tensordot(T, Mx, axes=([0], [0])))
                return T
            T0 = con(Lam, [a_eq] * 4 + [Ea])
            T1 = np.zeros(SH5)
            for l in range(4):
                T1 = md(T1 + con(Lam, [b_eq if m == l else a_eq for m in range(4)] + [Ea]))
            sgr = 1.0 if sg > 0 else FP - 1.0
            acc[f][0] = md(acc[f][0] - md(sgr * T0)); acc[f][1] = md(acc[f][1] - md(sgr * T1))
    log('equality terms done')

# orbit sums mod p
OR = np.load(common.W('orbits.npz'))
out = {'p': p, 'chunk': chunk, 'nchunk': nchunk, 'R0o': {}, 'R1o': {}}
for f in FAMILIES:
    oid = OR[f]
    for i, nm in ((0, 'R0o'), (1, 'R1o')):
        s = np.bincount(oid, weights=acc[f][i].ravel())
        out[nm][f] = md(s).astype(np.int64)
pickle.dump(out, open(outp, 'wb'), protocol=4)
log('saved %s' % outp)
