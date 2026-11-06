"""[release copy: only the module path and the FTP loader differ from word_rig_v2_orig.py]
Rigorous-in-floating-point trace-slack check of an s = 0 (d = infinity) k = 4 certificate, uniformly for all s = 1/d in [0, s0].

Certificate: PSD multipliers Q_t = M_t M_t^T on each raw typed space (M_t = C_t chol(D_t + mu I), float; Q_t is exactly PSD as a
real matrix, and any PSD multiplier on the raw space is valid because the raw block is a compression of the partially transposed
moment operator), equality multipliers lam on the literal equality rows, trace multiplier nu = gamma.
For each word w in S4^5 and family f the residual is a polynomial in s:
    rho_f(w; s) = c_f(w; s) - gamma tau_f(w; s) - sum_t <Q_t^(f), (x)_l P_l(pi(w_l); s)> - lam . E_f(w; s),
every term a multilinear contraction of a core with per-site polynomial factors P_l(s) = a_l + s b_l + s^2 r_l(s) (site data
FT_poly n^{-2f} = sum_j coef[2f-j] s^j; objective/trace site factors n^{nc-4}; scaled partial traces), the ancilla fixed.
Computed per word: R0 = rho(.;0), R1 = d rho/ds(.;0), rounding bounds e0, e1 (absolute-value shadow contractions times
gamma_m), and B2 with |rho(w;s) - R0 - s R1| <= s^2 B2(w) for 0 <= s <= 1 (expand prod_l (a_l + s b_l + s^2 r_l), |r_l| <= W_l).
Orbit sums over H_f = (site perms) x (left/right G_f) x (inversion); then for 0 <= s <= s0:
    sum_o |R(o; s)| <= S0 + s S1 + s^2 S2,   S0 = sum_o (|R0(o)| + e0(o)), S1 = sum_o (|R1(o)| + e1(o)), S2 = sum_w B2(w),
and the trace-slack lemma at d = 1/s gives q_4(t, C) >= (gamma - LK(d) (S0 + s S1 + s^2 S2)) ||C||^2 (normalised).
Usage: word_rig.py types.pkl ns.pkl ipm_result.pkl margin_meta.pkl s0 nproc out.pkl"""
import os, sys, pickle, time, itertools
_PKG = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))   # release package root
sys.path.insert(0, os.path.join(_PKG, 'zm'))
import numpy as np
from fractions import Fraction
from relax import Relaxation, P4, I4, I3, TAU, P0, SWAP03, FAMILY_GROUP, FAMILIES
from local import compose, inverse, ncycles
from exact import ExactLocal
FTP = pickle.load(open(os.path.join(_PKG, 'data', 'ftpoly.pkl'), 'rb'))   # = face_subset.FTP (same file)
from exact_blocks import WM2

t00 = time.time()
log = lambda s_: print('[%.0fs] %s' % (time.time() - t00, s_), flush=True)
types = pickle.load(open(sys.argv[1], 'rb'))
Ns = pickle.load(open(sys.argv[2], 'rb'))['Ns']
res = pickle.load(open(sys.argv[3], 'rb'))
mmeta = pickle.load(open(sys.argv[4], 'rb'))
s0 = float(sys.argv[5]); nproc = int(sys.argv[6]); outp = sys.argv[7]
base = pickle.load(open(mmeta['margin']['base_meta'], 'rb'))
gamma = float(mmeta['margin']['gamma']); t_ = float(Fraction(base['t']))
mu = float(res['dobj'])
assert mu > 0, 'needs a strictly feasible margin certificate (dobj > 0)'
NW = 24; SH5 = (NW,) * 5
U = 2.0 ** -53
gam = lambda m: m * U / (1 - m * U)

# ---------------- per-site polynomial data (exact rationals -> float, |rel err| <= u) ----------------
SITE = {}          # cut -> (coef array (5, D, 24) float, off, labels)
for c, P in FTP.items():
    SITE[c] = (np.array(P['coef'], dtype=float), P['off'], P['labels'])
ANC = {}
for t in types:
    c = t['cut']
    if c not in ANC:
        la = ExactLocal(2, 4, c)
        ANC[c] = (np.array(la.FT, dtype=float), la.off)


def site_poly(c, li):
    """a, b, W (|r(s)| <= W for 0 <= s <= 1): rows of label li at cut c, scaled limit coefficients."""
    coef, off, labels = SITE[c]
    f = labels[li][0]
    rows = slice(off[li], off[li + 1])
    cs = [coef[2 * f - j, rows] for j in range(2 * f + 1)]          # s^j coefficient = coef[2f - j]
    a = cs[0]
    b = cs[1] if len(cs) > 1 else np.zeros_like(a)
    W = sum(np.abs(x) for x in cs[2:]) if len(cs) > 2 else np.zeros_like(a)
    return a, b, W


PERM = dict(id=np.arange(NW), PA=np.array([I4[compose(compose(TAU, p), TAU)] for p in P4]),
            PB=np.array([I4[compose(p, P0)] for p in P4]), **{'G2' + f: np.array([I4[WM2[f](p)] for p in P4]) for f in FAMILIES})

# ---------------- multipliers M_t (Q_t = M_t M_t^T), folded per key ----------------
keys = {}
for D, b in zip(res['D'], res['blocks']):
    ti = b['type_index']; t = types[ti]
    Vb = np.array(t['Vb'], dtype=float)
    if t['kind'] == 'gram':
        Vb = np.block([[Vb, np.zeros_like(Vb)], [np.zeros_like(Vb), Vb]])
    elif t['kind'] == 'gram2':
        V2 = np.array(t['Vb2'], dtype=float); m = Vb.shape[0]
        Vb = np.block([[Vb, np.zeros((m, V2.shape[1]))], [np.zeros((m, Vb.shape[1])), V2]])
    C = (Vb @ Ns[ti]) @ b['Rinv']
    if b.get('Nlk') is not None:
        C = C @ b['Nlk']
    if b.get('Tanc') is not None:
        C = C @ b['Tanc']
    Ds = (D + D.T) / 2 + mu * np.eye(D.shape[0])
    L = np.linalg.cholesky(Ds)
    M = C @ L
    nraw = t['n']
    k0 = (t['cut'], tuple(t['st']), t['ai'])
    if t['kind'] == 'src':
        parts = [((t['f'], 'id'), M, M, 1.0)]
    else:
        pn = {'31': 'PA', '13': 'PA', '22': 'PB'} if t['kind'] == 'gram' else {f: 'G2' + f for f in FAMILIES}
        M1, M2 = M[:nraw], M[nraw:]
        parts = [(('31', pn['31']), M1, M1, 1.0), (('13', pn['13']), M2, M2, 1.0), (('22', pn['22']), M1, M2, 2.0)]
    for kk, X, Y, w in parts:
        key = k0 + kk
        Q = w * (X @ Y.T)
        Qb = w * (np.abs(X) @ np.abs(Y).T)            # dominates |Q| and bounds the rounding of X Y^T (factor gamma_r)
        r = X.shape[1]
        if key in keys:
            q_, qb_, rmax = keys[key]
            keys[key] = (q_ + Q, qb_ + Qb, max(rmax, r))
        else:
            keys[key] = (Q, Qb, r)
log('%d multiplier blocks folded into %d keys (mu = %.4e)' % (len(res['D']), len(keys), mu))
NKEYS = len(keys)


def contract(Q, mats):
    dims = [int(round(np.sqrt(M.shape[0]))) for M in mats]
    L_ = len(dims)
    T = Q.reshape(dims + dims)
    order = []
    for i in range(L_):
        order += [i, L_ + i]
    T = T.transpose(order).reshape([d * d for d in dims])
    for M in mats:
        T = np.tensordot(T, M, axes=([0], [0]))
    return T


def key_terms(item):
    """R0, R1, shadow A0, A1, B2 (24^5 each) for one key, with the word map applied."""
    key, (Q, Qb, rmax) = item
    cut, st, ai, f, pname = key
    a, b, W = zip(*[site_poly(cut, li) for li in st])
    FTa, offa = ANC[cut]
    anc = FTa[offa[ai]:offa[ai + 1]]
    R0 = contract(Q, list(a) + [anc])
    R1 = sum(contract(Q, [b[l] if m == l else a[m] for m in range(4)] + [anc]) for l in range(4) if np.any(b[l]))
    if isinstance(R1, int):
        R1 = np.zeros(SH5)
    aa = [np.abs(x) for x in a]; bb = [np.abs(x) for x in b]; ab = np.abs(anc)
    A0 = contract(Qb, aa + [ab])
    A1 = sum(contract(Qb, [bb[l] if m == l else aa[m] for m in range(4)] + [ab]) for l in range(4) if np.any(b[l]))
    if isinstance(A1, int):
        A1 = np.zeros(SH5)
    Bfull = contract(Qb, [aa[m] + bb[m] + W[m] for m in range(4)] + [ab])
    nraw = Q.shape[0]
    g_ = gam(nraw * nraw + rmax + 64) + gam(NKEYS + nproc + 8)   # contraction + forming/summing X Y^T + input rounding + key accumulation
    B2 = Bfull - A0 - A1 + 3 * g_ * Bfull           # terms of s-degree >= 2, plus a guard for the rounding of all three
    pm = PERM[pname]
    out = []
    for T in (R0, R1, g_ * A0, g_ * A1, np.maximum(B2, 0)):
        out.append(T[np.ix_(pm, pm, pm, pm, pm)] if pname != 'id' else T)
    return f, out


def worker(chunk):
    acc = {f: [np.zeros(SH5) for _ in range(5)] for f in FAMILIES}
    for item in chunk:
        f, out = key_terms(item)
        for i in range(5):
            acc[f][i] += out[i]
    return acc


items = sorted(keys.items(), key=lambda kv: -kv[1][0].shape[0])
chunks = [items[i::nproc] for i in range(nproc)]
import multiprocessing as mp
with mp.get_context('fork').Pool(nproc) as pool:
    parts_ = pool.map(worker, chunks)
blk = {f: [sum(p[f][i] for p in parts_) for i in range(5)] for f in FAMILIES}
log('block terms done')
# block terms enter rho with a minus sign: R0 -= ., R1 -= ., bounds add
R0 = {f: -blk[f][0] for f in FAMILIES}; R1 = {f: -blk[f][1] for f in FAMILIES}
E0 = {f: blk[f][2] * (1 + gam(8)) for f in FAMILIES}       # per-key bounds already include the key accumulation
E1 = {f: blk[f][3] * (1 + gam(8)) for f in FAMILIES}
B2 = {f: blk[f][4] * (1 + gam(nproc + len(keys))) for f in FAMILIES}

# ---------------- objective and trace (family 31): site factor sum_j z_j s^j, z_j = [nc = 4-j] - t [nc(SW p) = 4-j] ----------------
nc = np.array([ncycles(p) for p in P4]); ncs = np.array([ncycles(compose(SWAP03, p)) for p in P4])
zs = [(nc == 4 - j).astype(float) - t_ * (ncs == 4 - j) for j in range(4)]
ztr = [(nc == 4 - j).astype(float) for j in range(4)]
za = np.array([2.0 ** x for x in ncs]); zatr = np.array([2.0 ** x for x in nc])


def outer_terms(z, zaux, w):
    a, b = z[0], z[1]
    Wv = sum(np.abs(x) for x in z[2:])
    o5 = lambda v0, v1, v2, v3: np.einsum('a,b,c,d,e->abcde', v0, v1, v2, v3, zaux)
    T0 = w * o5(a, a, a, a)
    T1 = w * sum(o5(*[b if m == l else a for m in range(4)]) for l in range(4))
    aa, bb = np.abs(a), np.abs(b)
    S0 = abs(w) * np.einsum('a,b,c,d,e->abcde', aa, aa, aa, aa, np.abs(zaux))
    S1 = abs(w) * sum(np.einsum('a,b,c,d,e->abcde', *([bb if m == l else aa for m in range(4)] + [np.abs(zaux)])) for l in range(4))
    Bt = abs(w) * np.einsum('a,b,c,d,e->abcde', *([aa + bb + Wv] * 4 + [np.abs(zaux)])) - S0 - S1
    return T0, T1, gam(64) * S0, gam(64) * S1, np.maximum(Bt, 0)


for z, zx, w in ((zs, za, 1.0 / 16), (ztr, zatr, -gamma / 16)):
    T0, T1, e0, e1, b2 = outer_terms(z, zx, w)
    R0['31'] += T0; R1['31'] += T1; E0['31'] += e0 + gam(8) * (np.abs(T0) + np.abs(R0['31'])); E1['31'] += e1 + gam(8) * (np.abs(T1) + np.abs(R1['31'])); B2['31'] += b2 + gam(64) * (np.abs(b2) + 1e-300)
log('objective/trace terms done')

# ---------------- equality terms: lam from res['EtT_nu'] (y-level) fitted on the raw rows at s = 0 ----------------
R = Relaxation(4, 5, verbose=False)
orig_dm = R.delete_matrix


def dm_s(order_slot, j):
    """s^j coefficient (j = 0, 1) of the scaled partial trace n^{-1} Tr_slot: [p fixes slot] (j = 0), [p moves slot] (j = 1)."""
    slot, order = order_slot
    if order is None:
        order = tuple(i for i in range(4) if i != slot)
    M = np.zeros((6, 24))
    for a_, p in enumerate(P4):
        if (p[slot] == slot) == (j == 0):
            out = tuple(order.index(p[slot] if p[i] == slot else p[i]) for i in order)
            M[I3[out], a_] += 1
    return M


def dm0(nn, slot, order=None):
    if np.isfinite(nn):
        return orig_dm(nn, slot, order)
    return dm_s((slot, order), 0)


R.delete_matrix = dm0
R.d = float('inf')
Eraw = R.equality_rows()
ey = res['EtT_nu'] - mu * mmeta['tr']['31']
Gm = Eraw.T @ Eraw
wE, VE = np.linalg.eigh(Gm)
kp = wE > 1e-10 * wE[-1]
lam = Eraw @ (VE[:, kp] @ ((VE[:, kp].T @ ey) / wE[kp]))
log('equality multipliers: rank %d, |Eraw^T lam - e_y| %.2e' % (kp.sum(), np.abs(Eraw.T @ lam - ey).max()))
s3, a3, la4 = R.loc3['s'], R.loc3['a'], R.loc['a', ()]
groups, off = [], 0
for f, slot in (('31', 0), ('22', 0), ('13', 3)):
    Ea = la4.FT @ (np.eye(24) - 0.5 * R.embed_matrix(slot) @ orig_dm(2, slot))
    nrow = 6 ** 4 * Ea.shape[0]
    groups.append([(f, (slot, None), Ea, 1.0, off, nrow)]); off += nrow
for (f1, s1, o1), (f2, s2, o2) in [(('31', 2, (0, 1, 3)), ('22', 2, (0, 1, 3))), (('22', 1, (0, 2, 3)), ('13', 1, (3, 0, 2)))]:
    E1a = a3.FT @ orig_dm(2, s1, o1); E2a = a3.FT @ orig_dm(2, s2, o2)
    nrow = 6 ** 4 * E1a.shape[0]
    groups.append([(f1, (s1, o1), E1a, 1.0, off, nrow), (f2, (s2, o2), E2a, -1.0, off, nrow)]); off += nrow
assert off == Eraw.shape[0]
for grp in groups:
    for f, so, Ea, sg, o, nrow in grp:
        Lam = lam[o:o + nrow].reshape((6,) * 4 + (Ea.shape[0],))
        a = s3.FT @ dm_s(so, 0); b = s3.FT @ dm_s(so, 1)
        mats0 = [a] * 4 + [Ea]

        def con(core, ms):
            T = core
            for M in ms:
                T = np.tensordot(T, M, axes=([0], [0]))
            return T
        T0 = con(Lam, mats0)
        T1 = sum(con(Lam, [b if m == l else a for m in range(4)] + [Ea]) for l in range(4))
        aL = np.abs(Lam); aa, bb, ae = np.abs(a), np.abs(b), np.abs(Ea)
        S0 = con(aL, [aa] * 4 + [ae]); S1 = sum(con(aL, [bb if m == l else aa for m in range(4)] + [ae]) for l in range(4))
        Bt = con(aL, [aa + bb] * 4 + [ae]) - S0 - S1
        g_ = gam(6 ** 4 * 14 + 64)
        R0[f] -= sg * T0; R1[f] -= sg * T1; E0[f] += (g_ + gam(16)) * (S0 + np.abs(R0[f])); E1[f] += (g_ + gam(16)) * (S1 + np.abs(R1[f])); B2[f] += np.maximum(Bt + 3 * g_ * (Bt + S0 + S1), 0)
log('equality terms done')

# ---------------- orbit sums and the uniform bound ----------------
lmul = lambda g: np.array([I4[compose(g, p)] for p in P4])
rmul = lambda g: np.array([I4[compose(p, g)] for p in P4])
invp = np.array([I4[inverse(p)] for p in P4])
Wd = np.indices(SH5).reshape(5, -1)
enc = lambda ws: (((ws[0] * NW + ws[1]) * NW + ws[2]) * NW + ws[3]) * NW + ws[4]


def orbit_labels(gens):
    lab = np.arange(NW ** 5)
    while True:
        old = lab
        for g in gens:
            lab = np.minimum(lab, lab[g])
        lab = lab[lab]
        if np.array_equal(lab, old):
            return lab


S0 = S1 = S2 = 0.0
rep = {}
for f in FAMILIES:
    gens = []
    for i, j in ((0, 1), (1, 2), (2, 3)):
        ws = list(Wd); ws[i], ws[j] = Wd[j], Wd[i]; gens.append(enc(ws))
    for g in [g for g in FAMILY_GROUP[f] if sum(g[i] != i for i in range(4)) == 2]:
        for m in (lmul(g), rmul(g)):
            gens.append(enc([m[Wd[i]] for i in range(5)]))
    gens.append(enc([invp[Wd[i]] for i in range(5)]))
    _, oid = np.unique(orbit_labels(gens), return_inverse=True)
    r0 = np.bincount(oid, weights=R0[f].ravel()); r1 = np.bincount(oid, weights=R1[f].ravel())
    ab0 = np.bincount(oid, weights=np.abs(R0[f]).ravel()); ab1 = np.bincount(oid, weights=np.abs(R1[f]).ravel())
    e0 = np.bincount(oid, weights=E0[f].ravel()); e1 = np.bincount(oid, weights=E1[f].ravel())
    sz = np.bincount(oid)
    e0 += gam(sz.max() + 2) * ab0; e1 += gam(sz.max() + 2) * ab1        # orbit summation rounding
    f0 = float(np.sum(np.abs(r0) + e0) * (1 + gam(len(r0)))); f1 = float(np.sum(np.abs(r1) + e1) * (1 + gam(len(r1))))
    f2 = float(B2[f].sum() * (1 + gam(NW ** 5)))
    rep[f] = dict(norb=len(r0), S0=f0, S1=f1, S2=f2, maxR0=float(np.abs(r0).max()), sumE0=float(e0.sum()), sumE1=float(e1.sum()))
    S0 += f0; S1 += f1; S2 += f2
    log('family %s: %d orbits; S0 %.3e (rounding %.1e), S1 %.3e (rounding %.1e), S2 %.3e' % (f, len(r0), f0, e0.sum(), f1, e1.sum(), f2))
Ga = np.array([[2.0 ** ncycles(compose(inverse(v), w)) for w in P4] for v in P4])
nGa = np.abs(np.linalg.pinv(Ga)).sum(axis=1).max()
d0 = 1.0 / s0
eps_site = (6 / d0 + 11 / d0 ** 2 + 6 / d0 ** 3)               # ||G_site(d)/d^4 - I||_inf for d >= d0
LKmax = 16 * nGa * (1 / (1 - eps_site)) ** 4 * (1 + 1e-6)
tot = S0 + s0 * S1 + s0 ** 2 * S2
log('UNIFORM BOUND on [0, s0 = %.3e] (d >= %.4g): LK <= %.5f; S0 %.4e + s0 S1 %.4e + s0^2 S2 %.4e = %.4e; '
    'gamma - LK * total = %.6e' % (s0, d0, LKmax, S0, s0 * S1, s0 ** 2 * S2, tot, gamma - LKmax * tot))
pickle.dump(dict(rep=rep, S0=S0, S1=S1, S2=S2, s0=s0, LKmax=LKmax, gamma=gamma, mu=mu, t=base['t'],
                 margin=gamma - LKmax * tot), open(outp, 'wb'), protocol=4)
