"""EXACT all-d check of a k-copy s = 0 certificate (any k; src blocks), generalising k4/word_exact.py (k = 4, all words) to
site-permutation classes (verify_cert6's multiset trick) so that k = 5 is cheap.

Rounded certificate (what is verified):
  - blocks: Q_b = M_b M_b^T with M_b = M_int 2^-E (exactly PSD); raw site data = FT_poly coefficients (integers, uni/ftpoly.pkl),
    ancilla data = ExactLocal(2, 4, cut).FT (integers);
  - equalities: compressed rows of meta_s0_k.py (one S_k-orbit representative of the site output indices), site S3 Fourier
    folded into S3 words, ancilla re-expressed on literal rows of G_a A_slot (contrasts) / G_a3 dm2 (marginals) as in
    word_exact.py, multipliers rounded to 2^-Elam;
  - objective / trace with t and nu exact rationals.
Residual rho^(n)(V_w) = c - nu tau - sum <Q, M^(n)> - lam.E^(n) = R0(w) + s R1(w) + r2(w) (Lemma P).  Class sums (multiset of
the k site letters, ancilla letter) of R0, R1 are computed modulo primes p < 2^20 (float64 BLAS, all intermediates exact
integers < 2^53), orbit sums (G_f x G_f letterwise, inversion; orbits are unions of classes) by CRT against an absolute-value
float shadow.  S2 = sum_w |r2(w)| / s^2 is bounded in floating point from nonnegative terms only.
Lemma TS: q_k >= nu - LK(n) (S0 + s S1 + s^2 S2) with LK(n) <= 16 ||G_a^+||_inf / (1 - 6 s - 11 s^2 - 6 s^3)^k.
Usage: verify_alld_k.py cert_export.pkl s0 nproc out.pkl [nprimes]"""
import os, sys, pickle, time, itertools, math
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'zm'))

import numpy as np
import scipy.sparse as sps
from fractions import Fraction
from relax import P4, I4, I3, SWAP03, FAMILY_GROUP, FAMILIES, Relaxation
from local import compose, inverse, ncycles
from exact import ExactLocal

t00 = time.time()
log = lambda s_: print('[%.0fs] %s' % (time.time() - t00, s_), flush=True)
cert = pickle.load(open(sys.argv[1], 'rb'))
s0 = Fraction(sys.argv[2]); nproc = int(sys.argv[3]); outp = sys.argv[4]
NPR = int(sys.argv[5]) if len(sys.argv) > 5 else 0
K = cert['k']
tq = Fraction(cert['t'])
nuq = Fraction(cert['nu'])
FTP = pickle.load(open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'data', 'ftpoly.pkl'), 'rb'))


def primes_below(n, count):
    out, x = [], n - 1
    while len(out) < count:
        if x > 2 and all(x % q for q in range(2, int(math.isqrt(x)) + 1)):
            out.append(x)
        x -= 1
    return out


# ---------------- multisets (classes) and orbits ----------------
class Multisets:
    def __init__(self, k):
        self.k = k
        self.levels = [list(itertools.combinations_with_replacement(range(24), j)) for j in range(k + 1)]
        self.index = [{m: i for i, m in enumerate(lv)} for lv in self.levels]
        self.scatter = []
        for j in range(k):
            nxt = self.index[j + 1]
            tgt = np.array([nxt[tuple(sorted(m + (w,)))] for m in self.levels[j] for w in range(24)], dtype=np.int64)
            n_src = len(self.levels[j]) * 24
            self.scatter.append(sps.csr_matrix((np.ones(n_src), (tgt, np.arange(n_src))), shape=(len(self.levels[j + 1]), n_src)))

    @property
    def npoints(self):
        return len(self.levels[self.k]) * 24


def point_orbits(MS, f):
    top, idx = MS.levels[MS.k], MS.index[MS.k]
    mul = [[I4[compose(p, q)] for q in P4] for p in P4]
    inv = [I4[inverse(p)] for p in P4]
    maps = []

    def build(fn):
        mm = np.array([idx[tuple(sorted(fn(w) for w in m))] for m in top], dtype=np.int64)
        aa = np.array([fn(a) for a in range(24)], dtype=np.int64)
        return (mm[:, None] * 24 + aa[None, :]).reshape(-1)
    for g in FAMILY_GROUP[f]:
        gi = I4[g]
        maps.append(build(lambda w, gi=gi: mul[gi][w]))
        maps.append(build(lambda w, gi=gi: mul[w][gi]))
    maps.append(build(lambda w: inv[w]))
    lab = np.arange(MS.npoints, dtype=np.int64)
    while True:
        old = lab.copy()
        for m in maps:
            np.minimum(lab, lab[m], out=lab)
        lab = lab[lab]
        if np.array_equal(lab, old):
            break
    uniq, oid = np.unique(lab, return_inverse=True)
    return oid.reshape(-1).astype(np.int64), len(uniq)


def ms_contract(X, As, Aa, MS, p=None, Bs=None):
    """class sums of ((x)_l A_l (x) Aa) X; X (q_0, .., q_{k-1}, q_a); A_l (24 x q_l); Aa (24 x q_a).  p: residues mod p.
    With Bs (B_l or None per site) also the first-order term sum_l (A_0 x .. B_l .. x A_{k-1} x Aa) X in the same pass
    (value / derivative pair, as for R0 and R1); returns (T0, T1) then."""
    k = MS.k
    V0 = np.asarray(X, dtype=np.float64).reshape(1, -1)
    V1 = None

    def lay(V, n, q, rest):
        return V.reshape(n, q, rest).transpose(1, 0, 2).reshape(q, n * rest)

    def scat(U, j, n, rest):
        if p is not None:
            np.fmod(U, p, out=U)
        V = MS.scatter[j] @ U.reshape(24, n, rest).transpose(1, 0, 2).reshape(n * 24, rest)
        if p is not None:
            np.fmod(V, p, out=V)
        return V
    for j in range(k):
        q = As[j].shape[1]
        n = V0.shape[0]
        rest = V0.shape[1] // q
        T0 = lay(V0, n, q, rest)
        U1 = As[j] @ lay(V1, n, q, rest) if V1 is not None else None
        if Bs is not None and Bs[j] is not None:
            W = Bs[j] @ T0
            U1 = W if U1 is None else U1 + W
        V0 = scat(As[j] @ T0, j, n, rest)
        V1 = scat(U1, j, n, rest) if U1 is not None else None
    out0 = V0 @ Aa.T
    if p is not None:
        np.fmod(out0, p, out=out0)
    if Bs is None:
        return out0.reshape(-1)
    if V1 is None:
        return out0.reshape(-1), np.zeros(out0.size)
    out1 = V1 @ Aa.T
    if p is not None:
        np.fmod(out1, p, out=out1)
    return out0.reshape(-1), out1.reshape(-1)


MS = Multisets(K)
ORB = {f: point_orbits(MS, f) for f in FAMILIES}
log('k = %d: %d class points; orbits %s' % (K, MS.npoints, {f: ORB[f][1] for f in FAMILIES}))

# ---------------- exact inputs: blocks ----------------
blocks = cert['blocks']
assert all(b['kind'] == 'src' for b in blocks)
Mmax = max(np.abs(b['M']).max() for b in blocks)
E = int(os.environ.get("MBITS", "62")) - int(math.floor(math.log2(Mmax)))      # |M_int| < 2^63
for b in blocks:
    b['Mi'] = np.rint(b['M'] * 2.0 ** E).astype(np.int64)
log('blocks: %d, raw factors rounded to 2^-%d (max |M| %.3e)' % (len(blocks), E, Mmax))
SITE = {c: (np.array(P['coef'], dtype=object), P['off'], P['labels'], P['dims']) for c, P in FTP.items()}


def site_ab(c, li):
    coef, off, labels, _ = SITE[c]
    f = labels[li][0]
    rows = slice(off[li], off[li + 1])
    a = np.array(coef[2 * f, rows], dtype=np.int64)
    b = np.array(coef[2 * f - 1, rows], dtype=np.int64) if f >= 1 else np.zeros_like(a)
    W = sum(np.abs(np.array(coef[2 * f - j, rows], dtype=np.float64)) for j in range(2, 2 * f + 1)) if f >= 1 else np.zeros(a.shape)
    return a, b, W


ANC = {}
for b in blocks:
    c = b['cut']
    if c not in ANC:
        la_ = ExactLocal(2, 4, c)
        ANC[c] = (np.array(la_.FT, dtype=np.int64), la_.off)
keys = {}
for bi, b in enumerate(blocks):
    keys.setdefault((b['cut'], tuple(b['st']), b['ai'], b['f']), []).append(bi)
log('%d block keys' % len(keys))


def module_tensor(Q, dims):
    L_ = len(dims)
    T = np.asarray(Q).reshape(dims + dims)
    order = []
    for i in range(L_):
        order += [i, L_ + i]
    return T.transpose(order).reshape([d * d for d in dims])


def key_dims(key):
    cut, st, ai, f = key
    _, off, labels, dims = SITE[cut]
    FTa, offa = ANC[cut]
    da = int(round(math.sqrt(offa[ai + 1] - offa[ai])))
    return [dims[li] for li in st] + [da]


# ---------------- equality multipliers: fold s3 Fourier, literal ancilla rows, dyadic rounding ----------------
R5 = Relaxation(1, 5, verbose=False)          # only embed / delete matrices (k-independent) are used
Ga = np.array([[2 ** ncycles(compose(inverse(v), w)) for w in P4] for v in P4], dtype=np.int64)
P3 = [p for p in itertools.permutations(range(3))]
Ga3 = np.array([[2 ** ncycles(compose(inverse(v), w)) for w in P3] for v in P3], dtype=np.int64)
s3FT, a3FT, laFT = cert['s3FT'], cert['a3FT'], cert['laFT']
reps = cert['reps']


def dm_site(slot, order, j):
    if order is None:
        order = tuple(i for i in range(4) if i != slot)
    M = np.zeros((6, 24), dtype=np.int64)
    for a_, p in enumerate(P4):
        if (p[slot] == slot) == (j == 0):
            M[I3[tuple(order.index(p[slot] if p[i] == slot else p[i]) for i in order)], a_] += 1
    return M


eqparts = []
for g in cert['groups']:
    lamg = g['lam']                                            # (nrep, na) on compressed rows
    na = lamg.shape[1]
    L_ = np.zeros((6,) * K + (na,))
    for r, row in zip(reps, lamg):
        L_[tuple(r)] += row                                    # each compressed row sits at its representative index
    for _ in range(K):
        L_ = np.tensordot(L_, s3FT, axes=([0], [0]))           # site Fourier axes -> S3 words, appended at the end
    L_ = np.moveaxis(L_, 0, -1)                                # (u_0, .., u_{K-1}, alpha)
    for f, slot, order, sg in g['parts']:
        if g['kind'] == 'stiefel':
            FTa, Gx, aden = laFT, Ga, 2
            Amap = Ga @ (2 * np.eye(24) - R5.embed_matrix(slot) @ R5.delete_matrix(2, slot)).round().astype(np.int64)
        else:
            FTa, Gx, aden = a3FT, Ga3, 1
            Amap = Ga3 @ R5.delete_matrix(2, slot, order).round().astype(np.int64)
        phi = L_ @ FTa                                         # functional on ancilla words (24 or S3 words 6)
        mu_ = phi @ np.linalg.pinv(Gx.astype(float))
        eqparts.append(dict(f=f, slot=slot, order=order, sg=int(sg), Amap=Amap, aden=aden, mu=mu_))
mumax = max(np.abs(e['mu']).max() for e in eqparts)
Elam = int(os.environ.get("MBITS", "62")) - int(math.floor(math.log2(mumax)))
for e in eqparts:
    e['mui'] = np.rint(e['mu'] * 2.0 ** Elam).astype(np.int64)
log('equality multipliers on literal ancilla rows, rounded to 2^-%d' % Elam)

# ---------------- common denominator, objective / trace factors ----------------
tden = tq.denominator
Den = math.lcm(2 ** (2 * E), 2 ** Elam * 2, tden ** K * 16, nuq.denominator * 16)
fac_blk = Den // 2 ** (2 * E)
fac_obj = Den // (tden ** K * 16)
fac_tr = Den // (nuq.denominator * 16) * nuq.numerator
nc = np.array([ncycles(p) for p in P4]); ncs = np.array([ncycles(compose(SWAP03, p)) for p in P4])
z0 = [((nc == 4 - j) * tden - tq.numerator * (ncs == 4 - j)).astype(np.int64) for j in range(4)]
ztr = [(nc == 4 - j).astype(np.int64) for j in range(4)]
za = (2 ** ncs).astype(np.int64); zatr = (2 ** nc).astype(np.int64)
col = lambda v: np.asarray(v, dtype=np.int64).reshape(24, 1)
ONE = np.ones([1] * (K + 1))


def eq_terms(e):
    """site maps of an equality part: value [p fixes slot] and s-coefficient [p moves slot], as (24 x 6) matrices"""
    return dm_site(e['slot'], e['order'], 0).T, dm_site(e['slot'], e['order'], 1).T


# ---------------- modular class sums ----------------
def run_prime(p):
    tp = time.time()
    pm = lambda A: np.mod(np.asarray(A, dtype=np.int64), p).astype(np.float64)
    R0 = {f: np.zeros(MS.npoints) for f in FAMILIES}; R1 = {f: np.zeros(MS.npoints) for f in FAMILIES}
    for key, lst in keys.items():
        cut, st, ai, f = key
        Q = np.zeros((blocks[lst[0]]['n_raw'],) * 2)
        for bi in lst:
            X = pm(blocks[bi]['Mi'])
            Q = np.fmod(Q + np.fmod(X @ X.T, p), p)
        Xm = module_tensor(Q, key_dims(key))
        ab = [site_ab(cut, li) for li in st]
        FTa, offa = ANC[cut]
        anc = pm(FTa[offa[ai]:offa[ai + 1]]).T                  # (24 x q_a)
        T0, T1 = ms_contract(Xm, [pm(x[0]).T for x in ab], anc, MS, p, Bs=[pm(x[1]).T if np.any(x[1]) else None for x in ab])
        R0[f] = np.mod(R0[f] - (fac_blk % p) * T0, p)
        R1[f] = np.mod(R1[f] - (fac_blk % p) * T1, p)
    for zz, zx, sg, fac in ((z0, za, 1, fac_obj), (ztr, zatr, -1, fac_tr)):
        T0, T1 = ms_contract(ONE, [pm(col(zz[0]))] * K, pm(col(zx)), MS, p, Bs=[pm(col(zz[1]))] * K)
        R0['31'] = np.mod(R0['31'] + sg * (fac % p) * T0, p)
        R1['31'] = np.mod(R1['31'] + sg * (fac % p) * T1, p)
    for e in eqparts:
        a, b = eq_terms(e)
        facq = Den // (2 ** Elam * e['aden'])
        T0, T1 = ms_contract(pm(e['mui']), [pm(a)] * K, pm(e['Amap']).T, MS, p, Bs=[pm(b)] * K)
        R0[e['f']] = np.mod(R0[e['f']] - e['sg'] * (facq % p) * T0, p)
        R1[e['f']] = np.mod(R1[e['f']] - e['sg'] * (facq % p) * T1, p)
    out = {}
    for f in FAMILIES:
        oid, norb = ORB[f]
        out[f] = tuple(np.mod(np.rint(np.bincount(oid, weights=np.mod(np.rint(x), p), minlength=norb)).astype(np.int64), p)
                       for x in (R0[f], R1[f]))
    print('   prime %d done in %.0fs' % (p, time.time() - tp), flush=True)
    return p, out


# ---------------- absolute shadow (magnitude bounds) and the S2 majorant ----------------
def shadow():
    tp = time.time()
    A0 = {f: np.zeros(MS.npoints) for f in FAMILIES}; A1 = {f: np.zeros(MS.npoints) for f in FAMILIES}; B2 = 0.0
    for key, lst in keys.items():
        cut, st, ai, f = key
        Qb = np.zeros((blocks[lst[0]]['n_raw'],) * 2)
        for bi in lst:
            Mb = np.abs(blocks[bi]['Mi'].astype(np.float64))
            Qb += Mb @ Mb.T
        Qb *= 2.0 ** (-2 * E)
        Xm = module_tensor(Qb, key_dims(key))
        ab = [site_ab(cut, li) for li in st]
        FTa, offa = ANC[cut]
        anc = np.abs(FTa[offa[ai]:offa[ai + 1]]).astype(np.float64).T
        aa = [np.abs(x[0]).astype(np.float64).T for x in ab]; bb = [np.abs(x[1]).astype(np.float64).T for x in ab]
        WW = [x[2].T for x in ab]
        T0, T1 = ms_contract(Xm, aa, anc, MS, Bs=bb)
        A0[f] += T0; A1[f] += T1
        B2 += ms_contract(Xm, [aa[m] + bb[m] + WW[m] for m in range(K)], anc, MS).sum()
    for zz, zx, wgt in ((z0, za, 1.0 / (tden ** K * 16)), (ztr, zatr, float(nuq) / 16)):
        av = [np.abs(col(x)).astype(np.float64) for x in zz]; ax = np.abs(col(zx)).astype(np.float64)
        T0, T1 = ms_contract(ONE, [av[0]] * K, ax, MS, Bs=[av[1]] * K)
        A0['31'] += wgt * T0; A1['31'] += wgt * T1
        B2 += wgt * ms_contract(ONE, [av[0] + av[1] + sum(av[2:])] * K, ax, MS).sum()
    for e in eqparts:
        a, b = eq_terms(e)
        a = a.astype(np.float64); b = b.astype(np.float64)
        wgt = 2.0 ** (-Elam) / e['aden']
        Xe = np.abs(e['mui']).astype(np.float64); Aa = np.abs(e['Amap']).astype(np.float64).T
        T0, T1 = ms_contract(Xe, [a] * K, Aa, MS, Bs=[b] * K)
        A0[e['f']] += wgt * T0; A1[e['f']] += wgt * T1
        B2 += wgt * ms_contract(Xe, [a + b] * K, Aa, MS).sum()
    print('   shadow done in %.0fs' % (time.time() - tp), flush=True)
    return A0, A1, B2 * (1 + 1e-9)


# enough primes for |integer numerators| < Den * 2^60 (checked against the shadow below)
NPR = max(NPR, -(-(Den.bit_length() + 62) // 19))
PRIMES = primes_below(1 << 20, NPR)
for key in keys:
    assert blocks[keys[key][0]]['n_raw'] == math.prod(key_dims(key)), key
assert max(b['Mi'].shape[1] for b in blocks) < 4096          # X X^T mod p: r p^2 < 2^53


def task(x):
    return shadow() if x is None else run_prime(x)


import multiprocessing as mp
log('Den = 2^%d * %d (%d bits); %d primes < 2^20; %d tasks on %d processes' % (
    (Den & -Den).bit_length() - 1, Den // (Den & -Den), Den.bit_length(), len(PRIMES), len(PRIMES) + 1, min(nproc, len(PRIMES) + 1)))
with mp.get_context('fork').Pool(min(nproc, len(PRIMES) + 1)) as pool:
    allres = pool.map(task, [None] + PRIMES)
(A0, A1, B2), resl = allres[0], allres[1:]
log('modular orbit sums (%d primes) and float shadow done; S2 majorant %.4e' % (len(PRIMES), B2))
Mprod = math.prod(PRIMES)


def crt(residues):
    x = 0
    for (p, r) in residues:
        Mi = Mprod // p
        x = (x + r * Mi * pow(Mi, -1, p)) % Mprod
    return x - Mprod if x > Mprod // 2 else x


S0 = Fraction(0); S1 = Fraction(0); rep = {}
for f in FAMILIES:
    oid, norb = ORB[f]
    a0 = np.bincount(oid, weights=A0[f], minlength=norb) * Den * (1 + 1e-9) + 1
    a1 = np.bincount(oid, weights=A1[f], minlength=norb) * Den * (1 + 1e-9) + 1
    assert a0.max() < Mprod / 4 and a1.max() < Mprod / 4, 'need more primes (bound 2^%d vs Mprod 2^%d)' % (
        int(math.log2(max(a0.max(), a1.max()))), Mprod.bit_length())
    N0 = [crt([(p, int(r[f][0][o])) for p, r in resl]) for o in range(norb)]
    N1 = [crt([(p, int(r[f][1][o])) for p, r in resl]) for o in range(norb)]
    bad = sum(1 for o in range(norb) if abs(N0[o]) > a0[o] or abs(N1[o]) > a1[o])
    assert bad == 0, 'CRT value exceeds the magnitude bound (%d orbits)' % bad
    s0f = Fraction(sum(abs(x) for x in N0), Den); s1f = Fraction(sum(abs(x) for x in N1), Den)
    rep[f] = dict(norb=norb, S0=s0f, S1=s1f, maxR0=Fraction(max(abs(x) for x in N0), Den))
    if os.environ.get('DUMP_RESID'):          # exact orbit residuals (as floats) for the y-space correction step
        rep[f].update(R0=np.array([x / Den for x in N0]), R1=np.array([x / Den for x in N1]), oid=oid)
    S0 += s0f; S1 += s1f
    log('family %s: %d orbits, EXACT S0 = %.6e (max orbit %.3e), S1 = %.6e' % (f, norb, float(s0f), float(rep[f]['maxR0']), float(s1f)))
import sympy
Gap = sympy.Matrix(Ga.tolist()).pinv()
nGa = max(sum(abs(Gap[i, j]) for j in range(24)) for i in range(24))
eps = 6 * s0 + 11 * s0 ** 2 + 6 * s0 ** 3
LK = 16 * Fraction(str(nGa)) / (1 - eps) ** K
total = S0 + s0 * S1 + s0 ** 2 * Fraction(math.ceil(B2))
margin = nuq - LK * total
log('EXACT: ||G_a^+||_inf = %s; LK <= %.6f for d >= %s; S0 %.6e + s0 S1 %.6e + s0^2 S2 %.6e; nu - LK total = %.6e  => %s' %
    (nGa, float(LK), 1 / s0, float(S0), float(s0 * S1), float(s0 ** 2 * Fraction(B2)), float(margin), 'PASS' if margin > 0 else 'FAIL'))
if os.environ.get('DUMP_RESID'):
    pickle.dump(dict(k=K, rep={f: dict(R0=rep[f]['R0'], R1=rep[f]['R1'], oid=rep[f]['oid'], norb=rep[f]['norb']) for f in FAMILIES}),
                open(os.environ['DUMP_RESID'], 'wb'), protocol=4)
    log('orbit residuals written to %s' % os.environ['DUMP_RESID'])
pickle.dump(dict(rep=rep, S0=S0, S1=S1, S2=B2, s0=s0, LK=LK, nu=nuq, t=tq, k=K, margin=margin, E=E, Elam=Elam, primes=PRIMES,
                 Den=Den), open(outp, 'wb'), protocol=4)
