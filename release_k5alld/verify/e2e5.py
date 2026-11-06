"""End-to-end checks of the k = 5 word-level conventions on PHYSICAL points (audit item 6; own implementation).

Physical rank-2 points that are ENTANGLED across the 5 sites:
    C = sum_{r=0,1} (x)_l u_{l,r} v_{l,r}^T   (real vectors in C^m, m = 4, zero-padded into C^n),
    a = sum_r |r> (x) a_r, a_r = (x)_l u_{l,r};  b = sum_r |r> (x) b_r, b_r = (x)_l v_{l,r},
normalised to A^*A = I/2 (u_{0,0} perp u_{0,1}, |u_{0,r}| = 1/sqrt2, other |u_{l,r}| = 1) and ||b|| = 1.
The four-replica moment psi = psi_0 (x) .. (x) psi_3 (pattern aaab / aabb / bbba) is a sum of 16 product vectors,
so its trace coordinates g_v = <psi|V_v|psi> (v in S_4^5 x S_4) are a sum of 256 product tensors, and so are the
coefficients xhat = (G_a^+ (x) Ghat(n)^-1 ^(x)5) g  (Ghat = G_site / n^4; xhat = n^20 x).  Checks at n = 4, 50, 1000, 1e10:
  (1) 16 n^20 c(x) = sum xhat . (x)_l z(s) (x) za  equals  q_5(t, C) ||a||^4       (objective, t = 9/20)
  (2) 16 n^20 tau(x) equals Tr X_31 = ||a||^6 ||b||^2 = 1                          (trace)
  (3) max_w |xhat_w| <= LK(n) Tr X_f / 16 for f = 31, 22, 13 at n = 1e10            (Lemma TS; full 24^6 tensor)
  (4) every literal equality row (all v, all a') vanishes                           (Stiefel contrasts, marginals)
  (5) every raw block M_key(x) of the certificate is PSD (min eigenvalue), and <Q_key, M_key(x)> >= 0.
Usage: e2e5.py seed n [SAMPLE]   (SAMPLE = all (default): every key in (5); an integer N: all keys with n_raw <= 256
       plus N keys spread evenly over the larger ones)
"""
import os, sys, time, itertools, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import k5defs as KD

t0 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
seed = int(sys.argv[1])
NS = [float(sys.argv[2])] if len(sys.argv) > 2 else [4.0, 50.0, 1000.0, 1e10]
SAMPLE = sys.argv[3] if len(sys.argv) > 3 else 'all'
rng = np.random.default_rng(seed)
K, P4 = KD.K, KD.P4
t = float(KD.T_Q)
m = 4
REPL = {'31': 'aaab', '22': 'aabb', '13': 'bbba'}

# ---------------- the physical point ----------------
U0 = np.linalg.qr(rng.standard_normal((m, 2)))[0] / np.sqrt(2)
u = [[U0[:, 0], U0[:, 1]]] + [[x / np.linalg.norm(x) for x in rng.standard_normal((2, m))] for _ in range(K - 1)]
v = [[x for x in rng.standard_normal((2, m))] for _ in range(K)]
nb2 = sum(np.prod([v[l][r] @ v[l][r] for l in range(K)]) for r in range(2))
v[0] = [x / np.sqrt(nb2) for x in v[0]]
AA = np.array([[np.prod([u[l][r] @ u[l][s] for l in range(K)]) for s in range(2)] for r in range(2)])
na2 = np.trace(AA)
nb2 = sum(np.prod([v[l][r] @ v[l][r] for l in range(K)]) for r in range(2))
assert np.allclose(AA, np.eye(2) / 2) and abs(nb2 - 1) < 1e-12
X = [[np.outer(u[l][r], v[l][r]) for r in range(2)] for l in range(K)]
q5 = 0.0
for J in itertools.product((0, 1), repeat=K):          # J_l = 1: site l traced
    val = 0.0
    for r in range(2):
        for s in range(2):
            term = 1.0
            for l in range(K):
                term *= (np.trace(X[l][r]) * np.trace(X[l][s])) if J[l] else np.sum(X[l][r] * X[l][s])
            val += term
    q5 += (-t) ** sum(J) * val
log('point: A*A = I/2, ||a||^2 = %.6f, ||b||^2 = %.6f, q_5(9/20, C) = %.9e' % (na2, nb2, q5))

Ga = KD.gram(P4, 2).astype(float)
Gap = np.linalg.pinv(Ga)
nGa = np.abs(Gap).sum(axis=1).max()
nc = np.array([KD.ncycles(p) for p in P4]); ncs = np.array([KD.ncycles(KD.compose(KD.SWAP03, p)) for p in P4])
ANCMAT = {}
for rr in itertools.product((0, 1), repeat=4):
    for rp in itertools.product((0, 1), repeat=4):
        ANCMAT[rr, rp] = np.array([float(all(rr[p[i]] == rp[i] for i in range(4))) for p in P4])


def terms(f, n):
    """list of (alpha (24,), [eta_l (24,)]) with xhat = sum alpha (x) eta_0 (x) .. (x) eta_4 (ancilla first here)"""
    Gh = np.array([[n ** (KD.ncycles(KD.compose(KD.inverse(a), b)) - 4) for b in P4] for a in P4])
    Ghi = np.linalg.inv(Gh)
    pat = REPL[f]
    vec = lambda l, rho, r: u[l][r] if pat[rho] == 'a' else v[l][r]
    out = []
    for rr in itertools.product((0, 1), repeat=4):
        for rp in itertools.product((0, 1), repeat=4):
            alpha = Gap @ ANCMAT[rr, rp]
            etas = []
            for l in range(K):
                h = np.array([np.prod([vec(l, p[i], rr[p[i]]) @ vec(l, i, rp[i]) for i in range(4)]) for p in P4])
                etas.append(Ghi @ h)
            out.append((alpha, etas))
    return out, Ghi


cert = KD.load_cert()
FTP = KD.load_ftp()
keys = KD.block_keys(cert)
parts, Elam, _ = KD.equality_parts(cert)
z, y, za, zat = KD.obj_trace_factors()
SITE = {}
for n in NS:
    s = 1.0 / n
    TM = {}
    for f in KD.FAMS:
        TM[f], Ghi = terms(f, n)
    LK = 16 * nGa * np.abs(Ghi).sum(axis=1).max() ** K
    zf = sum(z[j] / 20.0 * s ** j for j in range(4))
    yf = sum(y[j] * s ** j for j in range(4))
    cval = sum((za @ al) * np.prod([zf @ e for e in et]) for al, et in TM['31'])
    tval = sum((zat @ al) * np.prod([yf @ e for e in et]) for al, et in TM['31'])
    log('n=%-8.3g (1) 16n^20 c(x) = %.12e  q5 ||a||^4 = %.12e  rel.err %.1e' % (n, cval, q5 * na2 ** 2, abs(cval - q5 * na2 ** 2) / abs(q5)))
    log('           (2) 16n^20 tau(x) = %.12e  (Tr X_31 = 1)' % tval)
    assert abs(cval - q5 * na2 ** 2) <= 1e-9 * max(1.0, abs(q5)) and abs(tval - 1) < 1e-9
    if n == 1e10:
        for f in KD.FAMS:
            full = np.zeros(KD.NWORD)
            for al, et in TM[f]:
                T = al
                for e in et:
                    T = np.multiply.outer(T, e).reshape(-1)
                full += T                                      # word order here: (w_a, w_0, .., w_4)
            mx = np.abs(full).max()
            assert mx <= LK / 16 * (1 + 1e-9), ('Lemma TS fails', f, mx, LK / 16)
            log('           (3) family %s: max|xhat| = %.6e <= LK(n)/16 = %.6e  OK' % (f, mx, LK / 16))
            del full
    worst, scale = 0.0, 0.0
    # the two parts of each marginal group share one row space: consecutive 'marg' entries of parts
    marg = [e for e in parts if e['kind'] == 'marg']
    blocks_eq = [[e] for e in parts if e['kind'] == 'stiefel'] + [marg[i:i + 2] for i in range(0, len(marg), 2)]
    for grp in blocks_eq:
        tot = 0.0
        for e in grp:
            dmn = KD.delete_site(e['slot'], e['order'], 0) + s * KD.delete_site(e['slot'], e['order'], 1)
            Ep = 0.0
            for al, et in TM[e['f']]:
                T = e['Amap'] @ al
                for ee in et:
                    T = np.multiply.outer(T, dmn @ ee).reshape(-1)
                Ep = Ep + T
            scale = max(scale, np.abs(Ep).max())
            tot = tot + e['sg'] * Ep
        worst = max(worst, np.abs(tot).max())
    log('           (4) max |E(x)| over all literal equality rows = %.3e (part scale %.3e)' % (worst, scale))
    assert worst <= 1e-10 * max(1.0, scale)
    nneg, minrel, minq, nchk = 0, 1.0, 1e300, 0
    klist = sorted(keys, key=repr)
    if SAMPLE != 'all':
        small = [k for k in klist if np.prod(KD.key_dims(FTP, k)) <= 256]
        large = [k for k in klist if np.prod(KD.key_dims(FTP, k)) > 256]
        step = max(1, len(large) // int(SAMPLE))
        klist = small + large[::step]
    for ik, key in enumerate(klist):
        lst = keys[key]
        if ik % 500 == 0:
            log('           (5) key %d/%d' % (ik, len(klist)))
        cut, st, ai, f = key
        dims = KD.key_dims(FTP, key)
        nr = int(np.prod(dims))
        Pl = []
        for li in st:
            if (cut, li, n) not in SITE:
                C = KD.site_poly(FTP, cut, li)
                SITE[cut, li, n] = sum(Cj.astype(float) * s ** j for j, Cj in enumerate(C))
            Pl.append(SITE[cut, li, n])
        _, adims, off, FT = KD.anc_ft(cut)
        Pa = FT[off[ai]:off[ai + 1]].astype(float)
        M = np.zeros((nr, nr))
        sc = 0.0                                         # rounding reference: sum over terms of cancellation-free magnitudes
        for al, et in TM[f]:
            F = (Pl[0] @ et[0]).reshape(dims[0], dims[0])
            for l in range(1, K):
                F = np.kron(F, (Pl[l] @ et[l]).reshape(dims[l], dims[l]))
            Tm = np.kron(F, (Pa @ al).reshape(dims[K], dims[K]))
            # cancellation-free magnitude of this term (bounds its rounding errors)
            sc += np.prod([(np.abs(Pl[l]) @ np.abs(et[l])).max() for l in range(K)]) * (np.abs(Pa) @ np.abs(al)).max()
            M += Tm
        asym = np.abs(M - M.T).max()
        Ms = (M + M.T) / 2
        lmin = np.linalg.eigvalsh(Ms)[0] if nr <= 1100 else None
        Q = sum(cert['blocks'][bi]['M'] @ cert['blocks'][bi]['M'].T for bi in lst)
        qv = float(np.sum(Q * Ms))
        nchk += 1
        if lmin is not None:
            minrel = min(minrel, lmin / max(sc, 1e-300))
            if lmin < -1e-12 * sc:
                nneg += 1
        minq = min(minq, qv / max(np.abs(Q).sum() * sc, 1e-300))
        assert asym <= 1e-12 * max(sc, 1e-300), ('raw block not symmetric', key, asym, sc)
    log('           (5) %d keys: raw blocks with min eig < -1e-12 scale: %d (min eig/scale = %.3e over keys with n_raw <= 1100); '
        'min <Q,M>/(|Q|_1 scale) = %.3e (must be >= -1e-12)' % (nchk, nneg, minrel, minq))
    assert nneg == 0 and minq >= -1e-12
log('ALL CHECKS PASSED (seed %d)' % seed)
