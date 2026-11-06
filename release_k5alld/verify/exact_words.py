"""Exact residues mod p of the ORBIT SUMS of the s^0 and s^1 coefficients (R0, R1) of the word-level residual of the
k = 5, t = 9/20 certificate, for one family f and one chunk of its multiplier keys.  Own implementation (auditor).

Full word space: every family-f term is expanded to all 24^6 words (no site-permutation class reduction), then
summed over the word-level orbits of orbits_words.py.  Terms (each an integer multiple of 1/Den):
  blocks     - sum_b <Q_b, M_b(x)>, Q_b = Mi Mi^T 2^-2E (Mi = round(M 2^E)), raw block
             M_key(x) = sum_w x(w) (x)_l P_l(s)[:, w_l] (x) P_a[:, w_a]   (per-site polynomial data, ancilla n = 2 data);
  objective  + (1/16) prod_l n^-4 (n^nc(w_l) - t n^nc(S w_l)) 2^nc(S w_a)                         (family 31 only);
  trace      - nu (1/16) prod_l n^(nc(w_l) - 4) 2^nc(w_a)                                       (family 31 only);
  equalities - sg mui[v, a'] prod_l (n^-1 Tr_slot)[v_l, w_l] Amap[a', w_a] / (2^Elam aden)        (k5defs.equality_parts).
Arithmetic: residues in [0, p) held in float64, p < 2^21; every BLAS product/partial sum < 2^53 (inner dims <= 213 for
Mi Mi^T, <= 16 per site), so all contractions are exact; the per-word accumulators are reduced every 128 keys.
Usage: exact_words.py p f chunk nchunk ORBDIR out.npz [selftest]
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.linalg.blas import dgemm
import k5defs as KD

t00 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t00, s), flush=True)
p = int(sys.argv[1]); f = sys.argv[2]; chunk = int(sys.argv[3]); nchunk = int(sys.argv[4])
ORB = sys.argv[5]; outp = sys.argv[6]
SELFTEST = len(sys.argv) > 7 and sys.argv[7] == 'selftest'
assert p < 2 ** 21 and f in KD.FAMS
FP = float(p)
NW, K = KD.NW, KD.K
W5 = NW ** K

cert = KD.load_cert()
FTP = KD.load_ftp()
E = KD.m_exponent(cert)
keys = KD.block_keys(cert)
klist = sorted([k for k in keys if k[3] == f], key=lambda k: repr(k))
mine = klist[chunk::nchunk]
parts, Elam, diag = KD.equality_parts(cert)
Den = KD.common_den(E, Elam)
log('p=%d f=%s chunk %d/%d: %d of %d keys; E=%d Elam=%d Den=2^%d*%d' % (
    p, f, chunk, nchunk, len(mine), len(klist), E, Elam, (Den & -Den).bit_length() - 1, Den // (Den & -Den)))


def rmod(A):
    """residues in [0, p) (float64) of an integer array (int64, or object array of python ints)"""
    A = np.asarray(A)
    if A.dtype == object:
        return np.array([int(x) % p for x in A.ravel()], dtype=np.float64).reshape(A.shape)
    assert A.dtype.kind in 'iu'
    return np.mod(A.astype(np.int64), p).astype(np.float64)


def fac(num_den):
    """residue of the rational Den * (num / den), an integer"""
    num, den = num_den
    v = Den * num
    assert v % den == 0
    return (v // den) % p


NWORD = NW ** (K + 1)
acc0 = np.zeros(NWORD)
acc1 = np.zeros(NWORD)
ACC0_T = acc0.reshape(W5, NW).T       # Fortran-contiguous (24 x 24^5) views for the fused final dgemm
ACC1_T = acc1.reshape(W5, NW).T
nterm = 0


def reduce_acc():
    np.fmod(acc0, FP, out=acc0)
    np.fmod(acc1, FP, out=acc1)


def contract_add(T, As, Bs):
    """T: core tensor (D_0, .., D_5) residues; As[i] (D_i x 24) residues; Bs[i] (D_i x 24) or None (s^1 part at site i).
    Adds to acc0 the word tensor sum T (x)_i As[i]   and to acc1 the first-order part sum_i (.. Bs[i] at slot i ..).
    Axis i is contracted at the front and its word axis appended at the end, so after 6 steps the axes are
    (w_0, .., w_4, w_a) in natural order; the last step is fused into the accumulators (dgemm with beta = 1)."""
    global nterm
    assert Bs[K] is None
    V0 = np.ascontiguousarray(T, dtype=np.float64)
    V1 = None
    for i in range(K + 1):
        A = As[i]
        Di = A.shape[0]
        X0 = V0.reshape(Di, -1)
        X1 = V1.reshape(Di, -1) if V1 is not None else None
        if i < K:
            N1 = None
            if X1 is not None:
                N1 = X1.T @ A
            if Bs[i] is not None:
                tb = X0.T @ Bs[i]
                N1 = tb if N1 is None else N1 + tb
            N0 = X0.T @ A
            np.fmod(N0, FP, out=N0)
            if N1 is not None:
                np.fmod(N1, FP, out=N1)
            V0, V1 = N0, N1
        else:
            assert X0.shape[1] == W5
            r = dgemm(1.0, np.asfortranarray(A.T), X0.T, beta=1.0, c=ACC0_T, trans_b=1, overwrite_c=1)
            assert np.shares_memory(r, acc0)
            if X1 is not None:
                r = dgemm(1.0, np.asfortranarray(A.T), X1.T, beta=1.0, c=ACC1_T, trans_b=1, overwrite_c=1)
                assert np.shares_memory(r, acc1)
    nterm += 1
    if nterm % 128 == 0:
        reduce_acc()


# ---------------- site / ancilla data (residues) ----------------
SITE = {}


def site_ab(cut, li):
    if (cut, li) not in SITE:
        C = KD.site_poly(FTP, cut, li)
        a = rmod(C[0])
        b = rmod(C[1]) if len(C) > 1 and np.any(C[1]) else None
        SITE[cut, li] = (a, b)
    return SITE[cut, li]


def anc_rows(cut, ai):
    _, adims, off, FT = KD.anc_ft(cut)
    return rmod(FT[off[ai]:off[ai + 1]])


def key_core(key):
    """core tensor (residues, times the block factor -Den/2^2E) of a multiplier key"""
    cut, st, ai, ff = key
    dims = KD.key_dims(FTP, key)
    n = int(np.prod(dims))
    Q = np.zeros((n, n))
    for bi in keys[key]:
        b = cert['blocks'][bi]
        assert b['n_raw'] == n and b['M'].shape[0] == n and b['M'].shape[1] < 2048
        X = rmod(KD.rounded_M(b, E))
        Q += X @ X.T
        np.fmod(Q, FP, out=Q)
    Q = np.fmod(Q * float((-fac((1, 2 ** (2 * E)))) % p), FP)
    L = len(dims)
    T = Q.reshape(dims + dims)
    order = []
    for i in range(L):
        order += [i, L + i]
    return np.ascontiguousarray(T.transpose(order).reshape([d * d for d in dims])), dims


tk = time.time()
for ik, key in enumerate(mine):
    cut, st, ai, ff = key
    T, dims = key_core(key)
    ab = [site_ab(cut, li) for li in st]
    contract_add(T, [x[0] for x in ab] + [anc_rows(cut, ai)], [x[1] for x in ab] + [None])
    if ik % 100 == 0:
        log('key %d/%d (%.2f s/key)' % (ik, len(mine), (time.time() - tk) / (ik + 1)))
log('block terms done: %d keys in %.0f s' % (len(mine), time.time() - tk))

if chunk == 0:
    z, y, za, zat = KD.obj_trace_factors()
    if f == '31':
        ONE = np.ones((1,) * (K + 1))
        row = lambda v: rmod(v).reshape(1, NW)
        fo = fac((1, 16 * KD.T_Q.denominator ** K))
        ftr = (-fac((KD.NU_Q.numerator, 16 * KD.NU_Q.denominator))) % p
        contract_add(ONE * fo, [row(z[0])] * K + [row(za)], [row(z[1])] * K + [None])
        contract_add(ONE * ftr, [row(y[0])] * K + [row(zat)], [row(y[1])] * K + [None])
        log('objective / trace terms done')
    d0 = {}
    for e in parts:
        if e['f'] != f:
            continue
        key = (e['slot'], e['order'])
        if key not in d0:
            d0[key] = (rmod(KD.delete_site(e['slot'], e['order'], 0)), rmod(KD.delete_site(e['slot'], e['order'], 1)))
        a, b = d0[key]
        fq = fac((1, 2 ** Elam * e['aden']))
        fe = (-e['sg'] * fq) % p
        Tc = np.fmod(rmod(e['mui']) * float(fe), FP)
        contract_add(Tc, [a] * K + [rmod(e['Amap'])], [b] * K + [None])
        log('equality part %s %s slot %d done' % (e['kind'], e['f'], e['slot']))
reduce_acc()

oid = np.load(os.path.join(ORB, 'oid_%s.npy' % f), mmap_mode='r')
norb = int(np.load(os.path.join(ORB, 'sizes_%s.npy' % f)).shape[0])
R0o = np.mod(np.bincount(oid, weights=acc0, minlength=norb), FP).astype(np.int64)
R1o = np.mod(np.bincount(oid, weights=acc1, minlength=norb), FP).astype(np.int64)
log('orbit sums: %d orbits' % norb)

if SELFTEST:
    # brute-force residues of the per-word block term at random words for the first keys (kron vectors, no BLAS path)
    rng = np.random.default_rng(p)
    for key in mine[:3]:
        T, dims = key_core(key)
        cut, st, ai, ff = key
        ab = [site_ab(cut, li) for li in st]
        As = [x[0] for x in ab] + [anc_rows(cut, ai)]
        Bs = [x[1] for x in ab] + [None]
        acc0[:] = 0; acc1[:] = 0
        contract_add(T, As, Bs)
        reduce_acc()
        Tf = T.reshape(-1)
        for _ in range(20):
            w = rng.integers(0, NW, size=K + 1)
            v = np.ones(1)
            for i in range(K + 1):
                v = np.fmod(np.multiply.outer(v, As[i][:, w[i]]).reshape(-1), FP)
            val0 = int(np.fmod(np.sum(np.fmod(Tf * v, FP)), FP))      # every partial sum < 2^21 * 2^24 < 2^53
            val1 = 0
            for l in range(K):
                if Bs[l] is None:
                    continue
                v = np.ones(1)
                for i in range(K + 1):
                    col = (Bs[i] if i == l else As[i])[:, w[i]]
                    v = np.fmod(np.multiply.outer(v, col).reshape(-1), FP)
                val1 += int(np.fmod(np.sum(np.fmod(Tf * v, FP)), FP))
            idx = int(np.ravel_multi_index(tuple(w), (NW,) * (K + 1)))
            assert int(acc0[idx]) == val0 % p and int(acc1[idx]) == val1 % p, ('selftest mismatch', key, w)
        log('selftest key %s: 20 random words agree (brute force)' % (key,))

np.savez(outp, p=p, f=f, chunk=chunk, nchunk=nchunk, nkeys=len(mine), E=E, Elam=Elam, Den=str(Den), R0o=R0o, R1o=R1o)
log('saved %s' % outp)
