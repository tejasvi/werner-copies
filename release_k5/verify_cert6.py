#!/usr/bin/env python3
"""Independent verifier (v6) for k-copy Werner certificates at a rational parameter t with a trace slack, any k.

Same claim, certificate format, residual lemma and checks as verify_cert5.py (see there and README).  The only
change is HOW the orbit sums R_f(o) of the residual functional are computed, so that k = 5 (24^6 words) is cheap:

* Every word orbit (G_f x G_f, inversion, permutations of the k site components) is a union of site-permutation
  classes, and a class is a pair (M, a): the multiset M of the k site letters and the auxiliary letter a.  The
  verifier works on these points (C(24+k-1, k) * 24 of them; k = 5: 2,358,720 instead of 191,102,976 words).
  G_f x G_f and inversion act on points (letterwise on M, then re-sorted), and the orbits of that action are
  exactly the word orbits.
* The class sum of a contraction (x)_l A_l applied to a module tensor X is accumulated factor by factor:
  V_{j+1}[M + {w}] += sum_i V_j[M, i] A_j[w, i] (all words whose site letters form the multiset M are summed), then
  the auxiliary factor is applied.  Objective and trace (equal maps on every site) are closed forms on points.
  The multiplier part runs modulo primes p < 2^20 (float64 matrix products, every intermediate an integer below
  2^53) with Chinese remaindering against a rigorous absolute-value bound; the objective, trace and equality parts
  are exact integers.
Nothing is imported from the construction code.
"""
import argparse
import itertools
import lzma
import math
import multiprocessing as mp
import pickle
import sys
import time
from fractions import Fraction

sys.set_int_max_str_digits(0)

import numpy as np
import flint
import scipy.sparse as sps

PERMS = tuple(itertools.permutations(range(4)))
IDX = {p: i for i, p in enumerate(PERMS)}
P3 = tuple(itertools.permutations(range(3)))
FAMILY_LETTERS = {'31': 'aaab', '22': 'aabb', '13': 'bbba', '40': 'aaaa', '04': 'bbbb'}
PMAX = 1 << 20


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(q)))


def inverse(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


# ------------------------------------------------------------ literal operators
def digits(x, n, m):
    return [(x // n ** (m - 1 - s)) % n for s in range(m)]


def undigits(ds, n):
    r = 0
    for x in ds:
        r = r * n + x
    return r


def perm_op(n, p):
    """Literal V_p on (C^n)^{x4}: V_p sends tensor factor i to factor p[i].  dict {(row, col): 1}."""
    ent = {}
    for src in itertools.product(range(n), repeat=4):
        tgt = [0] * 4
        for i in range(4):
            tgt[p[i]] = src[i]
        ent[(undigits(tgt, n), undigits(src, n))] = 1
    return ent


def parse_pattern(s):
    """'a a b* b' -> (('a', 0), ('a', 0), ('b', 1), ('b', 0))"""
    out = []
    for tok in s.split():
        out.append((tok[0], 1 if tok.endswith('*') else 0))
    assert len(out) == 4 and all(l in 'ab' for l, _ in out)
    return tuple(out)


def entry_rule(u, v):
    """Literal index rule of the entry |u><v| (partial transpose on the conjugated slots).
    Returns (family, kpos, lpos): entry[i; j] = X_f[k; l] with k_s = (i or j)[slot] as given by kpos[s] =
    ('i' | 'j', slot), similarly l from lpos."""
    assert all(cu == cv for (_, cu), (_, cv) in zip(u, v)), 'rows must share conjugation flags'
    unconj, conj = [], []
    for i in range(4):
        (lu, c), (lv, _) = u[i], v[i]
        if c == 0:
            unconj.append(('i', i, lu))      # component u_i[i_i]
            conj.append(('j', i, lv))        # conj(v_i[j_i])
        else:
            unconj.append(('j', i, lv))      # conj(conj(v_i[j_i]))
            conj.append(('i', i, lu))        # conj(u_i[i_i])
    letters = ''.join(sorted(x[2] for x in unconj))
    assert letters == ''.join(sorted(x[2] for x in conj)), 'unbalanced entry'
    fam = [f for f, L in FAMILY_LETTERS.items() if ''.join(sorted(L)) == letters]
    assert len(fam) == 1, 'no moment family for letters %s' % letters
    f = fam[0]
    L = FAMILY_LETTERS[f]

    def assign(factors):
        used = [False] * 4
        pos = []
        for s in range(4):
            for t, fac in enumerate(factors):
                if not used[t] and fac[2] == L[s]:
                    used[t] = True
                    pos.append((fac[0], fac[1]))
                    break
        assert len(pos) == 4
        return tuple(pos)
    return f, assign(unconj), assign(conj)


def entry_op(n, p, kpos, lpos):
    """Literal operator entry[i; j] = V_p[k; l] (k, l from (i, j) by the rule)."""
    out = {}
    for (r, c), v in perm_op(n, p).items():
        kd, ld = digits(r, n, 4), digits(c, n, 4)
        idig, jdig = [None] * 4, [None] * 4
        for s in range(4):
            for (which, slot), val in ((kpos[s], kd[s]), (lpos[s], ld[s])):
                (idig if which == 'i' else jdig)[slot] = val
        key = (undigits(idig, n), undigits(jdig, n))
        out[key] = out.get(key, 0) + v
    return out


def sandwich(J, ent):
    OJ = np.zeros((J.shape[0], J.shape[1]), dtype=object)
    for (r, c), v in ent.items():
        OJ[r, :] += v * J[c, :]
    return J.T.dot(OJ)


def partial_trace_replica(n, p, slot, order):
    """Literal Tr_slot V_p on (C^n)^{x4}, survivors relabelled by `order`: (factor, q) with
    Tr_slot V_p = factor * V_q on (C^n)^{x3}."""
    res = {}
    for (r, c), v in perm_op(n, p).items():
        rd, cd = digits(r, n, 4), digits(c, n, 4)
        if rd[slot] != cd[slot]:
            continue
        key = (undigits([rd[s] for s in order], n), undigits([cd[s] for s in order], n))
        res[key] = res.get(key, 0) + v
    for q in P3:
        Vq = perm3_op(n, q)
        if set(res) == set(Vq):
            vals = set(res.values())
            if len(vals) == 1:
                return vals.pop(), q
    raise AssertionError('partial trace not a multiple of a permutation operator')


def perm3_op(n, q):
    ent = {}
    for src in itertools.product(range(n), repeat=3):
        tgt = [0] * 3
        for i in range(3):
            tgt[q[i]] = src[i]
        ent[(undigits(tgt, n), undigits(src, n))] = 1
    return ent


def trace(ent):
    return sum(v for (r, c), v in ent.items() if r == c)


# ------------------------------------------------------------ exact helpers
def fz(A):
    A = np.asarray(A, dtype=object)
    return flint.fmpz_mat(A.shape[0], A.shape[1], [int(x) for x in A.ravel()])


def mode_product(T, A, axis):
    """T integer object tensor, A integer matrix (r x T.shape[axis])."""
    Tm = np.moveaxis(T, axis, 0)
    shp = Tm.shape
    R = fz(A) * fz(Tm.reshape(shp[0], -1))
    R = np.array([int(x) for x in R.entries()], dtype=object).reshape((A.shape[0],) + shp[1:])
    return np.moveaxis(R, 0, axis)


def psd_int(Zint):
    """Zint: integer symmetric matrix (numpy int64 or object).  True iff symmetric PSD."""
    Z = np.asarray(Zint, dtype=object)
    n = Z.shape[0]
    M = flint.fmpz_mat(n, n, [int(x) for x in Z.ravel()])
    if M != M.transpose():
        return False
    cp = M.charpoly()
    co = [int(cp[i]) for i in range(n + 1)]
    return all(((-1) ** kk) * co[n - kk] >= 0 for kk in range(n + 1))


def family_group(f):
    L = FAMILY_LETTERS[f]
    return [g for g in PERMS if all(L[g[i]] == L[i] for i in range(4))]


def gram_pinv(n):
    """Exact Moore-Penrose inverse of the 24 x 24 Gram matrix G[p, q] = Tr(V_p^* V_q) on (C^n)^{x4}."""
    ops = [perm_op(n, p) for p in PERMS]
    Gz = flint.fmpz_mat(24, 24)
    for i, p in enumerate(PERMS):
        for j, q in enumerate(PERMS):
            # Tr(V_p^T V_q) = number of matrix positions where both permutation matrices have a 1
            Gz[i, j] = sum(1 for key in ops[j] if key in ops[i])
    # kernel basis -> orthogonal projector P onto ker G; G^+ = (G + P)^{-1} - P
    Kb, nk = Gz.nullspace()
    rank = 24 - nk
    G = flint.fmpq_mat(Gz)
    if nk:
        N = flint.fmpq_mat(24, nk, [Kb[i, j] for i in range(24) for j in range(nk)])
        assert Gz * flint.fmpz_mat(24, nk, [Kb[i, j] for i in range(24) for j in range(nk)]) == flint.fmpz_mat(24, nk)
        P = N * (N.transpose() * N).inv() * N.transpose()
    else:
        P = flint.fmpq_mat(24, 24)
    Gp = (G + P).inv() - P
    assert G * Gp * G == G and Gp * G * Gp == Gp
    assert (G * Gp).transpose() == G * Gp and (Gp * G).transpose() == Gp * G
    norm = max(sum(abs(Fraction(int(Gp[i, j].p), int(Gp[i, j].q))) for j in range(24)) for i in range(24))
    return rank, norm



# ------------------------------------------------------------ site-permutation classes (multisets) and orbits
class Multisets:
    """Multisets of j letters from 24 (sorted tuples) for j = 0..k, and the insertion maps M -> M + {w}."""

    def __init__(self, k):
        self.k = k
        self.levels = [list(itertools.combinations_with_replacement(range(24), j)) for j in range(k + 1)]
        self.index = [{m: i for i, m in enumerate(lv)} for lv in self.levels]
        self.scatter = []
        for j in range(k):
            nxt = self.index[j + 1]
            tgt = np.array([nxt[tuple(sorted(m + (w,)))] for m in self.levels[j] for w in range(24)], dtype=np.int64)
            n_src = len(self.levels[j]) * 24
            self.scatter.append(sps.csr_matrix((np.ones(n_src), (tgt, np.arange(n_src))),
                                               shape=(len(self.levels[j + 1]), n_src)))
            if j == k - 1:
                self.tgt_last = tgt
        self.mult = np.array([math.factorial(k) // math.prod(math.factorial(m.count(c)) for c in set(m))
                              for m in self.levels[k]], dtype=object)

    @property
    def npoints(self):
        return len(self.levels[self.k]) * 24


def point_orbits(MS, f):
    """Orbit id of every point (M, a) (index M_idx * 24 + a) under G_f x G_f (letterwise g w h) and inversion."""
    k = MS.k
    top = MS.levels[k]
    idx = MS.index[k]
    mul = [[IDX[compose(p, q)] for q in PERMS] for p in PERMS]
    inv = [IDX[inverse(p)] for p in PERMS]
    maps = []

    def build(fn):
        mm = np.array([idx[tuple(sorted(fn(w) for w in m))] for m in top], dtype=np.int64)
        aa = np.array([fn(a) for a in range(24)], dtype=np.int64)
        return (mm[:, None] * 24 + aa[None, :]).reshape(-1)
    for g in family_group(f):
        gi = IDX[g]
        maps.append(build(lambda w, gi=gi: mul[gi][w]))
        maps.append(build(lambda w, gi=gi: mul[w][gi]))
    maps.append(build(lambda w: inv[w]))
    n = MS.npoints
    lab = np.arange(n, dtype=np.int64)
    while True:
        old = lab.copy()
        for m in maps:                       # the generator set is closed under inverses
            np.minimum(lab, lab[m], out=lab)
        lab = lab[lab]
        if np.array_equal(lab, old):
            break
    uniq, oid = np.unique(lab, return_inverse=True)
    return oid.reshape(-1).astype(np.int64), len(uniq)


def ms_contract(X, As, Aa, MS, mode, p=None):
    """Class sums of ((x)_l A_l (x) Aa) X for a module tensor X of shape (q_0, .., q_{k-1}, q_a): returns a float
    vector over points (M, a).  mode 'mod' (residues mod p), 'abs' / 'float' (no reduction)."""
    k = MS.k
    V = np.asarray(X, dtype=np.float64).reshape(1, -1)
    for j in range(k):
        q = As[j].shape[1]
        n = V.shape[0]
        rest = V.shape[1] // q
        Vt = V.reshape(n, q, rest).transpose(1, 0, 2).reshape(q, n * rest)
        U = As[j] @ Vt                                        # (24, n * rest)
        if mode == 'mod':
            np.fmod(U, p, out=U)
        U = U.reshape(24, n, rest).transpose(1, 0, 2).reshape(n * 24, rest)
        V = MS.scatter[j] @ U                                 # (n_{j+1}, rest)
        if mode == 'mod':
            np.fmod(V, p, out=V)
    out = V @ Aa.T                                            # (n_k, 24)
    if mode == 'mod':
        np.fmod(out, p, out=out)
    return out.reshape(-1)


def ms_contract_exact(X, Es, Ea, MS):
    """Exact (Python int) class sums of ((x)_l Es (x) Ea) X, identical integer map Es (24 x q) on every site."""
    k = MS.k
    V = np.asarray(X, dtype=object).reshape(1, -1)
    E = flint.fmpz_mat(Es.shape[0], Es.shape[1], [int(x) for x in np.asarray(Es, dtype=object).ravel()])
    for j in range(k):
        q = Es.shape[1]
        n = V.shape[0]
        rest = V.shape[1] // q
        Vt = V.reshape(n, q, rest).transpose(1, 0, 2).reshape(q, n * rest)
        U = E * flint.fmpz_mat(q, n * rest, [int(x) for x in Vt.ravel()])
        U = np.array([int(x) for x in U.entries()], dtype=object).reshape(24, n, rest)
        U = U.transpose(1, 0, 2).reshape(n * 24, rest)
        coo = MS.scatter[j].tocoo()
        order = np.argsort(coo.row, kind='stable')
        rows, cols = coo.row[order], coo.col[order]
        starts = np.flatnonzero(np.r_[True, rows[1:] != rows[:-1]])
        newV = np.zeros((MS.scatter[j].shape[0], rest), dtype=object)
        summed = np.add.reduceat(U[cols], starts, axis=0)
        newV[rows[starts]] = summed
        V = newV
    Ea_m = flint.fmpz_mat(Ea.shape[1], Ea.shape[0], [int(x) for x in np.asarray(Ea, dtype=object).T.ravel()])
    out = flint.fmpz_mat(V.shape[0], V.shape[1], [int(x) for x in V.ravel()]) * Ea_m
    return np.array([int(x) for x in out.entries()], dtype=object)


def orbit_sums_exact(oid, norb, vals):
    flat = np.asarray(vals, dtype=object).ravel()
    order = np.argsort(oid, kind='stable')
    so = oid[order]
    starts = np.flatnonzero(np.r_[True, so[1:] != so[:-1]])
    sums = np.add.reduceat(flat[order], starts)
    out = [0] * norb
    for i, v in zip(so[starts], sums):
        out[int(i)] = int(v)
    return out


# ------------------------------------------------------------ multiplier part (parallel)
GL = {}


def modp_array(arr, p):
    a = np.asarray(arr)
    if a.dtype == object:
        return np.array([int(x) % p for x in a.ravel()], dtype=np.float64).reshape(a.shape)
    return np.mod(a, p).astype(np.float64)


def scaled_abs(arr):
    """(F, e) with F a float array, F >= |arr| / 2^e entrywise (every entry of F an exact float)."""
    a = np.asarray(arr)
    if a.dtype != object and (a.size == 0 or int(np.abs(a).max()) < (1 << 53)):
        return np.abs(a).astype(np.float64), 0
    vals = [abs(int(x)) for x in a.ravel()]
    e = max(0, max(vals, default=0).bit_length() - 52)
    if e == 0:
        return np.array(vals, dtype=np.float64).reshape(a.shape), 0
    return np.array([(x >> e) + 1 for x in vals], dtype=np.float64).reshape(a.shape), e


def local_A(key):
    """A[(module key, rule)] : exact integer matrix 24 x dim^2, row p = J^T entry(V_p) J (flattened)."""
    if key not in GL['A']:
        mkey, (kpos, lpos) = key
        J = GL['J'][mkey]
        nn = int(mkey.split('|')[0])
        GL['A'][key] = np.array([sandwich(J, entry_op(nn, p, kpos, lpos)).ravel() for p in PERMS], dtype=object)
    return GL['A'][key]


def block_items(b):
    """(r, s, family, rule) for every row pair of a block, and the module tensor layout."""
    rows = [parse_pattern(u) for u in b['rows']]
    return [(r, s) + entry_rule(rows[r], rows[s]) for r in range(len(rows)) for s in range(len(rows))]


def module_tensor(T, dims, k):
    nl = k + 1
    T = T.reshape(dims + dims)
    order = []
    for i in range(nl):
        order += [i, nl + i]
    return np.ascontiguousarray(T.transpose(order)).reshape([x * x for x in dims])


def block_task(task):
    """mode 'mod' (residues mod p) or 'float': {family: class sums over points} for the blocks in the task."""
    mode, p, bidx = task
    cert = GL['cert']
    k = cert['k']
    MS = GL['MS']
    acc = {}
    Acache = {}
    for bi in bidx:
        b = cert['blocks'][bi]
        mods = list(b['modules'])
        dims = [GL['J'][m].shape[1] for m in mods]
        n = int(np.prod(dims))
        if mode == 'mod':
            W, Z, mu = modp_array(b['W'], p), modp_array(b['Zint'], p), float(GL['mult'][bi] % p)
        else:
            W, Z, mu = np.asarray(b['W'], dtype=np.float64), np.asarray(b['Zint'], dtype=np.float64), float(GL['mult'][bi])
        WZ = W @ Z
        if mode == 'mod':
            np.fmod(WZ, p, out=WZ)
        for r, s, f, kpos, lpos in block_items(b):
            T = WZ[r * n:(r + 1) * n] @ W[s * n:(s + 1) * n].T
            if mode == 'mod':
                np.fmod(T, p, out=T)
            X = module_tensor(T, dims, k)
            As = []
            for l in range(k + 1):
                ck = (mods[l], (kpos, lpos))
                if ck not in Acache:
                    Aex = local_A(ck)
                    Acache[ck] = modp_array(Aex, p) if mode == 'mod' else np.asarray(Aex, dtype=np.float64)
                As.append(Acache[ck])
            v = ms_contract(X, As[:k], As[k], MS, mode, p)
            if mu != 1.0:
                v = v * mu
                if mode == 'mod':
                    np.fmod(v, p, out=v)
            acc[f] = acc[f] + v if f in acc else v
    out = {}
    for f, a in acc.items():
        if mode == 'mod':
            a = np.fmod(a, p)
        oid, norb = GL['orb'][f]
        out[f] = np.bincount(oid, weights=a, minlength=norb)
    return out


def bound_task(bidx):
    """Rigorous integer bound on sum_b max_o |Dblk * orbit sum of <B_b, M_b(V_w)>| over the blocks in bidx: the
    same contraction with entrywise absolute values (scaled exact floats; all terms nonnegative, so the float
    result is within relative 1e-12 of the exact one and the factor 1 + 1e-9 covers rounding)."""
    cert = GL['cert']
    k = cert['k']
    MS = GL['MS']
    total = 0
    for bi in bidx:
        b = cert['blocks'][bi]
        mods = list(b['modules'])
        dims = [GL['J'][m].shape[1] for m in mods]
        n = int(np.prod(dims))
        W, eW = scaled_abs(b['W'])
        Z, eZ = scaled_abs(b['Zint'])
        WZ = W @ Z
        acc = {}
        for r, s, f, kpos, lpos in block_items(b):
            X = module_tensor(WZ[r * n:(r + 1) * n] @ W[s * n:(s + 1) * n].T, dims, k)
            As = []
            for l in range(k + 1):
                A, eA = scaled_abs(local_A((mods[l], (kpos, lpos))))
                assert eA == 0
                As.append(A)
            v = ms_contract(X, As[:k], As[k], MS, 'abs')
            acc[f] = acc[f] + v if f in acc else v
        m = 0.0
        for f, a in acc.items():
            oid, norb = GL['orb'][f]
            m = max(m, float(np.bincount(oid, weights=a, minlength=norb).max()))
        total += (math.ceil(m * (1 + 1e-9)) + 1) * GL['mult'][bi] << (eZ + 2 * eW)
    return total


def psd_task(bi):
    return bi, psd_int(GL['cert']['blocks'][bi]['Zint'])


def small_primes_below(n, count):
    out = []
    x = n - 1
    while len(out) < count:
        if x > 2 and all(x % q for q in range(2, int(math.isqrt(x)) + 1)):
            out.append(x)
        x -= 1
    return out


def load_cert(path):
    if path.endswith('.xz'):
        return pickle.load(lzma.open(path, 'rb'))
    return pickle.load(open(path, 'rb'))


def setup(cert, procs, log):
    k = cert['k']
    fams = set()
    for b in cert['blocks']:
        for _, _, f, _, _ in block_items(b):
            fams.add(f)
    for g in cert['eq_groups'].values():
        for part in g['parts']:
            fams.add(part['family'])
    fams |= {'31', '22', '13'}
    fams = sorted(fams)
    MS = Multisets(k)
    orb = {f: point_orbits(MS, f) for f in fams}
    log('points %d; orbits: %s' % (MS.npoints, {f: orb[f][1] for f in fams}))
    J = {key: np.array(Jm, dtype=object) for key, Jm in cert['modules'].items()}
    dens = [int(b['zden']) * int(b.get('Wden', 1)) ** 2 for b in cert['blocks']]
    Dblk = 1
    for x in dens:
        Dblk = Dblk * x // math.gcd(Dblk, x)
    GL.update(cert=cert, orb=orb, J=J, A={}, MS=MS, mult=[Dblk // x for x in dens])
    return fams, orb, Dblk


def block_chunks(chunk=8):
    nb = len(GL['cert']['blocks'])
    sizes = [np.asarray(b['Zint']).shape[0] ** 2 * len(b['rows']) ** 2 for b in GL['cert']['blocks']]
    order = sorted(range(nb), key=lambda i: -sizes[i])
    nt = max(1, nb // chunk)
    return [order[i::nt] for i in range(nt)]


def run_blocks(mode, p, procs, chunk=8):
    tasks = [(mode, p, bidx) for bidx in block_chunks(chunk)]
    tot = {}
    with mp.get_context('fork').Pool(procs) as pool:
        for res in pool.imap_unordered(block_task, tasks):
            for f, v in res.items():
                if mode == 'mod':
                    v = np.mod(np.rint(v).astype(np.int64), p)
                    tot[f] = np.mod(tot[f] + v, p) if f in tot else v
                else:
                    tot[f] = tot[f] + v if f in tot else v
    return tot


def exact_parts(cert, fams, orb, log):
    """Exact orbit sums of the objective (den b^k L), the trace tau_31 (den L) and lambda.E (Fractions)."""
    k, d = cert['k'], cert['d']
    MS = GL['MS']
    ta, tb = (int(x) for x in cert['t'].split('/'))
    swap = (3, 1, 2, 0)
    zs = [tb * trace(perm_op(d, p)) - ta * trace(perm_op(d, compose(swap, p))) for p in PERMS]
    za = [trace(perm_op(2, compose(swap, p))) for p in PERMS]
    ts = [trace(perm_op(d, p)) for p in PERMS]
    tra = [trace(perm_op(2, p)) for p in PERMS]

    def product_values(vs, va):
        """value at (M, a) = sum over the words of the class = mult(M) prod_{w in M} vs[w] * va[a]."""
        top = MS.levels[k]
        site = [MS.mult[i] * math.prod(vs[w] for w in m) for i, m in enumerate(top)]
        return np.array([sv * va[a] for sv in site for a in range(24)], dtype=object)
    obj = orbit_sums_exact(*orb['31'], product_values(zs, za))
    trs = orbit_sums_exact(*orb['31'], product_values(ts, tra))
    log('objective and trace orbit sums done')
    eqmods = {key: np.array(Jm, dtype=object) for key, Jm in cert['eq_modules'].items()}

    def eq_local1(n, slot, order, kind, mkey):
        J = eqmods[mkey]
        cols = []
        for p in PERMS:
            if kind == 'del':
                fac, q = partial_trace_replica(n, p, slot, order)
                M = fac * sandwich(J, perm3_op(n, q))
            else:                                   # 'stiefel_aux': 2 V_p - I_slot (x) Tr_slot V_p
                fac, q = partial_trace_replica(n, p, slot, tuple(i for i in range(4) if i != slot))
                nat = tuple(i for i in range(4) if i != slot)
                e = [None] * 4
                e[slot] = slot
                for i_new, i_old in enumerate(nat):
                    e[i_old] = nat[q[i_new]]
                M = 2 * sandwich(J, perm_op(n, p)) - fac * sandwich(J, perm_op(n, tuple(e)))
            cols.append(M.ravel())
        return np.array(cols, dtype=object).T

    def eq_local(n, slot, order, kind, mkeys):
        return np.vstack([eq_local1(n, slot, tuple(order), kind, mk) for mk in mkeys])

    eqs = {f: [Fraction(0)] * orb[f][1] for f in fams}
    cache = {}
    for gname, ginfo in sorted(cert['eq_groups'].items()):
        Lt = np.array(ginfo['lam_int'], dtype=object)
        lden = int(ginfo['lam_den'])
        if not any(int(x) for x in Lt.ravel()):
            continue
        for part in ginfo['parts']:
            fam, sign = part['family'], part['sign']
            specs = [tuple((s[0], s[1], tuple(s[2]), s[3], tuple(s[4]))) for s in part['local']]
            assert all(sp == specs[0] for sp in specs[:k]), 'site factors of an equality part must agree'
            for sp in (specs[0], specs[k]):
                if sp not in cache:
                    cache[sp] = eq_local(*sp)
            Es, Ea = cache[specs[0]].T, cache[specs[k]].T            # (24 x out)
            assert Lt.shape == tuple([Es.shape[1]] * k + [Ea.shape[1]]), (gname, Lt.shape)
            vals = ms_contract_exact(Lt, Es, Ea, MS)
            sums = orbit_sums_exact(*orb[fam], vals)
            acc = eqs[fam]
            for o, v in enumerate(sums):
                if v:
                    acc[o] += Fraction(sign * v, lden)
        log('equality group %s done' % gname)
    return obj, trs, eqs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cert')
    ap.add_argument('--procs', type=int, default=8)
    ap.add_argument('--skip-psd', action='store_true', help='residual only (construction aid; never PASS)')
    ap.add_argument('--dump', help='write the exact residual orbit sums {family: [Fraction]} to this pickle')
    args = ap.parse_args()
    t0 = time.time()
    log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
    cert = load_cert(args.cert)
    k, d = cert['k'], cert['d']
    L = (2 * d ** k) ** 4
    ta, tb = (int(x) for x in cert['t'].split('/'))
    nu = Fraction(cert['nu'])
    log('k=%d d=%d t=%d/%d nu=%s (%.6e); %d multiplier blocks, %d equality groups'
        % (k, d, ta, tb, cert['nu'], float(nu), len(cert['blocks']), len(cert['eq_groups'])))
    assert 0 <= ta and 0 < tb      # nu may have any sign; the final check nu >= L K sum >= 0 decides
    fams, orb, Dblk = setup(cert, args.procs, log)
    nbad = 0
    if args.skip_psd:
        nbad = -1
        log('PSD check SKIPPED (residual-only run)')
    else:
        with mp.get_context('fork').Pool(args.procs) as pool:
            for bi, ok in pool.imap_unordered(psd_task, range(len(cert['blocks'])), chunksize=8):
                if not ok:
                    nbad += 1
                    log('block %d NOT PSD' % bi)
        log('PSD check: %d failures over %d blocks' % (nbad, len(cert['blocks'])))
    with mp.get_context('fork').Pool(args.procs) as pool:
        bound = sum(pool.imap_unordered(bound_task, block_chunks(4)))
    nbits = (2 * bound + 1).bit_length()
    primes = []
    while True:
        primes = small_primes_below(PMAX, len(primes) + 1)
        if math.prod(primes) > 2 * bound + 1:
            break
    log('multiplier part: |orbit sums| < 2^%d -> %d primes; Dblk has %d bits'
        % (nbits - 1, len(primes), Dblk.bit_length()))
    res = []
    for p in primes:
        res.append(run_blocks('mod', p, args.procs))
        log('prime %d done' % p)
    M = math.prod(primes)
    blk = {}
    for f in fams:
        vals = [0] * orb[f][1]
        if f in res[0]:
            for p, r in zip(primes, res):
                Mi = M // p
                inv = pow(Mi, -1, p)
                rv = r[f]
                for o in range(orb[f][1]):
                    vals[o] += int(rv[o]) * inv * Mi
            vals = [v % M for v in vals]
            vals = [v - M if v > M // 2 else v for v in vals]
        blk[f] = vals
    obj, trs, eqs = exact_parts(cert, fams, orb, log)
    norms = {}
    dump = {}
    for f in fams:
        tot = Fraction(0)
        dump[f] = []
        for o in range(orb[f][1]):
            R = Fraction(-blk[f][o], Dblk) - eqs[f][o]
            if f == '31':
                R += Fraction(obj[o], tb ** k * L) - nu * Fraction(trs[o], L)
            tot += abs(R)
            dump[f].append(R)
        norms[f] = tot
        log('family %s: %d orbits, ||R_f||_1 = %.6e' % (f, orb[f][1], float(tot)))
    rs, ns = gram_pinv(d)
    ra, na = gram_pinv(2)
    K = ns ** k * na
    S = sum(norms.values(), Fraction(0))
    need = L * K * S
    log('Gram ranks: n=%d -> %d, n=2 -> %d; ||G_s^+||_inf = %s, ||G_a^+||_inf = %s; K = %.6e, L = %d'
        % (d, rs, ra, ns, na, float(K), L))
    log('sum_f ||R_f||_1 = %.6e;  L K sum = %.6e  vs  nu = %.6e  (ratio nu / (L K sum) = %.3e)'
        % (float(S), float(need), float(nu), float(nu / need) if need else float('inf')))
    if args.dump:
        pickle.dump(dump, open(args.dump, 'wb'), protocol=4)
        log('residual orbit sums written to %s' % args.dump)
    ok = nbad == 0 and nu >= need
    status = 'SLACK_CERTIFICATE_PASS' if ok else 'FAIL'
    log(status)
    return status


if __name__ == '__main__':
    main()
