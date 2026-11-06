"""Exact block types, symmetry subspaces and exact blocks of exact physical points."""
from __future__ import annotations

import itertools
import math
from fractions import Fraction

import numpy as np
import flint
import sympy as sp

from exact import (ExactLocal, P4, I4, P3, TAU, P0, compose, inverse, perms, mode_product, fz, from_fz)

FAMILY_GROUP = {
    '31': [p + (3,) for p in P3],
    '13': [p + (3,) for p in P3],
    '22': [(0, 1, 2, 3), (1, 0, 2, 3), (0, 1, 3, 2), (1, 0, 3, 2)],
}
FAMILY_CUTS = {
    '31': [(), (3,), (0,), (0, 1)],
    '13': [(), (3,), (0,), (0, 1)],
    '22': [(), (0,), (2,), (0, 1), (0, 2)],
}
FAMILIES = ('31', '22', '13')
# gram2: coupled Gram of word class (1,-1) on cut (2,3) (see relax_ext.py)
CUT23 = (2, 3)
PD2 = (1, 2, 3, 0)
QB2 = (1, 3, 0, 2)
H01 = [(0, 1, 2, 3), (1, 0, 2, 3)]
H23 = [(0, 1, 2, 3), (0, 1, 3, 2)]
WM2 = {'31': lambda p: p,
       '22': lambda p: compose(p, QB2),
       '13': lambda p: compose(compose(PD2, p), inverse(PD2))}


def qmat(rows):
    """list of lists of Fractions/ints -> flint fmpq_mat"""
    r = len(rows)
    c = len(rows[0]) if r else 0
    return flint.fmpq_mat(r, c, [flint.fmpq(int(Fraction(x).numerator), int(Fraction(x).denominator)) for row in rows for x in row])


def q_from_sympy(M):
    return flint.fmpq_mat(M.rows, M.cols, [flint.fmpq(int(sp.fraction(x)[0]), int(sp.fraction(x)[1])) for x in M])


def qkron(A, B):
    a, b = A.nrows(), B.nrows()
    ac, bc = A.ncols(), B.ncols()
    out = flint.fmpq_mat(a * b, ac * bc)
    for i in range(a):
        for j in range(ac):
            v = A[i, j]
            if v == 0:
                continue
            for k in range(b):
                for l in range(bc):
                    w = B[k, l]
                    if w != 0:
                        out[i * b + k, j * bc + l] = v * w
    return out


def qcolspace(M):
    """Rational basis (columns) of the column space of fmpq_mat M."""
    R, rank = M.transpose().rref()
    rows = [[R[i, j] for j in range(R.ncols())] for i in range(rank)]
    if not rows:
        return flint.fmpq_mat(M.nrows(), 0)
    return flint.fmpq_mat(rank, M.nrows(), [x for row in rows for x in row]).transpose()


def qnullspace(M):
    """Rational basis (columns) of the right null space of fmpq_mat M (r x n)."""
    n = M.ncols()
    if M.nrows() == 0:
        return flint.fmpq_mat(n, n, [1 if i == j else 0 for i in range(n) for j in range(n)])
    R, rank = M.rref()
    piv = []
    for i in range(rank):
        for j in range(n):
            if R[i, j] != 0:
                piv.append(j)
                break
    free = [j for j in range(n) if j not in piv]
    B = flint.fmpq_mat(n, len(free))
    for c, fj in enumerate(free):
        B[fj, c] = 1
        for i, pj in enumerate(piv):
            B[pj, c] = -R[i, fj]
    return B


def primitive_columns(B):
    """Scale each column of an fmpq_mat to a primitive integer vector."""
    n, r = B.nrows(), B.ncols()
    out = flint.fmpq_mat(n, r)
    for c in range(r):
        col = [B[i, c] for i in range(n)]
        den = 1
        for x in col:
            den = den * int(x.q) // math.gcd(den, int(x.q))
        ints = [int(x * den) for x in col]
        g = 0
        for v in ints:
            g = math.gcd(g, v)
        g = g or 1
        for i in range(n):
            out[i, c] = ints[i] // g
    return out


def site_irrep_projectors(stab, k):
    """Rational orthogonal first-row projectors (as lists of (coef, sigma)) for the irreps of the site
    stabiliser `stab` (a subgroup of S_k given as tuples).  Supports trivial, S_2, S_3 (k=3)."""
    n = len(stab)
    if n == 1:
        return [('triv', [(Fraction(1), stab[0])])]
    if n == 2:
        e = tuple(range(k))
        s = [g for g in stab if g != e][0]
        return [('plus', [(Fraction(1, 2), e), (Fraction(1, 2), s)]),
                ('minus', [(Fraction(1, 2), e), (Fraction(-1, 2), s)])]
    if n == 6 and k == 3:
        def sign(p):
            return (-1) ** sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3))
        triv = [(Fraction(1, 6), g) for g in stab]
        sgn = [(Fraction(sign(g), 6), g) for g in stab]
        std = []
        for g in stab:
            if g == (0, 1, 2) or g == (1, 0, 2):
                std.append((Fraction(1, 3), g))
            else:
                std.append((Fraction(-1, 6), g))
        return [('triv', triv), ('sign', sgn), ('std', std)]
    raise NotImplementedError(stab)


def _ga_mul(a, b):
    out = {}
    for s1, c1 in a.items():
        for s2, c2 in b.items():
            key = tuple(s1[s2[i]] for i in range(len(s2)))
            out[key] = out.get(key, Fraction(0)) + c1 * c2
    return {key: v for key, v in out.items() if v != 0}


def _partitions(n, maxpart=None):
    maxpart = n if maxpart is None else maxpart
    if n == 0:
        yield ()
        return
    for f in range(min(n, maxpart), 0, -1):
        for rest in _partitions(n - f, f):
            yield (f,) + rest


def site_irrep_projectors_jm(stab, k):
    """Rational orthogonal first-row projectors for every irreducible type of a Young subgroup `stab`
    of S_k (site permutations), via Jucys-Murphy idempotents of the row-reading standard tableaux.
    Returns [(name, [(coef, sigma), ...]), ...] (group-algebra elements of Q[stab])."""
    e = tuple(range(k))
    # orbits of stab on sites
    orbits, seen = [], set()
    for i in range(k):
        if i in seen:
            continue
        orb = sorted(set(g[i] for g in stab))
        orbits.append(orb)
        seen |= set(orb)
    per_orbit = []
    for orb in orbits:
        n = len(orb)
        opts = []
        for lam in _partitions(n):
            contents = []
            for r, rowlen in enumerate(lam):
                for col in range(rowlen):
                    contents.append(col - r)
            elem = {e: Fraction(1)}
            for j in range(1, n):
                Jj = {}
                for i in range(j):
                    t = list(e)
                    t[orb[i]], t[orb[j]] = t[orb[j]], t[orb[i]]
                    Jj[tuple(t)] = Jj.get(tuple(t), Fraction(0)) + 1
                cj = contents[j]
                for c in range(-j, j + 1):
                    if c == cj:
                        continue
                    fac = dict(Jj)
                    fac[e] = fac.get(e, Fraction(0)) - c
                    fac = {key: v / (cj - c) for key, v in fac.items()}
                    elem = _ga_mul(elem, fac)
            opts.append((''.join(map(str, lam)), elem))
        per_orbit.append(opts)
    out = []
    import itertools as _it
    for combo in _it.product(*per_orbit):
        name = '|'.join(c[0] for c in combo)
        elem = {e: Fraction(1)}
        for _, el in combo:
            elem = _ga_mul(elem, el)
        out.append((name, [(v, key) for key, v in elem.items()]))
    return out


def factor_perm_matrix(dims, s, k):
    """Permutation matrix (fmpq) of site factor permutation s on tensor space with factor dims."""
    n = int(np.prod(dims))
    idx = np.arange(n).reshape(dims)
    axes = list(range(k + 1))
    for i in range(k):
        axes[s[i]] = i
    tgt = np.transpose(idx, axes).ravel()
    M = flint.fmpq_mat(n, n)
    for J in range(n):
        M[J, int(tgt[J])] = 1
    return M


class ExactRelax:
    def __init__(self, k, d, drop=(), verbose=True, gram2=True):
        self.k, self.d = k, d
        self.verbose = verbose
        self.gram2 = gram2
        self.loc = {}
        for c in set(c for f in FAMILIES for c in FAMILY_CUTS[f]) | {(3,), CUT23}:
            self.loc['s', c] = ExactLocal(d, 4, c)
            self.loc['a', c] = ExactLocal(2, 4, c)
        self.siteperms = perms(k)
        self.drop = set(drop)
        self.build_types()

    def _log(self, s):
        if self.verbose:
            print(s, flush=True)

    def stab_group(self, f, cut):
        return [g for g in FAMILY_GROUP[f] if set(g[i] for i in cut) == set(cut)]

    def build_types(self):
        k = self.k
        self.types = []
        specs = [('src', f, cut) for f in FAMILIES for cut in FAMILY_CUTS[f]] + [('gram', None, (3,))]
        for kind, f, cut in specs:
            H = self.stab_group(f, cut) if kind == 'src' else [(0, 1, 2, 3), (1, 0, 2, 3)]
            ls, la = self.loc['s', cut], self.loc['a', cut]
            for st in itertools.combinations_with_replacement(range(len(ls.labels)), k):
                for ai in range(len(la.labels)):
                    dims = [ls.dims[i] for i in st] + [la.dims[ai]]
                    n = int(np.prod(dims))
                    # R = avg_g kron(pi(g)) (exact)
                    R = flint.fmpq_mat(n, n)
                    for g in H:
                        K = flint.fmpq_mat(1, 1, [1])
                        for i in st:
                            K = qkron(K, q_from_sympy(ls.pi[i][I4[g]]))
                        K = qkron(K, q_from_sympy(la.pi[ai][I4[g]]))
                        R = R + K
                    R = R / len(H)
                    stab = [s for s in self.siteperms if all(st[s[i]] == st[i] for i in range(k))]
                    projs = site_irrep_projectors(stab, k) if k <= 3 else site_irrep_projectors_jm(stab, k)
                    Pm = {s: factor_perm_matrix(dims, s, k) for s in stab}
                    for q, (name, terms) in enumerate(projs):
                        E = flint.fmpq_mat(n, n)
                        for coef, s in terms:
                            E = E + Pm[s] * flint.fmpq(coef.numerator, coef.denominator)
                        Vb = qcolspace(E * R.transpose())
                        if Vb.ncols() == 0:
                            continue
                        key = (kind, f, cut, st, ai, name)
                        if key in self.drop:
                            continue
                        self.types.append(dict(kind=kind, f=f, cut=cut, st=st, ai=ai, irrep=name,
                                               dims=dims, n=n, Vb=primitive_columns(Vb)))
        if self.gram2:
            self.build_gram2_types()
        self._log('exact block types: %d' % len(self.types))

    def _sym_R(self, H, st, ai, cut):
        ls, la = self.loc['s', cut], self.loc['a', cut]
        dims = [ls.dims[i] for i in st] + [la.dims[ai]]
        n = int(np.prod(dims))
        R = flint.fmpq_mat(n, n)
        for g in H:
            K = flint.fmpq_mat(1, 1, [1])
            for i in st:
                K = qkron(K, q_from_sympy(ls.pi[i][I4[g]]))
            K = qkron(K, q_from_sympy(la.pi[ai][I4[g]]))
            R = R + K
        return R / len(H), dims, n

    def build_gram2_types(self):
        k = self.k
        cut = CUT23
        ls, la = self.loc['s', cut], self.loc['a', cut]
        for st in itertools.combinations_with_replacement(range(len(ls.labels)), k):
            for ai in range(len(la.labels)):
                R1, dims, n = self._sym_R(H01, st, ai, cut)
                R2, _, _ = self._sym_R(H23, st, ai, cut)
                stab = [s for s in self.siteperms if all(st[s[i]] == st[i] for i in range(k))]
                projs = site_irrep_projectors(stab, k) if k <= 3 else site_irrep_projectors_jm(stab, k)
                Pm = {s: factor_perm_matrix(dims, s, k) for s in stab}
                for q, (name, terms) in enumerate(projs):
                    E = flint.fmpq_mat(n, n)
                    for coef, s in terms:
                        E = E + Pm[s] * flint.fmpq(coef.numerator, coef.denominator)
                    V1 = qcolspace(E * R1.transpose())
                    V2 = qcolspace(E * R2.transpose())
                    if V1.ncols() == 0 or V2.ncols() == 0:
                        continue
                    key = ('gram2', None, cut, st, ai, name)
                    if key in self.drop:
                        continue
                    self.types.append(dict(kind='gram2', f=None, cut=cut, st=st, ai=ai, irrep=name,
                                           dims=dims, n=n, Vb=primitive_columns(V1), Vb2=primitive_columns(V2)))

    # ---------- exact Fourier tensors of exact points ----------
    def fourier(self, x, keeps, cut, wordmap=None):
        """Apply per-mode FT_cut (columns restricted to keep sets, optionally composed with a word
        permutation map p -> wordmap(p)) to the scaled-integer tensor x."""
        out = x
        for l in range(self.k + 1):
            loc = self.loc['a' if l == self.k else 's', cut]
            cols = [wordmap(P4[p]) if wordmap else p for p in keeps[l]]
            A = loc.FT[:, [I4[c] if isinstance(c, tuple) else c for c in cols]]
            out = mode_product(out, A, l)
        return out

    def extract(self, F, t):
        ls, la = self.loc['s', t['cut']], self.loc['a', t['cut']]
        sl = tuple([ls.rows(i) for i in t['st']] + [la.rows(t['ai'])])
        Y = F[sl]
        shp = []
        for x in t['dims']:
            shp += [x, x]
        Y = Y.reshape(shp)
        k = self.k
        order = [2 * i for i in range(k + 1)] + [2 * i + 1 for i in range(k + 1)]
        n = t['n']
        return Y.transpose(order).reshape(n, n)

    def point_blocks(self, pts):
        """pts: dict family -> (xint, den, keeps).  Returns list (aligned with self.types) of exact
        compressed blocks Vb^T S Vb as fmpq_mat (common positive scaling per family irrelevant)."""
        Fcache = {}
        for f in FAMILIES:
            x, den, keeps = pts[f]
            for cut in FAMILY_CUTS[f]:
                Fcache[f, cut] = (self.fourier(x, keeps, cut), den)
        tauconj = lambda p: compose(compose(TAU, p), TAU)
        withp0 = lambda p: compose(p, P0)
        Fg = {}
        for f, wm in (('31', tauconj), ('22', withp0), ('13', tauconj)):
            x, den, keeps = pts[f]
            Fg[f] = (self.fourier(x, keeps, (3,), wm), den)
        Fg2 = {}
        if any(t['kind'] == 'gram2' for t in self.types):
            for f in FAMILIES:
                x, den, keeps = pts[f]
                Fg2[f] = (self.fourier(x, keeps, CUT23, WM2[f]), den)
        out = []
        for t in self.types:
            Vb = t['Vb']
            if t['kind'] == 'gram2':
                A = flint.fmpq_mat(fz(self.extract(Fg2['31'][0], t))) / Fg2['31'][1]
                B = flint.fmpq_mat(fz(self.extract(Fg2['22'][0], t))) / Fg2['22'][1]
                Dd = flint.fmpq_mat(fz(self.extract(Fg2['13'][0], t))) / Fg2['13'][1]
                n = t['n']
                Sq = flint.fmpq_mat(2 * n, 2 * n)
                for i in range(n):
                    for j in range(n):
                        Sq[i, j] = A[i, j]
                        Sq[i, n + j] = B[i, j]
                        Sq[n + i, j] = B[j, i]
                        Sq[n + i, n + j] = Dd[i, j]
                W = block_diag_pair(Vb, t['Vb2'])
                out.append(W.transpose() * Sq * W)
                continue
            if t['kind'] == 'src':
                F, den = Fcache[t['f'], t['cut']]
                S = self.extract(F, t)
                Sq = flint.fmpq_mat(fz(S)) / den
            else:
                A = flint.fmpq_mat(fz(self.extract(Fg['31'][0], t))) / Fg['31'][1]
                B = flint.fmpq_mat(fz(self.extract(Fg['22'][0], t))) / Fg['22'][1]
                Dd = flint.fmpq_mat(fz(self.extract(Fg['13'][0], t))) / Fg['13'][1]
                n = t['n']
                Sq = flint.fmpq_mat(2 * n, 2 * n)
                for i in range(n):
                    for j in range(n):
                        Sq[i, j] = A[i, j]
                        Sq[i, n + j] = B[i, j]
                        Sq[n + i, j] = B[j, i]
                        Sq[n + i, n + j] = Dd[i, j]
                Vb = block_diag2(Vb)
            out.append(Vb.transpose() * Sq * Vb)
        return out


def block_diag2(V):
    n, r = V.nrows(), V.ncols()
    W = flint.fmpq_mat(2 * n, 2 * r)
    for i in range(n):
        for j in range(r):
            W[i, j] = V[i, j]
            W[n + i, r + j] = V[i, j]
    return W


def block_diag_pair(V1, V2):
    n1, r1 = V1.nrows(), V1.ncols()
    n2, r2 = V2.nrows(), V2.ncols()
    W = flint.fmpq_mat(n1 + n2, r1 + r2)
    for i in range(n1):
        for j in range(r1):
            W[i, j] = V1[i, j]
    for i in range(n2):
        for j in range(r2):
            W[n1 + i, r1 + j] = V2[i, j]
    return W
