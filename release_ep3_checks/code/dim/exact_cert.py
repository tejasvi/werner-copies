"""Exact certificate assembly: rounding of the numeric multipliers, exact identity residual on all word
orbits, exact correction (equality multipliers + Gram entries) and exact PSD checks.

Identity (per family f, on every orbit O of words under G_f x G_f x site perms x inversion):
    sum_{w in O} [ c_f[w] - sum_t T_t^f[w] - T_lambda^f[w] ] = 0
with T_t^f[w] = <B_t, J^T P_w^Gamma J> (B_t = W_t Z_t W_t^T in J coordinates).
"""
from __future__ import annotations

import itertools
import math
import pickle
import sys
import time
from fractions import Fraction

import numpy as np
import flint

sys.path.insert(0, '<ROOT>/dim')
from exact import ExactLocal, P4, I4, P3, I3, TAU, P0, SWAP03, compose, inverse, ncycles, perms, fz, from_fz
from exact_blocks import FAMILY_GROUP, FAMILY_CUTS, FAMILIES, CUT23, WM2

INV4 = [I4[inverse(p)] for p in P4]
MUL4 = [[I4[compose(p, q)] for q in P4] for p in P4]


# ---------------------------------------------------------------- orbits
def word_orbits(k, f):
    """orbit id for every word (array over (24,)*(k+1)) and the number of orbits."""
    nl = k + 1
    gidx = [I4[g] for g in FAMILY_GROUP[f]]
    sp = perms(k)
    oid = -np.ones((24,) * nl, dtype=np.int64)
    n = 0
    for w in itertools.product(range(24), repeat=nl):
        if oid[w] >= 0:
            continue
        stack = [w]
        oid[w] = n
        while stack:
            u = stack.pop()
            imgs = []
            for g in gidx:
                for h in gidx:
                    imgs.append(tuple(MUL4[MUL4[g][x]][h] for x in u))
            imgs.append(tuple(INV4[x] for x in u))
            for s in sp:
                v = [None] * nl
                for i in range(k):
                    v[s[i]] = u[i]
                v[k] = u[k]
                imgs.append(tuple(v))
            for v in imgs:
                if oid[v] < 0:
                    oid[v] = n
                    stack.append(v)
        n += 1
    return oid, n


def orbit_sums(T, oid, n):
    """Exact orbit sums of an integer object table T (same shape as oid)."""
    flat = T.ravel()
    o = oid.ravel()
    order = np.argsort(o, kind='stable')
    so = o[order]
    starts = np.flatnonzero(np.r_[True, so[1:] != so[:-1]])
    vals = np.add.reduceat(flat[order], starts)
    out = np.zeros(n, dtype=object)
    out[so[starts]] = vals
    return out


# ---------------------------------------------------------------- tables
class Tables:
    def __init__(self, k, d):
        self.k, self.d = k, d
        self.loc = {}
        for c in set(c for f in FAMILIES for c in FAMILY_CUTS[f]) | {(3,), CUT23}:
            self.loc['s', c] = ExactLocal(d, 4, c)
            self.loc['a', c] = ExactLocal(2, 4, c)
        tauconj = [I4[compose(compose(TAU, p), TAU)] for p in P4]
        withp0 = [I4[compose(p, P0)] for p in P4]
        self.colmap = {'A': tauconj, 'B': withp0, None: list(range(24)),
                       'A2': [I4[WM2['31'](p)] for p in P4], 'B2': [I4[WM2['22'](p)] for p in P4],
                       'D2': [I4[WM2['13'](p)] for p in P4]}
        self.L = (2 * d ** k) ** 4

    def FT(self, typ, cut, li, mapkey=None):
        loc = self.loc[typ, cut]
        M = loc.FT[loc.rows(li), :]
        return M[:, self.colmap[mapkey]]

    def block_tensor(self, B, t):
        """n x n (or object) matrix in J coordinates -> tensor (d0^2, ..., dk^2) in Fourier layout order."""
        dims = t['dims']
        k = self.k
        T = np.asarray(B, dtype=object).reshape(dims + dims)
        order = []
        for i in range(k + 1):
            order += [i, k + 1 + i]
        return T.transpose(order).reshape([x * x for x in dims])

    def table_from_block(self, Bt, t, mapkey=None):
        """Word table (24,)*(k+1) of <B, J^T P_w^Gamma J> for an integer block tensor Bt."""
        out = Bt
        for l in range(self.k + 1):
            typ = 'a' if l == self.k else 's'
            li = t['ai'] if l == self.k else t['st'][l]
            A = self.FT(typ, t['cut'], li, mapkey).T          # 24 x d^2
            out = mode_product_int(out, A, l)
        return out

    def objective_table(self):
        d, k = self.d, self.k
        zs = [Fraction(d ** ncycles(p)) - Fraction(d ** ncycles(compose(SWAP03, p)), 2) for p in P4]
        za = [2 ** ncycles(compose(SWAP03, p)) for p in P4]
        den = 2 ** k * self.L
        zsi = [int(z * 2) for z in zs]
        T = np.ones((1,) * 0, dtype=object)
        T = np.array(1, dtype=object)
        for l in range(k):
            T = np.multiply.outer(T, np.array(zsi, dtype=object))
        T = np.multiply.outer(T, np.array(za, dtype=object))
        return T, den


def mode_product_int(T, A, axis):
    Tm = np.moveaxis(T, axis, 0)
    shp = Tm.shape
    Tm2 = Tm.reshape(shp[0], -1)
    R = fz(A) * fz(Tm2)
    R = from_fz(R).reshape((A.shape[0],) + shp[1:])
    return np.moveaxis(R, 0, axis)


# ---------------------------------------------------------------- equality local maps
def delete_matrix(n, slot, order=None):
    if order is None:
        order = tuple(i for i in range(4) if i != slot)
    M = np.zeros((6, 24), dtype=object)
    for a, p in enumerate(P4):
        out = tuple(order.index(p[slot] if p[i] == slot else p[i]) for i in order)
        M[I3[out], a] += n if p[slot] == slot else 1
    return M


def embed_matrix(slot):
    order = tuple(i for i in range(4) if i != slot)
    M = np.zeros((24, 6), dtype=object)
    for a, q in enumerate(P3):
        p = [None] * 4
        p[slot] = slot
        for i_new, i_old in enumerate(order):
            p[i_old] = order[q[i_new]]
        M[I4[tuple(p)], a] = 1
    return M


class Equalities:
    """Raw equality functionals as products of local maps (integer, with a factor-2 scaling on the
    Stiefel aux map).  Each equality group g has local maps (site map S_g (Ds x 24), aux map A_g),
    applied to family f with sign; row index = output coordinate tuple."""

    def __init__(self, k, d):
        self.k, self.d = k, d
        s3, a3 = ExactLocal(d, 3, ()), ExactLocal(2, 3, ())
        a4 = ExactLocal(2, 4, ())
        I24 = np.eye(24, dtype=object)
        self.groups = []
        for f, slot in (('31', 0), ('22', 0), ('13', 3)):
            S = s3.FT.dot(delete_matrix(d, slot))
            A = a4.FT.dot(2 * I24 - embed_matrix(slot).dot(delete_matrix(2, slot)))   # x2 scaled
            self.groups.append(dict(name='stiefel' + f, parts=[(f, S, A, 1)]))
        for (f1, s1, o1), (f2, s2, o2), name in [(('31', 2, (0, 1, 3)), ('22', 2, (0, 1, 3)), 'aab'),
                                                (('22', 1, (0, 2, 3)), ('13', 1, (3, 0, 2)), 'abb')]:
            p1 = (f1, s3.FT.dot(delete_matrix(d, s1, o1)), a3.FT.dot(delete_matrix(2, s1, o1)), 1)
            p2 = (f2, s3.FT.dot(delete_matrix(d, s2, o2)), a3.FT.dot(delete_matrix(2, s2, o2)), -1)
            self.groups.append(dict(name=name, parts=[p1, p2]))

    def row_tables(self, g, o):
        """For equality group g and output coordinate tuple o, the word tables per family."""
        out = {}
        for f, S, A, sign in self.groups[g]['parts']:
            T = np.array(sign, dtype=object)
            for l in range(self.k):
                T = np.multiply.outer(T, S[o[l]])
            T = np.multiply.outer(T, A[o[self.k]])
            out[f] = T
        return out

    def row_shapes(self, g):
        f, S, A, sign = self.groups[g]['parts'][0]
        return [S.shape[0]] * self.k + [A.shape[0]]


# ---------------------------------------------------------------- assembly
def frac_matrix(rows):
    return [[Fraction(x) for x in row] for row in rows]


def round_sym(Zf, den):
    """Round a float symmetric matrix to rationals with denominator den."""
    Z = (Zf + Zf.T) / 2
    return [[Fraction(int(round(Z[i, j] * den)), den) for j in range(Z.shape[1])] for i in range(Z.shape[0])]


def W_of(t, Nl):
    Vb = np.array(t['Vb'], dtype=object)
    N = np.array(Nl, dtype=object)
    if t['kind'] == 'gram':
        n, v = Vb.shape
        V2 = np.zeros((2 * n, 2 * v), dtype=object)
        V2[:n, :v] = Vb
        V2[n:, v:] = Vb
        Vb = V2
    elif t['kind'] == 'gram2':
        Vb2 = np.array(t['Vb2'], dtype=object)
        n, v1 = Vb.shape
        v2 = Vb2.shape[1]
        V2 = np.zeros((2 * n, v1 + v2), dtype=object)
        V2[:n, :v1] = Vb
        V2[n:, v1:] = Vb2
        Vb = V2
    return Vb.dot(N)


def block_B_int(W, Zint):
    """B = W Z W^T with integer Z (scaled) -> integer matrix."""
    return W.dot(np.asarray(Zint, dtype=object)).dot(W.T)


def family_tables(tabs, types, Ws, Zints, kfam_only=None, float_mode=False):
    """Sum of block word tables per family for multipliers Z (integer-scaled): returns dict f -> table."""
    k = tabs.k
    out = {f: None for f in FAMILIES}

    def add(f, T):
        out[f] = T if out[f] is None else out[f] + T

    # group types by (kind, f, cut): build combined Fourier-layout tensors
    groups = {}
    for i, t in enumerate(types):
        if Zints[i] is None:
            continue
        groups.setdefault((t['kind'], t['f'], t['cut']), []).append(i)
    for (kind, f, cut), ids in groups.items():
        ls, la = tabs.loc['s', cut], tabs.loc['a', cut]
        shape = [ls.D] * k + [la.D]
        if kind == 'src':
            comb = {None: np.zeros(shape, dtype=float if float_mode else object)}
            fams = [(f, None, None)]
        else:
            comb = {key: np.zeros(shape, dtype=float if float_mode else object) for key in ('11', '12', '22')}
        for i in ids:
            t = types[i]
            B = block_B_int(Ws[i], Zints[i]) if not float_mode else Ws[i] @ Zints[i] @ Ws[i].T
            sl = tuple([ls.rows(li) for li in t['st']] + [la.rows(t['ai'])])
            if kind == 'src':
                comb[None][sl] = comb[None][sl] + tabs.block_tensor(B, t)
            else:
                n = t['n']
                comb['11'][sl] = comb['11'][sl] + tabs.block_tensor(B[:n, :n], t)
                comb['12'][sl] = comb['12'][sl] + tabs.block_tensor(2 * B[:n, n:], t)
                comb['22'][sl] = comb['22'][sl] + tabs.block_tensor(B[n:, n:], t)
        if kind == 'src':
            items = [(f, comb[None], None)]
        elif kind == 'gram2':
            items = [('31', comb['11'], 'A2'), ('22', comb['12'], 'B2'), ('13', comb['22'], 'D2')]
        else:
            items = [('31', comb['11'], 'A'), ('22', comb['12'], 'B'), ('13', comb['22'], 'A')]
        for fam, C, mk in items:
            T = C
            for l in range(k + 1):
                typ = 'a' if l == k else 's'
                FTm = tabs.loc[typ, cut].FT[:, tabs.colmap[mk]]
                if float_mode:
                    T = np.moveaxis(np.tensordot(FTm.T.astype(float), T, axes=(1, l)), 0, l)
                else:
                    T = mode_product_int(T, FTm.T, l)
            add(fam, T)
    return out


def osum_float(T, oid, n):
    out = np.zeros(n)
    np.add.at(out, oid.ravel(), np.asarray(T, dtype=float).ravel())
    return out


def ldl_psd(Z):
    """Exact PSD test of a symmetric rational matrix (list of Fractions) via LDL^T with pivoting on
    the diagonal; returns (is_psd, min_pivot)."""
    n = len(Z)
    A = [[Fraction(x) for x in row] for row in Z]
    active = list(range(n))
    minpiv = None
    while active:
        # choose largest diagonal pivot
        p = max(active, key=lambda i: A[i][i])
        piv = A[p][p]
        if piv < 0:
            return False, piv
        if piv == 0:
            # then the whole row must vanish for PSD
            if any(A[p][j] != 0 for j in active):
                return False, Fraction(0)
            active.remove(p)
            minpiv = Fraction(0) if minpiv is None else min(minpiv, Fraction(0))
            continue
        minpiv = piv if minpiv is None else min(minpiv, piv)
        active.remove(p)
        rowp = {j: A[p][j] for j in active}
        for i in active:
            if rowp[i] == 0:
                continue
            fi = rowp[i] / piv
            Ai = A[i]
            for j in active:
                if rowp[j]:
                    Ai[j] -= fi * rowp[j]
    return True, minpiv


def charpoly_psd(Z):
    """Exact PSD test by the alternating-sign criterion on the characteristic polynomial (flint)."""
    n = len(Z)
    den = 1
    for row in Z:
        for x in row:
            den = den * Fraction(x).denominator // math.gcd(den, Fraction(x).denominator)
    M = flint.fmpz_mat(n, n, [int(Fraction(x) * den) for row in Z for x in row])
    if M != M.transpose():
        return False
    cp = M.charpoly()
    co = [int(cp[i]) for i in range(n + 1)]
    return all(((-1) ** kk) * co[n - kk] >= 0 for kk in range(n + 1))
