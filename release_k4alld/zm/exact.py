"""Exact (integer/rational) machinery for the k-copy four-replica relaxation.

Local data: for each (n, m, cut) the rational highest-weight modules J_nu (integer columns), and
M_nu[p] = J_nu^T V_p^{Gamma} J_nu (integer matrices).  Tensors over words are numpy object arrays of
Python/flint integers together with a common denominator; mode products use flint.fmpz_mat.
"""
from __future__ import annotations

import itertools
import math
from fractions import Fraction

import numpy as np
import flint
import sympy as sp

from local import module_data, perms, compose, inverse, ncycles

P4 = perms(4)
I4 = {p: i for i, p in enumerate(P4)}
P3 = perms(3)
I3 = {p: i for i, p in enumerate(P3)}
TAU = (0, 1, 3, 2)
P0 = (2, 3, 1, 0)
SWAP03 = (3, 1, 2, 0)


def to_int_matrix(M):
    """sympy/fraction matrix -> (integer numpy object array, common denominator)."""
    rows = [[Fraction(int(sp.fraction(x)[0]), int(sp.fraction(x)[1])) if not isinstance(x, Fraction) else x
             for x in row] for row in (M.tolist() if hasattr(M, 'tolist') else M)]
    den = 1
    for row in rows:
        for x in row:
            den = den * x.denominator // math.gcd(den, x.denominator)
    arr = np.array([[int(x * den) for x in row] for row in rows], dtype=object)
    return arr, den


class ExactLocal:
    def __init__(self, n, m, cut):
        cut = tuple(sorted(cut))
        data = module_data(m, cut, n)
        self.n, self.m, self.cut = n, m, cut
        self.P = perms(m)
        self.labels = list(data)
        self.dims = [data[l]['dim'] for l in self.labels]
        self.off = [0]
        for d in self.dims:
            self.off.append(self.off[-1] + d * d)
        self.D = self.off[-1]
        self.M = []
        self.G = []
        self.pi = []
        for l in self.labels:
            G = data[l]['G']
            Gi, gd = to_int_matrix(G)
            assert gd == 1
            self.G.append(Gi)
            Ms = []
            for pi in data[l]['pi']:
                Mi, md = to_int_matrix(G * pi)
                assert md == 1, 'M not integral'
                Ms.append(Mi)
            self.M.append(np.array(Ms, dtype=object))
            self.pi.append(data[l]['pi'])
        self.FT = np.zeros((self.D, len(self.P)), dtype=object)
        for li in range(len(self.labels)):
            self.FT[self.off[li]:self.off[li + 1], :] = self.M[li].reshape(len(self.P), -1).T

    def rows(self, li):
        return slice(self.off[li], self.off[li + 1])


# ---------------- flint helpers ----------------
def fz(A):
    A = np.asarray(A, dtype=object)
    return flint.fmpz_mat(A.shape[0], A.shape[1], [int(x) for x in A.ravel()])


def from_fz(Mz, shape=None):
    arr = np.array([int(x) for x in Mz.entries()], dtype=object).reshape(Mz.nrows(), Mz.ncols())
    return arr if shape is None else arr.reshape(shape)


def mode_product(T, A, axis):
    """Integer tensor T (object array), integer matrix A (r x T.shape[axis]) -> contract along axis."""
    Tm = np.moveaxis(T, axis, 0)
    shp = Tm.shape
    Tm = Tm.reshape(shp[0], -1)
    R = fz(A) * fz(Tm)
    R = from_fz(R).reshape((A.shape[0],) + shp[1:])
    return np.moveaxis(R, 0, axis)


def rat_matrix_inverse(A):
    """Exact inverse of an integer matrix: (integer matrix, denominator)."""
    Aq = flint.fmpq_mat(fz(A))
    Ai = Aq.inv()
    num, den = Ai.numer_denom()
    return from_fz(num), int(den)


# ---------------- exact physical points ----------------
LETTERS = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'


def gram_word_matrix(n):
    return np.array([[n ** ncycles(compose(inverse(v), w)) for w in P4] for v in P4], dtype=object)


def keep_set(n):
    """Indices of permutations forming a basis of span{V_p} on (C^n)^{x4} (greedy, exact rank)."""
    G = gram_word_matrix(n)
    keep = []
    for j in range(24):
        cand = keep + [j]
        sub = flint.fmpq_mat(fz(G[np.ix_(cand, cand)]))
        if sub.rank() == len(cand):
            keep = cand
    return keep


def exact_moment_x(k, d, vecs, G, nproc=1):
    """Exact permutation coefficients x (scaled integers, denominator) of the twirled, site-averaged,
    real part of the moment of psi = vecs[0] x .. x vecs[3] (Gaussian-integer vectors).
    Returns (xint, den, keeps) with x supported on keep sets per mode."""
    import physical as ph
    if nproc > 1:
        t, _ = ph.moment_tensor_par(k, d, vecs, G, nproc)
    else:
        t, _ = ph.moment_tensor(k, d, vecs, G)
    tr = np.round(t.real)
    assert np.abs(t.real - tr).max() < 1e-6 and np.abs(tr).max() < 2 ** 50, 'moment not exact integer'
    ti = tr.astype(np.int64).astype(object)
    # site average (sum; divide later)
    ts = np.zeros(ti.shape, dtype=object)
    for s in perms(k):
        ts = ts + np.transpose(ti, list(s) + [k])
    den = len(perms(k))
    keeps = []
    x = ts
    for l in range(k + 1):
        n = 2 if l == k else d
        keep = keep_set(n)
        keeps.append(keep)
        Gm = gram_word_matrix(n)
        Ginv, gden = rat_matrix_inverse(Gm[np.ix_(keep, keep)])
        # x_keep = Ginv t[keep]
        xt = np.take(x, keep, axis=l)
        x = mode_product(xt, Ginv, l)
        den *= gden
    return x, den, keeps


def reduce_frac(xint, den):
    g = 0
    for v in xint.ravel():
        g = math.gcd(g, int(v))
        if g == 1:
            break
    g = math.gcd(g, den)
    if g > 1:
        xint = np.array([int(v) // g for v in xint.ravel()], dtype=object).reshape(xint.shape)
        den //= g
    return xint, den
