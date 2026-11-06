"""Exact zero-mode points (Gaussian-integer data with exact isometric liftings) and exact zero-mode
ranges R_t (in exact V coordinates of every block type).

Zero-mode families F_J (k = 3): C = (S Omega)_J (x) |u><v|_{J^c}, S = x y^T - y x^T.
  |J| = 1: P = |0><0|+|1><1| on site 0, u, v in Z[i]^{d^2}; lifting A = [e0 (x) u, e1 (x) u].
  |J| = 2: x, y in Z[i]^4 Hermitian-orthogonal with |x| = |y|; u, v in Z[i]^2 (WLOG in the first two
           levels of site 2 by U(d) invariance); lifting A = [x (x) u, y (x) u]; support (C^2)^{x3}.
  |J| = 3: x, y in Z[i]^8 as above; lifting A = [x, y]; support (C^2)^{x3}.
b-vector: proportional to vec(C^* A) (common positive factors dropped; families are rescaled
consistently because the a- and b-scalings enter as a congruence of the Gram block, see gram_fix).
The moments t[w] = <psi|P_w|psi> do not depend on the ambient local dimension, so supports of
dimension 2 are computed at d = 2 and lifted with the d-dimensional Gram inverse.
"""
import itertools
import math
import pickle
import sys
import time

import numpy as np
import flint

sys.path.insert(0, '<ROOT>/dim')
import physical as ph
from exact import gram_word_matrix, keep_set, rat_matrix_inverse, mode_product, perms
from exact_blocks import ExactRelax, FAMILY_GROUP, FAMILIES, qcolspace

ISY = np.array([[0, 1], [-1, 0]])


def gauss_pair(n, rng, maxtries=10 ** 6):
    """Small Gaussian-integer x, y in Z[i]^n with x^* y = 0, |x|^2 = |y|^2, both nonzero."""
    vals = np.array([-1, 0, 1])
    for _ in range(maxtries):
        x = rng.choice(vals, n) + 1j * rng.choice(vals, n)
        y = rng.choice(vals, n) + 1j * rng.choice(vals, n)
        if np.vdot(x, x).real == 0:
            continue
        if abs(np.vdot(x, y)) == 0 and np.vdot(x, x).real == np.vdot(y, y).real:
            # avoid trivially related pairs (y proportional to a coordinate permutation of x is fine)
            if np.linalg.matrix_rank(np.array([x, y])) == 2:
                return x, y
    raise RuntimeError('no pair found')


def embed(vec_small, dims_small, dims_big):
    """Embed a tensor with dims_small into dims_big (first levels)."""
    T = np.asarray(vec_small).reshape(dims_small)
    out = np.zeros(dims_big, dtype=complex)
    out[tuple(slice(0, s) for s in dims_small)] = T
    return out.reshape(-1)


def zero_mode_vectors(J, d, rng):
    """Returns (a, b, d_support) with a, b Gaussian-integer vectors on (C^ds)^{x3} x C^2 (index x*2+q)."""
    if J == 1:
        ds = d
        u = rng.integers(-1, 2, d * d) + 1j * rng.integers(-1, 2, d * d)
        v = rng.integers(-1, 2, d * d) + 1j * rng.integers(-1, 2, d * d)
        e0 = np.zeros(d)
        e0[0] = 1
        e1 = np.zeros(d)
        e1[1] = 1
        A = np.stack([np.kron(e0, u), np.kron(e1, u)], axis=1)
        C = np.kron(np.diag([1, 1] + [0] * (d - 2)), np.outer(u, v.conj()))
        Bv = C.conj().T @ A
    elif J == 2:
        ds = 2
        x, y = gauss_pair(4, rng)
        u = rng.integers(-1, 2, 2) + 1j * rng.integers(-1, 2, 2)
        v = rng.integers(-1, 2, 2) + 1j * rng.integers(-1, 2, 2)
        while np.vdot(u, u).real == 0:
            u = rng.integers(-1, 2, 2) + 1j * rng.integers(-1, 2, 2)
        while np.vdot(v, v).real == 0:
            v = rng.integers(-1, 2, 2) + 1j * rng.integers(-1, 2, 2)
        Om = np.kron(ISY, ISY)
        S = np.outer(x, y) - np.outer(y, x)
        C = np.kron(S @ Om, np.outer(u, v.conj()))
        A = np.stack([np.kron(x, u), np.kron(y, u)], axis=1)
        Bv = C.conj().T @ A
    else:
        ds = 2
        x, y = gauss_pair(8, rng)
        Om = np.kron(np.kron(ISY, ISY), ISY)
        S = np.outer(x, y) - np.outer(y, x)
        C = S @ Om
        A = np.stack([x, y], axis=1)
        Bv = C.conj().T @ A
    # check isometry up to scale and C = A B^* / (2 |A col|^2) structure
    G = A.conj().T @ A
    assert abs(G[0, 1]) == 0 and G[0, 0].real == G[1, 1].real
    # make Bv primitive-ish: divide by gcd of Gaussian integer entries' components
    comps = [int(round(z.real)) for z in Bv.ravel()] + [int(round(z.imag)) for z in Bv.ravel()]
    g = 0
    for c in comps:
        g = math.gcd(g, abs(c))
    g = g or 1
    Bv = Bv / g
    assert np.allclose(Bv, np.round(Bv.real) + 1j * np.round(Bv.imag))
    a = A.reshape(-1)
    b = Bv.reshape(-1)
    # true a = a_int / sqrt(2N), true b = sqrt(2) g b_int / sqrt(N)  (N = |A col|^2, g = removed gcd)
    return a, b, ds, C, int(round(G[0, 0].real)), g


def exact_point(k, d, a, b, ds, nproc, N=1, g=1):
    """Exact x (keep-set coefficients, scaled ints, den) for the three families; moments at ds.
    Families are rescaled by the true normalisation (alpha^2 = 1/(2N), beta^2 = 2 g^2 / N) so that the
    three families are mutually consistent (needed for the coupled Gram block)."""
    from fractions import Fraction
    vec = {'31': [a, a, a, b], '22': [a, a, b, b], '13': [b, b, b, a]}
    na = int(round(np.vdot(a, a).real))
    nb = int(round(np.vdot(b, b).real))
    al2, be2 = Fraction(1, na), Fraction(1, nb)      # |a| = |b| = 1 for the true physical point
    scale = {'31': al2 ** 3 * be2, '22': al2 ** 2 * be2 ** 2, '13': al2 * be2 ** 3}
    out = {}
    for f in FAMILIES:
        if nproc > 1:
            t, _ = ph.moment_tensor_par(k, ds, vec[f], FAMILY_GROUP[f], nproc)
        else:
            t, _ = ph.moment_tensor(k, ds, vec[f], FAMILY_GROUP[f])
        tr = np.round(t.real)
        assert np.abs(t.real - tr).max() < 1e-6 and np.abs(tr).max() < 2 ** 50, 'moments not exact'
        ti = tr.astype(np.int64).astype(object)
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
            x = mode_product(np.take(x, keep, axis=l), Ginv, l)
            den *= gden
        sc = scale[f]
        x = x * sc.numerator
        den = den * sc.denominator
        out[f] = (x, den, keeps)
    return out


if __name__ == '__main__':
    k, d = 3, int(sys.argv[1])
    nper = int(sys.argv[2])
    nproc = int(sys.argv[3])
    outp = sys.argv[4]
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    rng = np.random.default_rng(seed)
    t0 = time.time()
    pts = []
    for J in (1, 2, 3):
        for s in range(nper):
            a, b, ds, C, N, g = zero_mode_vectors(J, d, rng)
            q = ph.qk(C / np.linalg.norm(C), k, ds)
            P = exact_point(k, d, a, b, ds, nproc, N, g)
            pts.append(dict(J=J, a=a, b=b, ds=ds, q=q, x={f: (P[f][0], P[f][1], P[f][2]) for f in FAMILIES}))
            print('J=%d sample %d (ds=%d) q=%s done %.0fs' % (J, s, ds, q, time.time() - t0), flush=True)
            pickle.dump(pts, open(outp, 'wb'))
