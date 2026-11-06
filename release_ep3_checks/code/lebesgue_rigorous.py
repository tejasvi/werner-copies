#!/usr/bin/env python3
"""Certified upper bounds for the two Lebesgue constants that dim/ac/uniform_verify.py uses (written for this package).

uniform_verify.py interpolates on [0, H], H = 1/17, at two sets of nodes that it builds as exact rationals:
  - the 28 evaluation points `se` (their Lebesgue constant Lam_e multiplies the residual and G bounds),
  - the 16 Chebyshev nodes `cm` of the pseudo-inverse interpolation (LamM multiplies Mmax),
and it bounds Lambda(s) = sum_j |l_j(s)| on [0, H] by a floating-point grid plus a Markov-type derivative estimate
(3.4895 and 3.0645).  This script bounds sup_{[0,H]} Lambda by interval arithmetic (mpmath.iv, outward rounding):
  - [0, H] is cut into subintervals with exact rational end points; on each subinterval S an interval enclosure of
    sum_j |l_j(S)| is computed from enclosures of the nodes and of the exact denominators prod_{i != j} (p_j - p_i);
  - S is bisected until the upper end of its enclosure is at most the target T, or S is shorter than WMIN;
  - the certified bound is the largest upper end over the final subintervals, which cover [0, H].
Point enclosures at the midpoints and end points of the highest subintervals give a rigorous lower bound, which shows
how tight the certified bound is.  The script first checks that its nodes reproduce uniform_verify's own grid values.
For these Chebyshev-type nodes the supremum is attained at s = 0 and s = H, outside the outermost nodes, where every
factor s - p_i has one sign and the enclosures are tight; the script prints where the highest upper end lies.
Usage: lebesgue_rigorous.py [T28 [T16]]          (targets of the bisection; defaults 3.0845 and 2.7285)"""
import math
import sys
import time
from fractions import Fraction

import numpy as np
from mpmath import iv
from mpmath.libmp import finf, fnan, fninf, to_rational

iv.prec = 80
H = Fraction(1, 17)
WMIN = H / 2 ** 40
USED = {28: 3.4895, 16: 3.0645}          # the constants printed by uniform_verify.py (its log: 3.4895, 3.0645)
t0 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)


def nodes(M):
    """the nodes exactly as uniform_verify.py builds them (se for M = 28, cm for M = 16)"""
    return [Fraction(math.floor((float(H) / 2) * (1 - math.cos((2 * k + 1) * math.pi / (2 * M))) * 10 ** 15), 10 ** 15)
            for k in range(M)]


def grid_bound(pts, a, b):
    """uniform_verify.py's lebesgue(): float grid of 8 m^3 points and Markov-type factor (consistency check only)"""
    m = len(pts)
    grid = 8 * m ** 3
    p = np.array([float(x) for x in pts])
    ss = np.linspace(float(a), float(b), grid)
    lam = np.zeros(grid)
    for j in range(m):
        lj = np.ones(grid)
        for i in range(m):
            if i != j:
                lj *= (ss - p[i]) / (p[j] - p[i])
        lam += np.abs(lj)
    mx = lam.max() * (1 + 1e-10)
    q = (float(b) - float(a)) / (grid - 1) / 2 * m * 2 * (m - 1) ** 2 / (float(b) - float(a))
    return mx / (1 - q)


def rational(t):
    """exact value of a raw finite mpf"""
    assert t not in (finf, fninf, fnan), 'non-finite interval end'
    p, q = to_rational(t)
    return Fraction(p, q)


def lo(x):
    return rational(x._mpi_[0])


def hi(x):
    return rational(x._mpi_[1])


def enclose(q):
    """interval enclosure of the rational q, checked exactly"""
    e = iv.mpf(q.numerator) / iv.mpf(q.denominator)
    assert lo(e) <= q <= hi(e), q
    return e


def span(a, b):
    """interval containing the rational segment [a, b], checked exactly"""
    S = iv.mpf([enclose(a).a, enclose(b).b])
    assert lo(S) <= a and b <= hi(S), (a, b)
    return S


def enclosure(S, P, inv_den):
    """enclosure of {sum_j |l_j(s)| : s in S}"""
    m = len(P)
    D = [S - p for p in P]
    pre, suf = [None] * m, [None] * m
    acc = iv.mpf(1)
    for i in range(m):
        pre[i] = acc
        acc = acc * D[i]
    acc = iv.mpf(1)
    for i in range(m - 1, -1, -1):
        suf[i] = acc
        acc = acc * D[i]
    tot = iv.mpf(0)
    for j in range(m):
        tot += abs(pre[j] * suf[j] * inv_den[j])
    return tot


def certify(pts, T):
    m = len(pts)
    T = Fraction(T)
    P = [enclose(p) for p in pts]
    inv_den = []
    for j in range(m):
        d = Fraction(1)
        for i in range(m):
            if i != j:
                d *= pts[j] - pts[i]
        inv_den.append(enclose(1 / d))
    stack, leaves, evals, upper = [(Fraction(0), H)], [], 0, Fraction(0)
    while stack:
        a, b = stack.pop()
        u = hi(enclosure(span(a, b), P, inv_den))
        evals += 1
        if evals % 20000 == 0:
            log('   %d enclosures, %d subintervals done, highest upper end so far %.6f' % (evals, len(leaves), upper))
        if u <= T or b - a <= WMIN:
            leaves.append((u, a, b))
            upper = max(upper, u)
        else:
            mid = (a + b) / 2
            stack += [(mid, b), (a, mid)]
    covered = sorted((a, b) for _, a, b in leaves)
    assert covered[0][0] == 0 and covered[-1][1] == H and all(x[1] == y[0] for x, y in zip(covered, covered[1:]))
    lower = Fraction(0)
    for _, a, b in sorted(leaves, reverse=True)[:40]:
        for s in (a, (a + b) / 2, b):
            lower = max(lower, lo(enclosure(span(s, s), P, inv_den)))
    top = max(leaves)
    return upper, lower, evals, len(leaves), min(b - a for _, a, b in leaves), (top[1], top[2])


if __name__ == '__main__':
    targets = {28: float(sys.argv[1]) if len(sys.argv) > 1 else 3.0845, 16: float(sys.argv[2]) if len(sys.argv) > 2 else 2.7285}
    e = abs(iv.mpf([-1, 2]))
    assert lo(e) == 0 and hi(e) == 2, 'interval abs'
    ok = True
    for M, name in ((28, '28 evaluation points (se)'), (16, '16 Chebyshev nodes (cm)')):
        pts = nodes(M)
        g = grid_bound(pts, 0, H)
        log('%s: nodes %s/10^15 ... %s/10^15; uniform_verify grid value recomputed from them: %.4f (its log: %.4f)'
            % (name, pts[0].numerator, pts[-1].numerator, g, USED[M]))
        assert round(g, 4) == USED[M], 'the nodes do not reproduce uniform_verify.py'
        upper, lower, evals, nleaves, wmin, (ta, tb) = certify(pts, targets[M])
        good = upper < Fraction(USED[M])
        ok &= good
        up6 = Fraction(math.ceil(upper * 10 ** 6), 10 ** 6)      # printed values: upper bound rounded up,
        low6 = Fraction(math.floor(lower * 10 ** 6), 10 ** 6)    # lower bound rounded down
        log('%s: certified sup Lambda <= %.6f (lower bound %.6f), highest on [%.3e, %.3e]; %d enclosures, %d subintervals, '
            'smallest width %.2e; %s %.4f' % (name, up6, low6, float(ta), float(tb), evals, nleaves, float(wmin),
                                              '<' if good else 'NOT <', USED[M]))
    log('LEBESGUE BOUNDS CERTIFIED: both constants used by uniform_verify.py hold' if ok else 'FAIL: a constant is not certified')
