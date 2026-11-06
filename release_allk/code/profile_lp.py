#!/usr/bin/env python
"""Symmetric partial-trace profile LP (paper, Section 9).  Only the helper parts() is used by this package.
Profile a_j = avg_{|K|=j} ||Tr_K C||^2 / ||C||^2, a_0 = 1, 0 <= a_j <= 2.  q_k(g) = sum_j C(k,j) (-g)^j a_j.
The function rows() below is the original floating-point row generator of the first version of the LP; it is not called by
the scripts of this package (they use param_cert_ext.base_exact and profile_lp_k5)."""
import itertools, sys
import numpy as np
from math import comb
from scipy.optimize import linprog


def parts(s, m, mn=1):
    if m == 1:
        if s >= mn:
            yield (s,)
        return
    for x in range(mn, s // m + 1):
        for rest in parts(s - x, m - 1, x):
            yield (x,) + rest


def rows(k, frozen=True, foi_max=7, ep3=True, ep3_grid=False, sc2_grid=True, cr=True):
    n = k + 1
    A, b = [], []
    totals = range(2, k + 1) if frozen else [k]
    for s in totals:
        for (x, y) in parts(s, 2):
            r = np.zeros(n); r[x] += 1; r[y] += 1; r[s] -= 0.5; A.append(r); b.append(2.0)
            if cr:
                r = np.zeros(n); r[x] += 1; r[y] -= 1; r[s] += 0.5; A.append(r); b.append(2.0)
                r = np.zeros(n); r[y] += 1; r[x] -= 1; r[s] += 0.5; A.append(r); b.append(2.0)
            if sc2_grid:
                for t in np.linspace(0.02, 0.5, 25):
                    r = np.zeros(n); r[x] += t; r[y] += t; r[s] -= t * t; A.append(r); b.append(1 - (1 - 2 * t) * (1 - t))
        for m in range(3, min(foi_max, s) + 1):
            for comp in parts(s, m):
                r = np.zeros(n)
                for x in comp:
                    r[x] += 1
                A.append(r); b.append(float(m + 1))
        if ep3 and s >= 3:
            for comp in parts(s, 3):
                ts = [0.5] + (list(np.linspace(0.05, 0.45, 9)) if ep3_grid else [])
                for t in ts:
                    r = np.zeros(n)          # -q_3(t) <= -c_3(t) * 0  (use q_3(t) >= 0)
                    for u in range(4):
                        for U in itertools.combinations(range(3), u):
                            r[sum(comp[g] for g in U)] -= (-t) ** u
                    A.append(r); b.append(0.0)
    return np.array(A), np.array(b)


def lp_min(k, g, A, b):
    n = k + 1
    c = np.array([comb(k, j) * (-g) ** j for j in range(n)])
    res = linprog(c, A_ub=A, b_ub=b, bounds=[(1, 1)] + [(0, 2)] * k, method='highs')
    return (res.fun, res.x) if res.status == 0 else (-9.0, None)


def gamma(k, A, b, iters=45):
    lo, hi = 0.0, 0.5
    for _ in range(iters):
        mid = (lo + hi) / 2
        if lp_min(k, mid, A, b)[0] >= -1e-12:
            lo = mid
        else:
            hi = mid
    return lo


if __name__ == '__main__':
    ks = [int(s) for s in sys.argv[1].split(',')]
    cfgs = [('BASE(full)', dict(frozen=False, ep3=False)), ('BASE+frozen', dict(frozen=True, ep3=False)),
            ('EP3(full)', dict(frozen=False, ep3=True)), ('EP3+frozen', dict(frozen=True, ep3=True))]
    for k in ks:
        out = []
        for name, kw in cfgs:
            A, b = rows(k, **kw)
            g = gamma(k, A, b)
            out.append('%s %.8f (k g %.4f)' % (name, g, k * g))
        print('k = %2d | ' % k + ' | '.join(out), flush=True)
