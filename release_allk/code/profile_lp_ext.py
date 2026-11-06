#!/usr/bin/env python
"""Floating-point profile LP with single compressed copies (an earlier variant of the paper's Section 9 rows).
Only imported here because profile_lp_ext2 imports base_ineqs from it; no script of this package calls it."""
import itertools, os, sys
from math import comb
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # python -I does not add the script dir
from profile_lp import parts


def base_ineqs(s):
    """list of (coeff dict over 'size of traced union', rhs) for inequalities of the form sum_S c_S a_{size(S)} >= 0 written as
    sum_S c_S a_size(S) + const >= 0 with groups covering s sites; returned as list of (groups, dict S-size-> coeff) with constant in key 0."""
    out = []
    for (x, y) in parts(s, 2):
        out.append({0: 2.0, x: -1.0, y: -1.0, s: 0.5} if x != y else {0: 2.0, x: -2.0, s: 0.5})            # FHPV
        out.append({0: 2.0, x: -1.0, y: 1.0, s: -0.5} if x != y else None)                                      # CR
        out.append({0: 2.0, y: -1.0, x: 1.0, s: -0.5} if x != y else None)
    for m in range(3, min(7, s) + 1):
        for comp in parts(s, m):
            d = {0: float(m + 1)}
            for x in comp:
                d[x] = d.get(x, 0.0) - 1.0
            out.append(d)
    if s >= 3:
        for comp in parts(s, 3):
            d = {}
            for u in range(4):
                for U in itertools.combinations(range(3), u):
                    key = sum(comp[g] for g in U)
                    d[key] = d.get(key, 0.0) + (-0.5) ** u
            out.append(d)
    return [o for o in out if o is not None]


def rows(k, gmin=0.0, dmono=None):
    n = k + 1
    A, b = [], []
    for s in range(2, k + 1):
        for ineq in base_ineqs(s):
            rest = k - s
            for n1 in range(rest + 1):
                n2 = rest - n1
                r = np.zeros(n)                       # constraint: sum r_j a_j >= 0, with a_0 = 1 handled as a variable fixed to 1
                for key, cS in ineq.items():
                    for r1 in range(n1 + 1):
                        for r2 in range(n2 + 1):
                            w = comb(n1, r1) * comb(n2, r2) * (gmin ** r2 if r2 else 1.0)
                            if w == 0:
                                continue
                            r[key + r1 + r2] += cS * w
                A.append(-r); b.append(0.0)
    if dmono:
        for j in range(k):
            r = np.zeros(n); r[j + 1] = 1.0; r[j] = -dmono; A.append(r); b.append(0.0)
    return np.array(A), np.array(b)


def gamma(k, A, b, iters=45):
    lo, hi = 0.0, 0.5
    for _ in range(iters):
        mid = (lo + hi) / 2
        c = np.array([comb(k, j) * (-mid) ** j for j in range(k + 1)])
        res = linprog(c, A_ub=A, b_ub=b, bounds=[(1, 1)] + [(0, 2)] * k, method='highs')
        if res.status == 0 and res.fun >= -1e-12:
            lo = mid
        else:
            hi = mid
    return lo


if __name__ == '__main__':
    for k in [int(s) for s in sys.argv[1].split(',')]:
        # all d: compressions gamma in {0, 1} (n2 sites frozen)
        A, b = rows(k, gmin=0.0); g1 = gamma(k, A, b)
        # d = 3: gamma in {-1/3, 1} + monotonicity a_{j+1} <= 3 a_j
        A3, b3 = rows(k, gmin=-1.0 / 3); g3 = gamma(k, A3, b3)
        A3m, b3m = rows(k, gmin=-1.0 / 3, dmono=3.0); g3m = gamma(k, A3m, b3m)
        A4m, b4m = rows(k, gmin=-1.0 / 4, dmono=4.0); g4m = gamma(k, A4m, b4m)
        print('k = %d | all-d (+compressed sites): %.6f | d=3 (gamma >= -1/3): %.6f | d=3 + mono: %.6f | d=4 + mono: %.6f' % (
            k, g1, g3, g3m, g4m), flush=True)
