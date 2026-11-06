#!/usr/bin/env python
"""Profile LP with compressed groups (paper, Lemma 9.1(b)): the copies outside the groups of a base inequality are split into
sets R_1..R_p, each contributing a factor 1 + S^{|R_l|} (all dimensions), and frozen copies (Lemma 9.1(a)).
This package uses only group_multisets() from this module."""
import itertools, os, sys
from math import comb
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # python -I does not add the script dir
from profile_lp import parts
from profile_lp_ext import base_ineqs


def group_multisets(n, maxparts=None):
    """all multisets of positive sizes with sum <= n (the rest frozen)"""
    out = [()]
    def rec(rem, mn, cur):
        for x in range(mn, rem + 1):
            nxt = cur + (x,)
            out.append(nxt)
            rec(rem - x, x, nxt)
    rec(n, 1, ())
    return out


def rows(k, gammas=(1.0,), d=None, dmono=None):
    """gammas: allowed gamma values per compressed group, as functions of D (callables) or floats"""
    n = k + 1
    A, b, seen = [], [], set()
    for s in range(2, k + 1):
        for ineq in base_ineqs(s):
            for grp in group_multisets(k - s):
                gchoices = []
                for r in grp:
                    opts = []
                    for gm in gammas:
                        opts.append(gm(d ** r) if callable(gm) else gm)
                    gchoices.append(opts)
                for gsel in itertools.product(*gchoices):
                    r_ = np.zeros(n)
                    for key, cS in ineq.items():
                        for T in itertools.product([0, 1], repeat=len(grp)):
                            w = 1.0; shift = 0
                            for t_, rr, gg in zip(T, grp, gsel):
                                if t_:
                                    w *= gg; shift += rr
                            if w != 0:
                                r_[key + shift] += cS * w
                    key_ = tuple(np.round(r_, 12))
                    if key_ in seen:
                        continue
                    seen.add(key_)
                    A.append(-r_); b.append(0.0)
    if dmono:
        for j in range(k):
            r_ = np.zeros(n); r_[j + 1] = 1.0; r_[j] = -dmono; A.append(r_); b.append(0.0)
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
        A, b = rows(k, gammas=(0.0, 1.0)); g1 = gamma(k, A, b)
        A3, b3 = rows(k, gammas=(lambda D: -1.0 / D, 1.0), d=3, dmono=3.0); g3 = gamma(k, A3, b3)
        print('k = %d | all-d (compressed groups, gamma in {0,1}): %.6f (rows %d) | d=3 (gamma in {-1/D,1} + mono): %.6f (rows %d)' % (
            k, g1, len(A), g3, len(A3)), flush=True)
