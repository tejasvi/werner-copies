#!/usr/bin/env python
"""Rows of the profile LP of the paper, Section 9, for C of rank at most two on (C^d)^{(x)k}, every d.
Base inequalities on disjoint groups of copies (Lemma 9.1(a)), with the input labels of the paper:
  FHPV (I2), CR (I3), EP3 (I4)   from param_cert_ext.base_exact;
  K4    q_4(79/160, .) >= 0 (I5) on 4 groups:  prod_i (1 - (79/160) S^{k_i});
  K5    q_5(9/20, .)   >= 0 (I6) on 5 groups:  prod_i (1 - (9/20) S^{k_i})   (included iff k5=True).
Every base inequality is applied with the leftover copies frozen or split into compressed sets R_l (Lemma 9.1(b)), each giving a
factor 1 + S^{|R_l|} (label 'g<r>=1').  A row is base(S) * prod_l (1 + S^{r_l}) truncated at degree k and read as
sum_j row_j a_j >= 0 with a_0 = 1; the LP also uses 0 <= a_j <= 2 ((I1) and Lemma 9.1(a)).
The options d = <int>, EP4_3, EP5_3 (the qutrit inputs of Section 8) and the fixed-d group factors are not used by this package.
rows_exact gives Fraction rows (exact certificates), rows_float the same rows in floating point (LP).
usage: profile_lp_k5.py all K1,K2,... k5=1     (prints the LP threshold gamma_k for each k)"""
import itertools, os, sys
from fractions import Fraction as Fr
from math import comb
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # python -I does not add the script dir
from profile_lp import parts
from param_cert_ext import base_exact
from profile_lp_ext2 import group_multisets

T_K4 = Fr(79, 160)
T_EP4_3 = Fr(4979, 10000)
T_EP5_3 = Fr(47, 100)
T_K5 = Fr(9, 20)


def ep_on_groups(comp, t):
    """q_m(t) on m groups of sizes comp: sum_{U subset [m]} (-t)^|U| a_{sum_{i in U} comp_i}"""
    d = {}
    for u in range(len(comp) + 1):
        for U in itertools.combinations(range(len(comp)), u):
            key = sum(comp[i] for i in U)
            d[key] = d.get(key, Fr(0)) + (-t) ** u
    return d


def bases(k, d=None, tk4=T_K4, t4=T_EP4_3, t5=T_EP5_3, k4=True, ep45=True, ep1=False, triv=False, k5=False, tk5=T_K5):
    """(s, label, dict) for every base inequality on groups covering s <= k copies"""
    out = []
    for s in range(2, k + 1):
        for lab, ineq in base_exact(s):
            out.append((s, lab, ineq))
        if k4 and s >= 4:
            for comp in parts(s, 4):
                out.append((s, ('K4',) + comp, ep_on_groups(comp, tk4)))
        if k5 and s >= 5:
            for comp in parts(s, 5):
                out.append((s, ('K5',) + comp, ep_on_groups(comp, tk5)))
    if d == 3 and ep45:
        if k >= 4:
            out.append((4, ('EP4_3',), ep_on_groups((1, 1, 1, 1), t4)))
        if k >= 5:
            out.append((5, ('EP5_3',), ep_on_groups((1, 1, 1, 1, 1), t5)))
    if ep1:
        for s in range(1, k + 1):
            out.append((s, ('EP1', s), {0: Fr(2), s: Fr(-1)}))
    if triv:
        out.append((0, ('norm',), {0: Fr(1)}))
    return out


def group_factors(r, d):
    if d is None:
        return [('g%d=1' % r, [Fr(1)] + [Fr(0)] * (r - 1) + [Fr(1)])]
    o = [('g%d=-1/%d' % (r, d ** r), [Fr(1)] + [Fr(0)] * (r - 1) + [Fr(-1, d ** r)]),
         ('g%d=1' % r, [Fr(1)] + [Fr(0)] * (r - 1) + [Fr(1)])]
    if r == 2:
        o.append(('ent2', [Fr(1), Fr(-2, d), Fr(1)]))
    return o


def polymul(a, b, n):
    out = [Fr(0)] * n
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            if i + j < n:
                out[i + j] += x * y
    return out


def rows_exact(k, d=None, **kw):
    R, seen = [], set()
    for s, lab, ineq in bases(k, d, **kw):
        base = [Fr(0)] * (k + 1)
        for key, c in ineq.items():
            base[key] += c
        for grp in group_multisets(k - s):
            for sel in itertools.product(*[group_factors(r, d) for r in grp]):
                row = base[:]
                for _, P in sel:
                    row = polymul(row, P, k + 1)
                key = tuple(row)
                if key in seen:
                    continue
                seen.add(key)
                R.append((lab + tuple(nm for nm, _ in sel), row))
    if d is not None:
        for j in range(k):
            r_ = [Fr(0)] * (k + 1); r_[j] = Fr(d); r_[j + 1] = Fr(-1); R.append((('mono', j), r_))
    return R


def rows_float(k, d=None, **kw):
    """same rows in floating point (numpy convolutions), deduplicated; returns A_ub with A_ub a <= 0"""
    A, seen = [], set()
    gf = {}
    for s, lab, ineq in bases(k, d, **kw):
        base = np.zeros(k + 1)
        for key, c in ineq.items():
            base[key] += float(c)
        for grp in group_multisets(k - s):
            opts = []
            for r in grp:
                if (r, d) not in gf:
                    gf[(r, d)] = [np.array([float(x) for x in P]) for _, P in group_factors(r, d)]
                opts.append(gf[(r, d)])
            for sel in itertools.product(*opts):
                row = base
                for P in sel:
                    row = np.convolve(row, P)[:k + 1]
                key = tuple(np.round(row, 11))
                if key in seen:
                    continue
                seen.add(key)
                A.append(-row)
    if d is not None:
        for j in range(k):
            r_ = np.zeros(k + 1); r_[j + 1] = 1.0; r_[j] = -d; A.append(r_)
    return np.array(A)


def lp_min(k, A, t):
    c = np.array([comb(k, j) * (-t) ** j for j in range(k + 1)])
    res = linprog(c, A_ub=A, b_ub=np.zeros(len(A)), bounds=[(1, 1)] + [(0, 2)] * k, method='highs')
    return res


def gamma(k, A, iters=42, lo=0.0, hi=0.5):
    for _ in range(iters):
        mid = (lo + hi) / 2
        res = lp_min(k, A, mid)
        if res.status == 0 and res.fun >= -1e-12:
            lo = mid
        else:
            hi = mid
    return lo


if __name__ == '__main__':
    import time
    mode = sys.argv[1]                     # 'all' or an integer d
    ks = [int(x) for x in sys.argv[2].split(',')]
    opts = dict(a.split('=') for a in sys.argv[3:])
    kw = {key: bool(int(v)) for key, v in opts.items() if key in ('k4', 'ep45', 'ep1', 'triv', 'k5')}
    kw.update({key: Fr(v) for key, v in opts.items() if key in ('t4', 't5', 'tk4', 'tk5')})
    d = None if mode == 'all' else int(mode)
    for k in ks:
        t0 = time.time()
        A = rows_float(k, d, **kw)
        g = gamma(k, A)
        res = lp_min(k, A, g)
        print('d = %s k = %2d %s: gamma %.10f  k*gamma %.6f | rows %d | %.0fs | vertex %s' % (
            mode, k, kw, g, k * g, len(A), time.time() - t0, np.round(res.x, 5).tolist()), flush=True)
