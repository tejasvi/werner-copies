#!/usr/bin/env python
"""Exact parametric certificate for the profile LP (paper, Section 9).  certify(k, gref, R): solve the LP at t = gref, keep the
active rows, solve the stationarity equations for the multipliers y_i(g) as rational functions of g, and check
  (i) the identity q_k(g; a) = LB(g) + sum_i y_i(g) row_i(a) + sum z_m(g) (2 - a_m) + sum w_m(g) a_m as polynomials;
  (ii) the threshold gamma* is the smallest positive root of LB's numerator (isolated on a rational interval);
  (iii) every multiplier is positive on that interval.
Used by cert_k5.py.  rows_exact() here is an earlier row generator, not used by this package."""
import os, sys, itertools
from fractions import Fraction as Fr
from math import comb
import numpy as np
import sympy as sp
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # python -I does not add the script dir
from param_cert_ext import base_exact
from profile_lp_ext2 import group_multisets
g = sp.symbols('g', positive=True)


def rows_exact(k, d=None):
    R, seen = [], set()
    for s in range(2, k + 1):
        for lab, ineq in base_exact(s):
            for grp in group_multisets(k - s):
                opts = [[Fr(0), Fr(1)] if d is None else [Fr(-1, d ** r), Fr(1)] for r in grp]
                for gsel in itertools.product(*opts):
                    r_ = [Fr(0)] * (k + 1)
                    for key, cS in ineq.items():
                        for T in itertools.product([0, 1], repeat=len(grp)):
                            w = Fr(1); shift = 0
                            for t_, rr, gg in zip(T, grp, gsel):
                                if t_:
                                    w *= gg; shift += rr
                            if w != 0:
                                r_[key + shift] += cS * w
                    key_ = tuple(r_)
                    if key_ in seen:
                        continue
                    seen.add(key_)
                    R.append((lab + tuple('g%d=%s' % (rr, gg) for rr, gg in zip(grp, gsel)), r_))
    if d is not None:
        for j in range(k):
            r_ = [Fr(0)] * (k + 1); r_[j] = Fr(d); r_[j + 1] = Fr(-1); R.append((('mono', j), r_))
    return R


def certify(k, gref, R):
    A = -np.array([[float(v) for v in r] for _, r in R]); b = np.zeros(len(R))
    cf = [comb(k, m) * (-float(gref)) ** m for m in range(k + 1)]
    res = linprog(np.array(cf), A_ub=A, b_ub=b, bounds=[(1, 1)] + [(0, 2)] * k, method='highs')
    yn = -res.ineqlin.marginals; zn = -res.upper.marginals[1:]; wn = res.lower.marginals[1:]
    S = [i for i in range(len(R)) if yn[i] > 1e-10]
    Z = [m for m in range(1, k + 1) if zn[m - 1] > 1e-10]
    W = [m for m in range(1, k + 1) if wn[m - 1] > 1e-10]
    ys = sp.symbols('y0:%d' % len(S)); zs = sp.symbols('z0:%d' % len(Z)); ws = sp.symbols('w0:%d' % len(W))
    c = [sp.binomial(k, m) * (-g) ** m for m in range(k + 1)]
    Rat = lambda f: sp.Rational(f.numerator, f.denominator)
    eqs = []
    for m in range(1, k + 1):
        e = c[m] - sum(ys[t] * Rat(R[i][1][m]) for t, i in enumerate(S))
        if m in Z: e += zs[Z.index(m)]
        if m in W: e -= ws[W.index(m)]
        eqs.append(e)
    sol = list(sp.linsolve(eqs, list(ys) + list(zs) + list(ws)))[0]
    if any(sp.sympify(v).free_symbols - {g} for v in sol):
        return None
    sol = [sp.factor(sp.simplify(v)) for v in sol]
    LB = sp.factor(sp.expand(c[0] - sum(sol[t] * Rat(R[i][1][0]) for t, i in enumerate(S)) - 2 * sum(sol[len(S):len(S) + len(Z)])))
    P = sp.Poly(sp.numer(sp.together(LB)), g)
    gstar = min(r for r in P.real_roots() if r > 0); gs = sp.N(gstar, 25)
    lo, hi = [(x0, x1) for (x0, x1), mlt in P.intervals(eps=sp.Rational(1, 10 ** 14)) if x0 <= gs <= x1][0]
    names = [R[i][0] for i in S] + [('a_%d<=2' % m,) for m in Z] + [('a_%d>=0' % m,) for m in W]
    good = []
    for nm, v in zip(names, sol):
        num, den = sp.fraction(sp.together(v)); pn, pd = sp.Poly(num, g), sp.Poly(den, g)
        nr = pn.count_roots(lo, hi) if pn.degree() > 0 else 0; dr = pd.count_roots(lo, hi) if pd.degree() > 0 else 0
        good.append((nm, str(v), float(v.subs(g, gs)), nr == 0 and dr == 0 and v.subs(g, (lo + hi) / 2) > 0))
    a = [sp.Integer(1)] + list(sp.symbols('a1:%d' % (k + 1)))
    q = sum(c[m] * a[m] for m in range(k + 1))
    rhs = LB + sum(sol[t] * sum(Rat(R[i][1][m]) * a[m] for m in range(k + 1)) for t, i in enumerate(S))
    rhs += sum(sol[len(S) + t] * (2 - a[m]) for t, m in enumerate(Z)) + sum(sol[len(S) + len(Z) + t] * a[m] for t, m in enumerate(W))
    ident = sp.expand(q - rhs) == 0
    return dict(gs=gs, LB=LB, mult=good, ident=ident, ok=ident and all(x[3] for x in good))


if __name__ == '__main__':
    for arg in sys.argv[1:]:
        ps = arg.split(':'); k = int(ps[0]); gr = Fr(ps[1]); d = int(ps[2]) if len(ps) > 2 else None
        C = certify(k, gr, rows_exact(k, d))
        print('k = %d d = %s: gamma* = %s  (root of %s) | identity %s | CERTIFIED %s' % (k, d or 'all', C['gs'], sp.factor(C['LB']), C['ident'], C['ok']))
        for nm, expr, val, gd in C['mult']:
            print('    %-46s %s   (at g*: %.4e, > 0: %s)' % (str(nm), expr, val, gd))
