#!/usr/bin/env python
"""Base inequalities of the profile LP (paper, Section 9) in exact arithmetic, base_exact(s): on groups covering s copies,
  FHPV(x, y) = (I2): 2 - S^x - S^y + S^{x+y}/2;   CR(x, y) = (I3): 2 - S^x + S^y - S^{x+y}/2 (both orders);
  EP3(x, y, z) = (I4): prod (1 - S^{k_i}/2).
The original computation also generated rows FOI_m (sum_i a_{k_i} <= m + 1, 3 <= m <= 7).  They are not among the inputs (I1)-(I6)
of the paper, none of them carries weight in the shipped certificates, and they are switched off here (FOI_MAX = 2).
rows_exact / certify: single compressed copies (an earlier variant; not used by the scripts of this package)."""
import os, sys, itertools
from fractions import Fraction as Fr
from math import comb
import numpy as np
import sympy as sp
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # python -I does not add the script dir
from profile_lp import parts

g = sp.symbols('g', positive=True)
FOI_MAX = 2          # no FOI_m rows (the original computation used 7)


def base_exact(s):
    H = Fr(1, 2); out = []
    for (x, y) in parts(s, 2):
        d = {0: Fr(2), s: H}; d[x] = d.get(x, 0) - 1; d[y] = d.get(y, 0) - 1; out.append((('FHPV', x, y), d))
        if x != y:
            out.append((('CR', x, y), {0: Fr(2), x: Fr(-1), y: Fr(1), s: -H}))
            out.append((('CR', y, x), {0: Fr(2), y: Fr(-1), x: Fr(1), s: -H}))
    for m in range(3, min(FOI_MAX, s) + 1):
        for comp in parts(s, m):
            d = {0: Fr(m + 1)}
            for x in comp:
                d[x] = d.get(x, 0) - 1
            out.append((('FOI',) + comp, d))
    if s >= 3:
        for comp in parts(s, 3):
            d = {}
            for u in range(4):
                for U in itertools.combinations(range(3), u):
                    key = sum(comp[t] for t in U); d[key] = d.get(key, 0) + Fr(-1, 2) ** u
            out.append((('EP3',) + comp, d))
    return out


def rows_exact(k, gmin, dmono=None):
    R = []
    for s in range(2, k + 1):
        for lab, ineq in base_exact(s):
            rest = k - s
            for n1 in range(rest + 1):
                n2 = rest - n1
                r = [Fr(0)] * (k + 1)
                for key, cS in ineq.items():
                    for r1 in range(n1 + 1):
                        for r2 in range(n2 + 1):
                            w = comb(n1, r1) * comb(n2, r2) * (gmin ** r2)
                            r[key + r1 + r2] += cS * w
                R.append((lab + ('c%d' % n1, 'm%d' % n2), r))          # row: sum_j r_j a_j >= 0
    if dmono:
        for j in range(k):
            r = [Fr(0)] * (k + 1); r[j] = Fr(dmono); r[j + 1] = Fr(-1); R.append((('mono', j), r))
    return R


def certify(k, gref, gmin, dmono=None):
    R = rows_exact(k, gmin, dmono)
    A = -np.array([[float(v) for v in r] for _, r in R]); b = np.zeros(len(R))
    cf = [comb(k, m) * (-float(gref)) ** m for m in range(k + 1)]
    res = linprog(np.array(cf), A_ub=A, b_ub=b, bounds=[(1, 1)] + [(0, 2)] * k, method='highs')
    yn = -res.ineqlin.marginals; zn = -res.upper.marginals[1:]; wn = res.lower.marginals[1:]
    S = [i for i in range(len(R)) if yn[i] > 1e-10]
    Z = [m for m in range(1, k + 1) if zn[m - 1] > 1e-10]
    W = [m for m in range(1, k + 1) if wn[m - 1] > 1e-10]
    ys = sp.symbols('y0:%d' % len(S)); zs = sp.symbols('z0:%d' % len(Z)); ws = sp.symbols('w0:%d' % len(W))
    c = [sp.binomial(k, m) * (-g) ** m for m in range(k + 1)]
    eqs = []
    for m in range(1, k + 1):     # stationarity: c_m - sum y_i r_im + z_m - w_m = 0 (rows are r.a >= 0)
        e = c[m] - sum(ys[t] * sp.Rational(R[i][1][m].numerator, R[i][1][m].denominator) for t, i in enumerate(S))
        if m in Z: e += zs[Z.index(m)]
        if m in W: e -= ws[W.index(m)]
        eqs.append(e)
    unk = list(ys) + list(zs) + list(ws)
    sol = list(sp.linsolve(eqs, unk))[0]
    if any(sp.sympify(v).free_symbols - {g} for v in sol):
        return dict(ok=False, why='underdetermined', S=[R[i][0] for i in S])
    sol = [sp.factor(sp.simplify(v)) for v in sol]
    LB = c[0] - sum(sol[t] * sp.Rational(R[i][1][0].numerator, R[i][1][0].denominator) for t, i in enumerate(S)) - 2 * sum(sol[len(S):len(S) + len(Z)])
    LB = sp.factor(sp.expand(LB))
    P = sp.Poly(sp.numer(sp.together(LB)), g)
    gstar = min(r for r in P.real_roots() if r > 0)
    gs = sp.N(gstar, 25)
    lo, hi = [(x0, x1) for (x0, x1), mlt in P.intervals(eps=sp.Rational(1, 10 ** 14)) if x0 <= gs <= x1][0]
    good = []
    names = [R[i][0] for i in S] + [('a_%d<=2' % m,) for m in Z] + [('a_%d>=0' % m,) for m in W]
    for nm, v in zip(names, sol):
        num, den = sp.fraction(sp.together(v))
        pn, pd = sp.Poly(num, g), sp.Poly(den, g)
        nr = pn.count_roots(lo, hi) if pn.degree() > 0 else 0
        dr = pd.count_roots(lo, hi) if pd.degree() > 0 else 0
        good.append((nm, str(v), float(v.subs(g, gs)), nr == 0 and dr == 0 and v.subs(g, (lo + hi) / 2) > 0))
    # identity check: q_k(g; a) - sum y_i (r_i . a) - sum z(2 - a) - sum w a - LB == 0
    a = [sp.Integer(1)] + list(sp.symbols('a1:%d' % (k + 1)))
    q = sum(c[m] * a[m] for m in range(k + 1))
    rhs = LB + sum(sol[t] * sum(sp.Rational(R[i][1][m].numerator, R[i][1][m].denominator) * a[m] for m in range(k + 1)) for t, i in enumerate(S))
    rhs += sum(sol[len(S) + t] * (2 - a[m]) for t, m in enumerate(Z)) + sum(sol[len(S) + len(Z) + t] * a[m] for t, m in enumerate(W))
    ident = sp.expand(q - rhs) == 0
    return dict(ok=ident and all(x[3] for x in good), gstar=gstar, gs=gs, LB=LB, mult=good, ident=ident)


if __name__ == '__main__':
    for arg in sys.argv[1:]:
        parts_ = arg.split(':')
        k = int(parts_[0]); gr = Fr(parts_[1]); gm = Fr(parts_[2]); dm = int(parts_[3]) if len(parts_) > 3 else None
        C = certify(k, gr, gm, dm)
        if not C.get('gstar'):
            print(arg, C); continue
        print('k = %d gmin = %s mono = %s: gamma* = %s (root of %s) | identity %s | CERTIFIED %s' % (k, gm, dm, C['gs'], sp.factor(C['LB']), C['ident'], C['ok']))
        for nm, expr, val, gd in C['mult']:
            print('    %-40s %s   (at g*: %.4e, > 0: %s)' % (str(nm), expr, val, gd))
