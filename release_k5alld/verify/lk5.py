"""Exact trace-slack constant for k = 5 (own implementation).
|x_w| <= ||G^+||_inf max_v |g_v| with x = G^+ g, G = (x)_l G_site(n) (x) G_a, |g_v| = |<psi|V_v^*|psi>| <= Tr X_f = 1
(||a|| = ||b|| = 1) and Tr X_31 = 16 n^20 tau(x) give |x_w| <= LK(n) tau(x),
    LK(n) = 16 (n^4 ||G_site(n)^-1||_inf)^5 ||G_a^+||_inf <= 16 ||G_a^+||_inf / (1 - eps(n))^5,
eps(n) = 6/n + 11/n^2 + 6/n^3 = off-diagonal row sum of G_site(n)/n^4 (Neumann series).
Usage: lk5.py s0 out.pkl     (s0 = 1/d0)
"""
import os, sys, pickle
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
import sympy as sp
import k5defs as KD

s0 = Fraction(sys.argv[1])
Ga = KD.gram(KD.P4, 2)
GaS = sp.Matrix(Ga.tolist())
print('rank G_a =', GaS.rank())
Gp = GaS.pinv()
assert GaS * Gp * GaS == GaS and Gp * GaS * Gp == Gp and (GaS * Gp).T == GaS * Gp and (Gp * GaS).T == Gp * GaS
nGa = max(sum(abs(Gp[i, j]) for j in range(24)) for i in range(24))
print('||G_a^+||_inf =', nGa, '=', float(nGa))
cnt = {}
for p in KD.P4:
    if p != (0, 1, 2, 3):
        c = KD.ncycles(p)
        cnt[c] = cnt.get(c, 0) + 1
print('cycle counts of non-identity permutations:', cnt)
assert cnt == {3: 6, 2: 11, 1: 6}
eps = 6 * s0 + 11 * s0 ** 2 + 6 * s0 ** 3
LK = 16 * Fraction(int(sp.fraction(nGa)[0]), int(sp.fraction(nGa)[1])) / (1 - eps) ** KD.K
print('LK(s0 = %s) <= %s = %.12f' % (s0, 'exact rational', float(LK)))
for n in (4, 5, 7, 11):
    G = sp.Matrix(24, 24, lambda i, j: sp.Integer(n) ** KD.ncycles(KD.compose(KD.inverse(KD.P4[i]), KD.P4[j])))
    Gi = G.inv()
    val = n ** 4 * max(sum(abs(Gi[i, j]) for j in range(24)) for i in range(24))
    e = sp.Rational(6, n) + sp.Rational(11, n ** 2) + sp.Rational(6, n ** 3)
    ok = (e >= 1) or (val <= 1 / (1 - e))
    print('n = %d: n^4 ||G_site^-1||_inf = %.6f, Neumann bound %s %s' % (n, float(val), '%.6f' % float(1 / (1 - e)) if e < 1 else 'n/a', 'OK' if ok else 'FAIL'))
    assert ok
pickle.dump(dict(s0=s0, LK=LK, nGa=Fraction(int(sp.fraction(nGa)[0]), int(sp.fraction(nGa)[1]))), open(sys.argv[2], 'wb'))
