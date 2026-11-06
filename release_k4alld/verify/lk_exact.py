# exact recomputation of the trace-slack constant LK(n) = 16 (n^4 ||G_site(n)^-1||_inf)^4 ||G_aux^+||_inf
import itertools, sympy as sp
from fractions import Fraction
P4 = list(itertools.permutations(range(4)))
def compose(p, q): return tuple(p[q[i]] for i in range(4))
def inverse(p):
    r = [0]*4
    for i, x in enumerate(p): r[x] = i
    return tuple(r)
def ncycles(p):
    seen, c = set(), 0
    for i in range(4):
        if i not in seen:
            c += 1; j = i
            while j not in seen: seen.add(j); j = p[j]
    return c
Ga = sp.Matrix(24, 24, lambda i, j: 2**ncycles(compose(inverse(P4[i]), P4[j])))
print('rank Ga', Ga.rank())
Gp = Ga.pinv()
nGa = max(sum(abs(Gp[i, j]) for j in range(24)) for i in range(24))
print('||Ga^+||_inf =', nGa, '=', float(nGa))
# site Neumann bound at n0
cnt = {}
for p in P4:
    if p != (0,1,2,3): cnt[ncycles(p)] = cnt.get(ncycles(p), 0) + 1
print('cycle counts of non-identity perms', cnt)
n0 = Fraction(1250000000)
eps = Fraction(6)/n0 + Fraction(11)/n0**2 + Fraction(6)/n0**3
LK = 16 * Fraction(str(nGa)) if False else None
LKq = 16 * sp.Rational(nGa) * (1/(1 - sp.Rational(eps.numerator, eps.denominator)))**4
print('LK(n0) exact bound =', float(LKq))
# also verify for a small n that n^4 ||G_site(n)^-1||_inf <= 1/(1-eps(n)) numerically exactly at n=5,7
for n in (4, 5, 7, 11):
    G = sp.Matrix(24, 24, lambda i, j: sp.Integer(n)**ncycles(compose(inverse(P4[i]), P4[j])))
    Gi = G.inv()
    val = n**4 * max(sum(abs(Gi[i, j]) for j in range(24)) for i in range(24))
    e = sp.Rational(6, n) + sp.Rational(11, n**2) + sp.Rational(6, n**3)
    print('n', n, 'n^4||Gsite^-1||_inf =', float(val), ' Neumann bound', float(1/(1-e)) if e < 1 else 'n/a', ' ok' if (e >= 1 or val <= 1/(1-e)) else ' FAIL')
