"""Independent check of the Lebesgue constants used in uniform_verify.py (mpmath 40 digits, fine grid + Markov bound)."""
import math
from fractions import Fraction
import mpmath as mp
mp.mp.dps = 40
H = Fraction(1, 17)
def cheb(M):
    return [Fraction(math.floor((float(H) / 2) * (1 - math.cos((2 * k + 1) * math.pi / (2 * M))) * 10 ** 15), 10 ** 15) for k in range(M)]
def leb(pts, grid):
    p = [mp.mpf(x.numerator) / x.denominator for x in pts]
    m = len(p); a, b = mp.mpf(0), mp.mpf(H.numerator) / H.denominator
    best = mp.mpf(0)
    for g in range(grid + 1):
        s = a + (b - a) * g / grid
        tot = mp.mpf(0)
        for j in range(m):
            v = mp.mpf(1)
            for i in range(m):
                if i != j:
                    v *= (s - p[i]) / (p[j] - p[i])
            tot += abs(v)
        best = max(best, tot)
    hstep = (b - a) / grid
    q = hstep / 2 * m * 2 * (m - 1) ** 2 / (b - a)       # Markov: |Lambda'| <= m * 2(m-1)^2/(b-a) * Lambda_max
    return best, best / (1 - q), q
for name, pts, grid in [('28 eval points', cheb(28), 60000), ('16 M nodes', cheb(16), 20000),
                        ('16 integer nodes', [Fraction(1, n) for n in [7061, 790, 288, 150, 93, 64, 48, 38, 31, 26, 23, 21, 20, 19, 18, 17]], 20000)]:
    g, ub, q = leb(pts, grid)
    print('%-18s grid max %.6f  rigorous upper bound %.6f (q=%.3e)' % (name, float(g), float(ub), float(q)), flush=True)
