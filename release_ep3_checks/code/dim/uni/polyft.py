"""Exact polynomial-in-n representation of the local Fourier maps FT (J-coordinates, M(p) = J^T V_p^Gamma J)
for the site factors on the stable range n >= 4.  FTpoly[cut] = list of coefficient matrices (Fractions),
FT(n) = sum_k n^k FTpoly[cut][k].  Built by Lagrange interpolation on n = 4..8, checked on n = 9, 10."""
import sys, pickle
sys.path.insert(0, '<ROOT>/dim')
import numpy as np
from fractions import Fraction
from exact import ExactLocal

CUTS = [(), (3,), (0,), (2,), (0, 1), (0, 2), (2, 3)]
NS = [4, 5, 6, 7, 8]


def lagrange_coeffs(xs, ys):
    """coefficients c_0..c_{m-1} (Fractions) of the interpolating polynomial through (xs, ys)."""
    m = len(xs)
    coeffs = [Fraction(0)] * m
    for i in range(m):
        # basis polynomial l_i(x) = prod_{j != i} (x - x_j)/(x_i - x_j)
        num = [Fraction(1)]
        den = Fraction(1)
        for j in range(m):
            if j == i:
                continue
            num = [Fraction(0)] + num
            for k in range(len(num) - 1):
                num[k] -= xs[j] * num[k + 1]
            den *= (xs[i] - xs[j])
        for k in range(m):
            coeffs[k] += ys[i] * num[k] / den
    return coeffs


def build():
    out = {}
    for cut in CUTS:
        L = {n: ExactLocal(n, 4, cut) for n in NS + [9, 10]}
        D = L[4].D
        assert all(L[n].D == D and L[n].labels == L[4].labels for n in L)
        FT = {n: np.array(L[n].FT, dtype=object) for n in L}
        coef = np.zeros((5, D, 24), dtype=object)
        for a in range(D):
            for p in range(24):
                ys = [int(FT[n][a, p]) for n in NS]
                c = lagrange_coeffs(NS, [Fraction(y) for y in ys])
                for k in range(5):
                    coef[k, a, p] = c[k]
                for n in (9, 10):
                    assert sum(c[k] * n ** k for k in range(5)) == int(FT[n][a, p])
        dens = set(x.denominator for x in coef.ravel())
        out[cut] = dict(coef=coef, labels=L[4].labels, dims=L[4].dims, off=L[4].off, D=D)
        print('cut', cut, 'D', D, 'coefficient denominators', sorted(dens)[:8], 'max degree',
              max(k for k in range(5) if any(x != 0 for x in coef[k].ravel())), flush=True)
    return out


if __name__ == '__main__':
    out = build()
    pickle.dump(out, open('<ROOT>/dim/uni/ftpoly.pkl', 'wb'))
