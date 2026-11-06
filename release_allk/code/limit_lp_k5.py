#!/usr/bin/env python
"""k -> infinity limit of the profile LP with inputs (I2)-(I6) (profile_lp_k5.rows_float): q_k(x/k) -> sum_j (-x)^j a_j / j!.
Rows = every base inequality with frozen copies / compressed sets of total size <= J (valid for every k >= J by Lemma 9.1).
Prints the threshold c*_J = largest x for which the LP minimum of the degree-J truncation is >= 0, and the minimum delta(x) at
the given x values.  c*_J increases towards 9/4 (Proposition 9.3).  usage: limit_lp_k5.py J1,J2,... [x1,x2,...]"""
import os, sys
from math import factorial
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # python -I does not add the script dir
from profile_lp_k5 import rows_float
for J in [int(s) for s in sys.argv[1].split(',')]:
    A = rows_float(J, None, k5=True)
    def mn(x):
        obj = np.array([(-x) ** j / factorial(j) for j in range(J + 1)])
        r = linprog(obj, A_ub=A, b_ub=np.zeros(len(A)), bounds=[(1, 1)] + [(0, 2)] * J, method='highs')
        return r.fun if r.status == 0 else -9
    lo, hi = 1.0, 3.0
    for _ in range(40):
        mid = (lo + hi) / 2
        if mn(mid) >= -1e-12: lo = mid
        else: hi = mid
    xs = [float(v) for v in sys.argv[2].split(',')] if len(sys.argv) > 2 else []
    print('J = %2d rows %d: c*_J = %.6f | ' % (J, len(A), lo) + ' '.join('delta(%.3f) = %.5f' % (x, mn(x)) for x in xs), flush=True)
