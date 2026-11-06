#!/usr/bin/env python
"""All-k profile-LP certificates for Theorem 9.2 of the paper, written to a JSON certificate file that allk_check.py re-checks
exactly (no LP there):
  q_k(X/k, C) >= 0 for every k >= k0, every C of rank at most two, every d.
Rows: profile_lp_k5.rows_exact (inputs (I2)-(I5); (I6) iff --k5).
(A) k0 <= k < J: per-k LP at g = X/k on rows_exact(k); certificate y_k (rows of total size <= k).
(B) J <= k <= K: limit certificate y_inf (objective e_j = (-X)^j/j!, rows of size <= J), per-k certificates where y_inf fails.
(C) k > K: slack >= delta_inf - E2/k - 2 TAIL.
usage: allk_dump.py X J k0 OUT.json [--k5]"""
import os, sys, json, time
from fractions import Fraction as Fr
from math import comb, factorial, ceil
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # python -I does not add the script dir
from profile_lp_k5 import rows_exact as _rows_exact

X = Fr(sys.argv[1]); J = int(sys.argv[2]); K0 = int(sys.argv[3]); OUT = sys.argv[4]; K5 = '--k5' in sys.argv
rows_exact = lambda k: _rows_exact(k, None, k5=K5)


def lp_duals(R, obj):
    A = -np.array([[float(v) for v in r] for _, r in R])
    n = len(obj)
    res = linprog(np.array([float(c) for c in obj]), A_ub=A, b_ub=np.zeros(len(R)), bounds=[(1, 1)] + [(0, 2)] * (n - 1),
                  method='highs')
    y = -res.ineqlin.marginals
    return {i: Fr(float(v)).limit_denominator(10 ** 15) for i, v in enumerate(y) if v > 1e-14}


def slack(R, y, obj, n):
    r = list(obj[:n + 1]) + [Fr(0)] * max(0, n + 1 - len(obj))
    for i, yi in y.items():
        for j, v in enumerate(R[i][1]):
            r[j] -= yi * v
    return r[0] + 2 * sum(min(Fr(0), v) for v in r[1:])


def cvec(k, g, upto):
    return [Fr(comb(k, j)) * (-g) ** j for j in range(min(k, upto) + 1)]


def enc(R, y):
    return [[list(R[i][0]), str(yi)] for i, yi in sorted(y.items())]


t0 = time.time()
TAIL = X ** (J + 1) / factorial(J + 1) / (1 - X / (J + 2))
cert = dict(X=str(X), J=J, k0=K0, k5=K5, TAIL=str(TAIL), A={}, B={})
for k in range(K0, J):
    Rk = rows_exact(k)
    obj = cvec(k, X / k, k)
    y = lp_duals(Rk, obj)
    s = slack(Rk, y, obj, k)
    assert s > 0, (k, float(s))
    cert['A'][k] = enc(Rk, y)
R = rows_exact(J)
e = [(-X) ** j / factorial(j) for j in range(J + 1)]
yinf = lp_duals(R, e)
dinf = slack(R, yinf, e, J)
E2 = sum(X ** j / factorial(j - 2) for j in range(2, J + 1, 2))
K = ceil(E2 / (dinf - 2 * TAIL))
cert.update(yinf=enc(R, yinf), K=K, E2=str(E2), delta_inf=str(dinf))
Ract = [R[i] for i in sorted(yinf)]
for k in range(J, K + 1):
    obj = cvec(k, X / k, J)
    if slack(R, yinf, obj, J) - 2 * TAIL > 0:
        continue
    yk = lp_duals(Ract, obj); RR = Ract
    if slack(RR, yk, obj, J) - 2 * TAIL <= 0:
        yk = lp_duals(R, obj); RR = R
    assert slack(RR, yk, obj, J) - 2 * TAIL > 0, k
    cert['B'][k] = enc(RR, yk)
json.dump(cert, open(OUT, 'w'))
print('X = %s J = %d k0 = %d k5 = %s: A %d certificates, K = %d, B fixes %d, delta_inf %.4e -> %s (%.0fs)' % (
    X, J, K0, K5, len(cert['A']), K, len(cert['B']), float(dinf), OUT, time.time() - t0), flush=True)
