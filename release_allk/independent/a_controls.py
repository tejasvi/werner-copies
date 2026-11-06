#!/usr/bin/env python3
"""Controls for a_cert.py (imported from this directory).
(1) every row (total size <= 14, K5 included) is >= 0 at the profile P'' = (1, 4/9, 0, ...) of Proposition 9.3(b);
    every non-K5 row is >= 0 at P' = (1, 40/79, 0, ...), the same point for (I1)-(I5).  A negative value would expose a mis-coded row.
(2) negative controls: the LP must FAIL (a) without K5 rows at X = 11/5 (k = 6, 9 and the J = 12 limit), and
    (b) with K5 rows at X = 113/50 > 9/4 (k = 9 and the J = 12 limit).
(3) numerical sanity of the row encoding on random rank-2 C, k = 7 qubits: profile a_j from all partial traces;
    q_7(t) from the profile equals sum_J (-t)^|J| ||Tr_J C||^2; the rows used in the certificates are >= 0.
"""
import os, sys, math, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from fractions import Fraction as Fr
import a_cert as A

def main():
    # (1)
    labs, R = A.build_rows(14, True)
    P2 = [Fr(1), Fr(4, 9)] + [Fr(0)] * 13
    vals = [sum(r[j] * P2[j] for j in range(15)) for r in R]
    i = min(range(len(R)), key=lambda t: vals[t])
    print('(1) rows <= 14 (with K5): %d; min value at P\'\' = %s (%s)  -> %s' % (len(R), vals[i], labs[i],
          'OK' if vals[i] >= 0 else 'NEGATIVE ROW'), flush=True)
    labs0, R0 = A.build_rows(14, False)
    P1 = [Fr(1), Fr(40, 79)] + [Fr(0)] * 13
    vals0 = [sum(r[j] * P1[j] for j in range(15)) for r in R0]
    i0 = min(range(len(R0)), key=lambda t: vals0[t])
    print('(1) rows <= 14 (no K5): %d; min value at P\' = %s (%s)  -> %s' % (len(R0), vals0[i0], labs0[i0],
          'OK' if vals0[i0] >= 0 else 'NEGATIVE ROW'), flush=True)
    # (2)
    for (X, use_k5, ks) in [(Fr(11, 5), False, [6, 9]), (Fr(113, 50), True, [9])]:
        for k in ks:
            labs, R = A.build_rows(k, use_k5)
            Rf = np.array([[float(v) for v in row] for row in R])
            lp, y = A.solve_lp(Rf, np.array([float(v) for v in A.b_exact(X, k, k)]))
            print('(2) X = %s, K5 rows %s, k = %d: LP optimum (min q) = %.6e -> %s' % (X, use_k5, k, lp,
                  'FAILS as it must' if lp < 0 else 'UNEXPECTED PASS'), flush=True)
        labs, R = A.build_rows(12, use_k5)
        Rf = np.array([[float(v) for v in row] for row in R])
        bw = A.b_worst(X, 10 ** 12, None, 12)
        lp, y = A.solve_lp(Rf, np.array([float(v) for v in bw]))
        lp -= 2 * float(A.tail_bound(X, 12))
        print('(2) X = %s, K5 rows %s, J = 12 limit: LP optimum = %.6e -> %s' % (X, use_k5, lp,
              'FAILS as it must' if lp < 0 else 'UNEXPECTED PASS'), flush=True)
    # (3)
    rng = np.random.default_rng(918)
    k, d = 7, 2
    D = d ** k
    used = ['K5(1, 1, 1, 1, 1)', 'K5(1, 1, 1, 1, 1)+c[2]', 'K4(1, 1, 1, 1)+c[3]', 'FHPV(2,2)+c[1, 1, 1]', 'TB(6)',
            'EP3(2, 1, 1)+c[2]', 'CR(1,2)+c[2, 2]', 'CR(2,1)+c[3]']
    labs, R = A.build_rows(k, True)
    lab2row = dict(zip(labs, R))
    worst = {u: 1e9 for u in used}
    maxdev = 0.0
    for trial in range(30):
        u = rng.normal(size=(D, 2)) + 1j * rng.normal(size=(D, 2))
        v = rng.normal(size=(D, 2)) + 1j * rng.normal(size=(D, 2))
        if trial % 3 == 1:  # near-PSD
            v = u + 0.1 * v
        C = u @ v.conj().T
        T = C.reshape([d] * (2 * k))
        aJ = {}
        for mask in range(1 << k):
            Jset = [m for m in range(k) if mask >> m & 1]
            X = T
            # trace site m: axes m (row) and k+m (col); trace from the highest index down
            rows_left = list(range(k))
            Y = T
            nrow = k
            ax = sorted(Jset, reverse=True)
            for m in ax:
                Y = np.trace(Y, axis1=m, axis2=m + nrow)
                nrow -= 1
            aJ[mask] = float(np.sum(np.abs(Y) ** 2))
        N = aJ[0]
        a = [np.mean([aJ[m] for m in range(1 << k) if bin(m).count('1') == j]) / N for j in range(k + 1)]
        t = 0.37
        q_direct = sum((-t) ** bin(m).count('1') * aJ[m] for m in range(1 << k)) / N
        q_prof = sum(math.comb(k, j) * (-t) ** j * a[j] for j in range(k + 1))
        maxdev = max(maxdev, abs(q_direct - q_prof))
        for ulab in used:
            r = lab2row.get(ulab)
            if r is None:
                continue
            val = sum(float(r[j]) * a[j] for j in range(k + 1))
            worst[ulab] = min(worst[ulab], val)
        if trial == 0:
            print('(3) sample profile a_j (k = 7 qubits):', ' '.join('%.4f' % x for x in a), flush=True)
    print('(3) max |q_direct - q_profile| over 30 random rank-2 C: %.2e' % maxdev, flush=True)
    for ulab in used:
        print('(3) min over samples of row %-28s = %.5f %s' % (ulab, worst[ulab], 'OK' if worst[ulab] >= -1e-12 else
              'NEGATIVE'), flush=True)
    print('CONTROLS DONE', flush=True)

if __name__ == '__main__':
    main()
