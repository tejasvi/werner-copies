"""Degree facts used by the left-kernel argument:
 (1) D(n) Wg(n) is a polynomial matrix of degree <= 4, D(n) = n^2 (n^2-1)(n^2-4)(n^2-9), Wg = inverse S_4 Gram
     [n^{cycles(v^-1 w)}]  (exact: interpolate on n = 4..12 and check two more points; plus the character formula).
 (2) every label row block of FT_poly has degree <= 2 f(label) in n (exact coefficients of ftpoly).
 (3) max over kept types of 12 + 2 F_t (numerator degree bound)."""
import sys, pickle
sys.path.insert(0, '<ROOT>/dim')
import flint
from fractions import Fraction
from local import compose, inverse, ncycles, perms
P4 = perms(4)


def DWg(n):
    G = flint.fmpq_mat(24, 24, [n ** ncycles(compose(inverse(v), w)) for v in P4 for w in P4])
    Gi = G.inv()
    D = n * n * (n * n - 1) * (n * n - 4) * (n * n - 9)
    return [[Gi[i, j] * D for j in range(24)] for i in range(24)]


vals = {n: DWg(n) for n in range(4, 15)}
ok = True
maxdeg = 0
for i in range(24):
    for j in range(24):
        xs = list(range(4, 13))
        # Newton divided differences on 9 points -> degree <= 8 representation; check degree <= 4 and two extra points
        ys = [Fraction(int(vals[n][i][j].p), int(vals[n][i][j].q)) for n in xs]
        coef = list(ys)
        for kk in range(1, len(xs)):
            for m in range(len(xs) - 1, kk - 1, -1):
                coef[m] = (coef[m] - coef[m - 1]) / (xs[m] - xs[m - kk])
        deg = max([kk for kk in range(len(coef)) if coef[kk] != 0] + [0])
        maxdeg = max(maxdeg, deg)
        for n in (13, 14):
            v = coef[-1]
            for m in range(len(xs) - 2, -1, -1):
                v = v * (n - xs[m]) + coef[m]
            if v != Fraction(int(vals[n][i][j].p), int(vals[n][i][j].q)):
                ok = False
print('(1) D(n) Wg(n): max degree %d, consistent at n=13,14: %s' % (maxdeg, ok))
FTP = pickle.load(open('<ROOT>/dim/uni/ftpoly.pkl', 'rb'))
bad = 0
for cut, P in FTP.items():
    for li, lab in enumerate(P['labels']):
        rows = range(P['off'][li], P['off'][li + 1])
        dmax = max([kk for kk in range(5) if any(P['coef'][kk][r][p] != 0 for r in rows for p in range(24))] + [0])
        if dmax > 2 * lab[0]:
            bad += 1
            print('   cut %s label %s: degree %d > 2f' % (cut, lab, dmax))
print('(2) label blocks with degree > 2f: %d' % bad)
types = pickle.load(open('<ROOT>/dim/runs/exact_types2_k3_d6.pkl', 'rb'))
kept = pickle.load(open('<ROOT>/dim/runs/red2_k3_d6.pkl', 'rb'))['type_index']
Fm = max(sum(FTP[types[ti]['cut']]['labels'][li][0] for li in types[ti]['st']) for ti in kept)
print('(3) max F_t over kept types = %d -> numerator degree bound 12 + 2F = %d' % (Fm, 12 + 2 * Fm))
