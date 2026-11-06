"""Rigorous strict PD of relcert2 Y blocks without huge exact determinants:
Y = Yround + Delta, Yround = Yint/2^bits (exact, small denominators).  Bound ||Delta||_2 <= ||Delta||_F <= mu (float with
upward safety), then EXACT Sylvester on Yround - mu I.  Yround - mu I > 0  =>  Y >= Yround - ||Delta|| I > 0."""
import sys, pickle, math, flint
from fractions import Fraction
D0 = '<ROOT>/dim'
kref = list(pickle.load(open(D0 + '/runs/red2_k3_d6.pkl', 'rb'))['type_index'])
def spd_shift(Yr, mu):
    m = len(Yr)
    M = flint.fmpq_mat(m, m, [flint.fmpq(Yr[i][j].numerator, Yr[i][j].denominator) - (flint.fmpq(mu.numerator, mu.denominator) if i == j else 0)
                             for i in range(m) for j in range(m)])
    for k in range(1, m + 1):
        if flint.fmpq_mat(k, k, [M[i, j] for i in range(k) for j in range(k)]).det() <= 0:
            return False
    return True
for p in sys.argv[1:]:
    c = pickle.load(open(p, 'rb'))
    bits = c['bits']; bad = []; worst_mu = 0.0
    for ti in c['kept']:
        Y = c['Y'][ti]; m = len(Y)
        sym = all(Y[a][b] == Y[b][a] for a in range(m) for b in range(a))
        Yr = [[Fraction(round(Y[a][b] * 2 ** bits), 2 ** bits) for b in range(m)] for a in range(m)]
        Yr = [[(Yr[a][b] + Yr[b][a]) / 2 for b in range(m)] for a in range(m)]
        s = 0.0
        for a in range(m):
            for b in range(m):
                dlt = abs(float(Y[a][b] - Yr[a][b]))
                s += (dlt * (1 + 2.0 ** -50)) ** 2
        mu = Fraction(math.sqrt(s * (1 + m * m * 2.0 ** -50)) * 1.001) + Fraction(1, 2 ** 1000)   # exact binary upper bound
        worst_mu = max(worst_mu, float(mu))
        if not (sym and spd_shift(Yr, mu)):
            bad.append(ti)
    print('%s: n=%s consistent=%s kept==red2_d6: %s; rigorous strict PD failures %d of %d (max ||Delta||_F bound %.2e)' %
          (p.split('/')[-1], c['n'], c['consistent'], list(c['kept']) == kref, len(bad), len(c['kept']), worst_mu), flush=True)
