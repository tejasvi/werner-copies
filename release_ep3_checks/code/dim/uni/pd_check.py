"""Exact strict positive definiteness of every multiplier of a certificate (charpoly sign pattern: all roots > 0)."""
import sys, pickle
import flint
from fractions import Fraction


def strictly_pd(Z):
    n = len(Z)
    M = flint.fmpq_mat(n, n, [flint.fmpq(Fraction(x).numerator, Fraction(x).denominator) for row in Z for x in row])
    for i in range(n):
        for j in range(i):
            if M[i, j] != M[j, i]:
                return False
    # Sylvester's criterion on leading principal minors (exact)
    for k in range(1, n + 1):
        S = flint.fmpq_mat(k, k, [M[i, j] for i in range(k) for j in range(k)])
        if S.det() <= 0:
            return False
    return True


if __name__ == '__main__':
    for path in sys.argv[1:]:
        c = pickle.load(open(path, 'rb'))
        bad = [i for i, Z in enumerate(c['Z']) if not strictly_pd(Z)]
        print('%s: d=%s, %d multipliers, consistent=%s, strictly PD failures: %d' % (path, c.get('d'), len(c['Z']), c.get('consistent'), len(bad)), flush=True)
