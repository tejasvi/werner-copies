"""Exact rank over Q of the 107 tau generators (dim/lk/tau_exact2.pkl), recomputed independently with flint."""
import pickle, flint
from fractions import Fraction
d = pickle.load(open('<ROOT>/dim/lk/tau_exact2.pkl', 'rb'))
rows = [[Fraction(x) for x in r] for r in d['tau']]
M = flint.fmpq_mat(len(rows), len(rows[0]), [flint.fmpq(x.numerator, x.denominator) for r in rows for x in r])
print('tau generators: %d x %d, exact rank over Q = %d (stored %s); kinds: %s' % (len(rows), len(rows[0]), M.rank(), d.get('rank'),
      sorted(set((s['kind'], s.get('J'), s['gen']) for s in d['specs']))[:12]))
