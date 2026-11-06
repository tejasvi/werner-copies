"""Degree in n of the selected equality columns (must be <= 3 so that E(n)/n^3 is a polynomial in s) and of the objective
(c(n) n^12 must be a polynomial of degree <= 24... i.e. c a polynomial in s of degree <= 12): exact finite differences."""
import sys, pickle
sys.path.insert(0, '<ROOT>/dim')
sys.path.insert(0, '<ROOT>/dim/uni')
import numpy as np
from fractions import Fraction
from polytables import PolyEqualities, PolyTables
from exact_cert import word_orbits, orbit_sums, FAMILIES
from run_exact import lam_column_exact
sel = pickle.load(open('<ROOT>/dim/ac/rel31.pkl', 'rb'))['sel_eq']
orb = {f: word_orbits(3, f) for f in FAMILIES}
ns = list(range(4, 10))
cols = {}
for n in ns:
    EQ = PolyEqualities(3, n)
    cols[n] = np.array([lam_column_exact(EQ, orb, g, tuple(o)) for (g, o) in sel], dtype=object)
# 4th finite difference over n=4..8 and n=5..9 must vanish (degree <= 3)
def diff(vals):
    while len(vals) > 1:
        vals = [b - a for a, b in zip(vals, vals[1:])]
    return vals[0]
d4a = diff([cols[n] for n in ns[:5]]); d4b = diff([cols[n] for n in ns[1:]])
print('equality columns: 4th differences vanish: %s %s' % (not (d4a != 0).any(), not (d4b != 0).any()))
# objective: c(n) * n^12 * 128 = polynomial of degree <= 12 in n ... check 13th difference on 14 points
cvals = []
for n in range(4, 19):
    T = PolyTables(3, n)
    cT, cden = T.objective_table()
    v = orbit_sums(cT, *orb['31'])
    cvals.append(np.array([Fraction(int(x), int(cden)) * n ** 12 for x in v], dtype=object))
d13 = diff(cvals[:14]); d13b = diff(cvals[1:])
print('objective * n^12: 13th differences vanish: %s %s' % (not (d13 != 0).any(), not (d13b != 0).any()))
