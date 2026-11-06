"""Independent cross-check (mod two 61-bit primes) of a relative node certificate converted to the W basis:
Z_t = n^{-2F_t} L_t Y_t L_t^T,  c = sum_t A_t(Z_t) + sum_e lam_e E_e  on every orbit row (exact integer tables mod p)."""
import sys, pickle
from fractions import Fraction
sys.set_int_max_str_digits(0)
sys.path.insert(0, '<ROOT>/dim')
sys.path.insert(0, '<ROOT>/dim/uni')
import numpy as np
from polytables import PolyTables, PolyEqualities
from exact_cert import word_orbits, orbit_sums, W_of, family_tables, FAMILIES
from run_exact import lam_column_exact
cert = pickle.load(open(sys.argv[1], 'rb'))
n = cert['n']
D0 = '<ROOT>/dim/'
types = pickle.load(open(D0 + 'runs/exact_types2_k3_d6.pkl', 'rb'))
Nref = pickle.load(open(D0 + 'runs/red2_k3_d6.pkl', 'rb'))['N']
F = pickle.load(open(D0 + 'ac/rel2_31.pkl', 'rb'))['F']
tabs = PolyTables(3, n); EQ = PolyEqualities(3, n)
orb = {f: word_orbits(3, f) for f in FAMILIES}
cT, cden = tabs.objective_table()
cvec = np.concatenate([orbit_sums(cT, *orb[f]) if f == '31' else np.zeros(orb[f][1], dtype=object) for f in FAMILIES])
lamcols = {key: lam_column_exact(EQ, orb, key[0], tuple(key[1])) for key in cert['lam']}
for p in (2 ** 61 - 1, 2 ** 61 - 1 - 2 * 15):
    md = lambda x: (Fraction(x).numerator % p) * pow(Fraction(x).denominator % p, -1, p) % p
    Wl = [None] * len(types); Zi = [None] * len(types)
    for ti in cert['kept']:
        Ln = np.array(cert['Lnum'][ti], dtype=object)
        Ym = np.array([[md(x) for x in row] for row in cert['Y'][ti]], dtype=object)
        inv_sc = pow((4 ** cert['E'][ti] * n ** (2 * F[ti])) % p, -1, p)
        Zi[ti] = (Ln.dot(Ym).dot(Ln.T) * inv_sc) % p
        Wl[ti] = W_of(types[ti], Nref[ti])
    T = family_tables(tabs, types, Wl, Zi)
    gram = np.concatenate([orbit_sums(T[f], *orb[f]) for f in FAMILIES])
    inv_cden = pow(int(cden) % p, -1, p)
    res = [(int(cvec[i]) * inv_cden - int(gram[i])) % p for i in range(len(cvec))]
    for key, lam in cert['lam'].items():
        lm = md(lam)
        col = lamcols[key]
        for i in range(len(res)):
            if col[i]:
                res[i] = (res[i] - lm * int(col[i])) % p
    bad = sum(1 for x in res if x != 0)
    print('n=%d p=%d: nonzero residual rows mod p: %d -> %s' % (n, p, bad, 'OK' if bad == 0 else 'FAIL'), flush=True)
