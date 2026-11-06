"""Anchor-relative float columns WITH rigorous componentwise error bounds at local dimension n.
Relative Gram column of Y-entry (a,b) of type t: table of B = n^{-2F_t} (WL)(E_ab + E_ba)(WL)^T, WL = W_t L_t
(L_t = exact binary rational value of the float matrix in rel2).  Bound: |fl - exact| <= GAMMA * M where M is the same
computation on absolute values with |V| and |FT| (all terms nonnegative), GAMMA = 1e-13 (covering the
4 mode products (inner dim <= 60), the orbit sums (<= 432 terms), the outer product, FT/V rounding and scalings:
<= 750 u = 8.4e-14).
Equality columns (selected, scaled n^-3) and the objective are exact -> float (relative error <= u).
Usage: dumpcols_rel.py n rel2.pkl rel31b.pkl out.npz"""
import sys, pickle, time
sys.path.insert(0, '<ROOT>/dim')
sys.path.insert(0, '<ROOT>/dim/uni')
import numpy as np
from fractions import Fraction
from polytables import PolyTables, PolyEqualities
from exact_cert import word_orbits, osum_float, orbit_sums, W_of, family_tables, FAMILIES
from run_exact import lam_column_exact

n = int(sys.argv[1]); rel2 = pickle.load(open(sys.argv[2], 'rb')); relb = pickle.load(open(sys.argv[3], 'rb')); outp = sys.argv[4]
t0 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
types = pickle.load(open('<ROOT>/dim/runs/exact_types2_k3_d6.pkl', 'rb'))
Nref = pickle.load(open('<ROOT>/dim/runs/red2_k3_d6.pkl', 'rb'))['N']
kept, F = rel2['kept'], rel2['F']
k = 3
tabs = PolyTables(k, n)
tabs_abs = PolyTables(k, n)
for key, loc in tabs_abs.loc.items():
    loc.FT = np.abs(np.array(loc.FT, dtype=object))
EQ = PolyEqualities(k, n)
orb = {f: word_orbits(k, f) for f in FAMILIES}
# V_t = W_t L_t computed EXACTLY (W integer, L = Lnum/Lden binary rational), then correctly rounded: no cancellation
# in the error bounds (|V_exact - V_float| <= u |V_float|, absorbed in GAMMA).
W, Wa = [None] * len(types), [None] * len(types)
Lden = relb['Lden']
for ti in kept:
    Wi = W_of(types[ti], Nref[ti])
    Ln = np.array(relb['Lnum'][ti], dtype=object)
    Vex = Wi.dot(Ln)
    V = np.array([[float(Fraction(int(x), Lden)) for x in row] for row in Vex])
    W[ti] = V
    Wa[ti] = np.abs(V) * (1 + 4.0 * 2.0 ** -53)
cols, bnds, idx = [], [], []
for ti in kept:
    r = W[ti].shape[1]
    sc = float(n) ** (-2 * F[ti])
    for a in range(r):
        for b in range(a, r):
            E = np.zeros((r, r)); E[a, b] = 1; E[b, a] = 1
            Zl = [None] * len(types); Zl[ti] = E
            T = family_tables(tabs, types, W, Zl, float_mode=True)
            Ta = family_tables(tabs_abs, types, Wa, Zl, float_mode=True)
            cols.append(sc * np.concatenate([osum_float(T[f], *orb[f]) if T[f] is not None else np.zeros(orb[f][1]) for f in FAMILIES]))
            bnds.append(sc * np.concatenate([osum_float(Ta[f], *orb[f]) if Ta[f] is not None else np.zeros(orb[f][1]) for f in FAMILIES]))
            idx.append((ti, a, b))
    if len(idx) % 2000 < r * (r + 1) // 2:
        log('%d columns' % len(idx))
Rc = np.array(cols).T; Rb = np.array(bnds).T
log('relative Gram columns %s' % (Rc.shape,))
Ecols = []
for (g, o) in relb['sel_eq']:
    col = lam_column_exact(EQ, orb, g, tuple(o))
    Ecols.append([float(Fraction(int(x), n ** 3)) for x in col])
Ec = np.array(Ecols).T
cT, cden = tabs.objective_table()
c = np.concatenate([np.array([float(Fraction(int(x), int(cden))) for x in orbit_sums(cT, *orb[f])]) if f == '31' else np.zeros(orb[f][1]) for f in FAMILIES])
np.savez(outp, R=Rc, Rbound=Rb * 1e-13, E=Ec, c=c, idx=np.array(idx))
log('saved %s' % outp)
