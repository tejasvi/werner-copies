"""Exact strictly-PD node certificate in anchor-relative coordinates with moderate integers.
  Z_t = L_t Y_t L_t^T / n^{2F_t},  L_t = Lnum_t / 2^{E_t}  (per-type 40-bit rounding of the accurate relative metric).
Selected Gram columns are integer tables of W Lnum E Lnum^T W^T (no n factors): true column = col_int / (4^{E_t} n^{2F_t}).
Y is rounded from the analytic centre at n (2^-bits), corrected exactly on the fixed selection (rel31.pkl), PD checked exactly.
Usage: run_exact_rel2.py n acx.pkl out.pkl [bits]"""
import math, pickle, sys, time, os
from fractions import Fraction
sys.set_int_max_str_digits(0)
import numpy as np
import scipy.linalg as sla
import flint
sys.path.insert(0, '<ROOT>/dim')
sys.path.insert(0, '<ROOT>/dim/uni')
from polytables import PolyTables, PolyEqualities
from exact_cert import word_orbits, orbit_sums, W_of, family_tables, FAMILIES
from run_exact import lam_column_exact


def strictly_pd(Y):
    n = len(Y)
    den = 1
    for row in Y:
        for x in row:
            den = den * x.denominator // math.gcd(den, x.denominator)
    M = flint.fmpz_mat(n, n, [int(x * den) for row in Y for x in row])
    for k in range(1, n + 1):
        if flint.fmpz_mat(k, k, [M[i, j] for i in range(k) for j in range(k)]).det() <= 0:
            return False
    return True


def main():
    n = int(sys.argv[1]); ac = pickle.load(open(sys.argv[2], 'rb')); outp = sys.argv[3]
    bits = int(sys.argv[4]) if len(sys.argv) > 4 else 50
    k = 3
    t0 = time.time()
    log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
    D0 = '<ROOT>/dim/'
    types = pickle.load(open(D0 + 'runs/exact_types2_k3_d6.pkl', 'rb'))
    rel2 = pickle.load(open(D0 + 'ac/rel2_31.pkl', 'rb'))
    sel = pickle.load(open(D0 + 'ac/rel31.pkl', 'rb'))
    kept, F = rel2['kept'], rel2['F']
    assert list(ac['type_index']) == list(kept)
    tabs = PolyTables(k, n)
    EQ = PolyEqualities(k, n)
    orb = {f: word_orbits(k, f) for f in FAMILIES}
    nrows = sum(orb[f][1] for f in FAMILIES)
    Et, Ln, Wp, Yint = {}, {}, [None] * len(types), [None] * len(types)
    for ti, Zac in zip(kept, ac['Z_exact_basis']):
        L = rel2['L'][ti]
        E = 40 - int(math.floor(math.log2(np.abs(L).max())))
        Et[ti] = E
        Ln[ti] = np.array([[int(round(x * 2.0 ** E)) for x in row] for row in L], dtype=object)
        Lf = Ln[ti].astype(float) / 2.0 ** E
        W = W_of(types[ti], ac['N'][ti])
        Wp[ti] = W.dot(Ln[ti])
        Y = np.linalg.solve(Lf, np.linalg.solve(Lf, Zac * float(n) ** (2 * F[ti])).T).T
        Y = (Y + Y.T) / 2
        Yint[ti] = np.array([[int(round(Y[a, b] * 2 ** bits)) for b in range(Y.shape[1])] for a in range(Y.shape[0])], dtype=object)
    log('relative metric with per-type 40-bit rounding; Y rounded at 2^-%d' % bits)
    # residual: true Z_t = Wp_t Yint Wp_t^T / (2^bits 4^{E_t} n^{2F_t}); common denominator Dz
    Dz = 1
    for ti in kept:
        Dz = Dz * (4 ** Et[ti] * n ** (2 * F[ti])) // math.gcd(Dz, 4 ** Et[ti] * n ** (2 * F[ti]))
    Zsc = [None] * len(types)
    for ti in kept:
        Zsc[ti] = Yint[ti] * (Dz // (4 ** Et[ti] * n ** (2 * F[ti])))
    den = 2 ** bits * Dz
    T = family_tables(tabs, types, Wp, Zsc)
    cT, cden = tabs.objective_table()
    Dt = den * cden // math.gcd(den, cden)
    r = np.concatenate([orbit_sums((cT * (Dt // cden) if f == '31' else 0) - T[f] * (Dt // den), *orb[f]) for f in FAMILIES])
    log('exact residual; max |r|/D = %.3e' % (float(max(abs(int(x)) for x in r)) / Dt))
    sel_eq, sel_g = sel['sel_eq'], sel['sel_gram']
    ecols, fcols, scl = [], [], []
    if os.path.exists(outp + '.cols.pkl'):
        sv = pickle.load(open(outp + '.cols.pkl', 'rb'))
        ecols, fcols, scl, r, Dt = sv['ecols'], sv['fcols'], sv['scl'], sv['r'], sv['Dt']
        log('resumed exact columns and residual from %s.cols.pkl' % outp)
        sel_eq_iter, sel_g_iter = [], []
    else:
        sel_eq_iter, sel_g_iter = sel_eq, sel_g
    for (g, o) in sel_eq_iter:
        col = lam_column_exact(EQ, orb, g, tuple(o))
        ecols.append(col); fcols.append(np.array([float(x) for x in col])); scl.append(Fraction(1))
    for (ti, a, b) in sel_g_iter:
        rr = Wp[ti].shape[1]
        Em = np.zeros((rr, rr), dtype=object); Em[a, b] = 1; Em[b, a] = 1
        Zl = [None] * len(types); Zl[ti] = Em
        Tt = family_tables(tabs, types, Wp, Zl)
        col = np.concatenate([orbit_sums(Tt[f], *orb[f]) if Tt[f] is not None else np.zeros(orb[f][1], dtype=object) for f in FAMILIES])
        ecols.append(col); fcols.append(np.array([float(x) for x in col]))
        scl.append(Fraction(4 ** Et[ti] * n ** (2 * F[ti])))      # delta Y_ab = u * scl
    log('exact selected columns: %d equality + %d Gram' % (len(sel_eq), len(sel_g)))
    pickle.dump(dict(ecols=ecols, fcols=fcols, scl=scl, r=r, Dt=Dt), open(outp + '.cols.pkl', 'wb'), protocol=4)
    C = np.array(fcols).T
    cn = np.linalg.norm(C, axis=0); cn[cn == 0] = 1
    Qr, Rr, pr = sla.qr((C / cn).T, mode='economic', pivoting=True)
    rho = C.shape[1]
    rows = sorted(pr[:rho].tolist())
    Cex = np.array(ecols, dtype=object).T
    A = flint.fmpz_mat(rho, rho, [int(Cex[i, j]) for i in rows for j in range(rho)])
    bvec = flint.fmpq_mat(rho, 1, [flint.fmpq(int(r[i]), Dt) for i in rows])
    log('solving %d x %d (max entry bits %d)' % (rho, rho, max(int(abs(int(x))).bit_length() for x in Cex[rows].ravel())))
    u = flint.fmpq_mat(A).solve(bvec, algorithm='dixon')
    log('exact solve done')
    Cz = flint.fmpq_mat(flint.fmpz_mat(nrows, rho, [int(Cex[i, j]) for i in range(nrows) for j in range(rho)]))
    prod = Cz * u
    ok = all(prod[i, 0] == flint.fmpq(int(r[i]), Dt) for i in range(nrows))
    log('all-row exact consistency: %s' % ok)
    Yfin = {ti: [[Fraction(int(Yint[ti][a, b]), 2 ** bits) for b in range(Yint[ti].shape[1])] for a in range(Yint[ti].shape[0])] for ti in kept}
    lam = {}
    corr = 0.0
    for j in range(rho):
        uj = Fraction(int(u[j, 0].p), int(u[j, 0].q))
        if j < len(sel_eq):
            lam[(sel_eq[j][0], tuple(sel_eq[j][1]))] = uj
        else:
            ti, a, b = sel_g[j - len(sel_eq)]
            dy = uj * scl[j]
            corr = max(corr, abs(float(dy)))
            Yfin[ti][a][b] += dy
            if a != b:
                Yfin[ti][b][a] += dy
    log('max |exact correction of Y| = %.3e' % corr)
    # rigorous PD: Y = Yround + Delta;  lambda_min(Yround) (exact 2^-bits rationals, float + error bound) > ||Delta||_F
    bad = []
    for ti in kept:
        Yr = Yint[ti].astype(float) / 2.0 ** bits
        m = Yr.shape[0]
        lam_min = np.linalg.eigvalsh(Yr)[0] - 10 * m * m * 2.0 ** -53 * np.abs(Yr).max() - m * 2.0 ** -53 * np.abs(Yr).max()
        dF = math.sqrt(sum(float(abs(Yfin[ti][a][b] - Fraction(int(Yint[ti][a, b]), 2 ** bits))) ** 2 for a in range(m) for b in range(m))) * (1 + 1e-12)
        if not lam_min > dF:
            bad.append(ti)
    log('strict PD failures: %d of %d' % (len(bad), len(kept)))
    pickle.dump(dict(n=n, kept=kept, E=Et, Lnum={ti: [[int(x) for x in row] for row in Ln[ti]] for ti in kept},
                     Y=Yfin, lam=lam, consistent=ok,
                     pd_failures=bad, bits=bits, maxcorr=corr), open(outp, 'wb'), protocol=4)
    log('written %s' % outp)


if __name__ == '__main__':
    main()
