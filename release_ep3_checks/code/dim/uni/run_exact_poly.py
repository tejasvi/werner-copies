"""Exact certificate: round numeric multipliers, correct exactly, check PSD.  Writes a certificate pickle."""
import math
import pickle
import sys
import time
from fractions import Fraction

import numpy as np
import scipy.linalg as sla
import flint

sys.path.insert(0, '<ROOT>/dim')
sys.path.insert(0, '<ROOT>/dim/uni')
from polytables import PolyTables, PolyEqualities
from exact_cert import (word_orbits, orbit_sums, osum_float, W_of, family_tables,
                        round_sym, charpoly_psd, ldl_psd, mode_product_int, FAMILIES)


def lam_columns_float(EQ, orb, k):
    """Float orbit-sum columns of all raw equality rows; returns (cols (rows x nrow), index list)."""
    cols, index = [], []
    for g in range(len(EQ.groups)):
        shp = EQ.row_shapes(g)
        for o in np.ndindex(*shp):
            col = []
            parts = {f: (S, A, sign) for f, S, A, sign in EQ.groups[g]['parts']}
            for f in FAMILIES:
                oid, n = orb[f]
                if f not in parts:
                    col.append(np.zeros(n))
                    continue
                S, A, sign = parts[f]
                T = np.array(float(sign))
                for l in range(k):
                    T = np.multiply.outer(T, S[o[l]].astype(float))
                T = np.multiply.outer(T, A[o[k]].astype(float))
                col.append(np.bincount(oid.ravel(), weights=T.ravel(), minlength=n))
            cols.append(np.concatenate(col))
            index.append((g, o))
    return np.array(cols).T, index


def lam_column_exact(EQ, orb, g, o):
    tb = EQ.row_tables(g, o)
    return np.concatenate([orbit_sums(tb[f], *orb[f]) if f in tb else np.zeros(orb[f][1], dtype=object)
                           for f in FAMILIES])


def direction_table(tabs, t, W, i, j, float_mode):
    r = W.shape[1]
    if float_mode:
        E = np.zeros((r, r))
    else:
        E = np.zeros((r, r), dtype=object)
    E[i, j] += 1
    E[j, i] += 1
    return E


def main():
    k, d = map(int, sys.argv[1].split(','))
    types = pickle.load(open(sys.argv[2], 'rb'))
    res = pickle.load(open(sys.argv[3], 'rb'))
    outp = sys.argv[4]
    bits = int(sys.argv[5]) if len(sys.argv) > 5 else 50
    ncand_types = int(sys.argv[6]) if len(sys.argv) > 6 else 10 ** 9
    t0 = time.time()
    log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
    tabs = PolyTables(k, d)
    EQ = PolyEqualities(k, d)
    orb = {f: word_orbits(k, f) for f in FAMILIES}
    nrows = sum(orb[f][1] for f in FAMILIES)
    log('orbits %s' % {f: orb[f][1] for f in FAMILIES})
    den = 2 ** bits
    kept = list(res['type_index'])
    Wint = [None] * len(types)
    Zint = [None] * len(types)
    Zf = {}
    for ti, Z in zip(kept, res['Z_exact_basis']):
        Wint[ti] = W_of(types[ti], res['N'][ti])
        Zs = (Z + Z.T) / 2
        Zint[ti] = np.array([[int(round(Zs[a, b] * den)) for b in range(Zs.shape[1])] for a in range(Zs.shape[0])], dtype=object)
        Zf[ti] = Zs
    # exact residual with rounded Z
    T = family_tables(tabs, types, Wint, Zint)
    cT, cden = tabs.objective_table()
    D = den * cden // math.gcd(den, cden)
    r = np.concatenate([orbit_sums((cT * (D // cden) if f == '31' else 0) - T[f] * (D // den), *orb[f]) for f in FAMILIES])
    log('exact residual computed; max |r|/D = %.3e' % (float(max(abs(int(x)) for x in r)) / D))
    # float candidate columns: equalities
    Lf, lidx = lam_columns_float(EQ, orb, k)
    log('equality columns %s' % (Lf.shape,))
    # float candidate columns: Gram entries of kept types, ordered by margin (largest min eig first)
    margins = []
    for ti in kept:
        w = np.linalg.eigvalsh(Zf[ti])
        # margin in the module-orthonormal metric is what matters; use min eig of the numeric D
        margins.append((ti, w.min() / max(w.max(), 1e-300)))
    Dmin = {ti: np.linalg.eigvalsh(Dm).min() for ti, Dm in zip(kept, res['D'])}
    order = sorted(kept, key=lambda ti: -Dmin[ti])[:ncand_types]
    cand_cols, cand_idx = [], []
    Wf = [None if w is None else w.astype(float) for w in Wint]
    for ti in order:
        t = types[ti]
        r_ = Wint[ti].shape[1]
        for a in range(r_):
            for b in range(a, r_):
                E = np.zeros((r_, r_))
                E[a, b] += 1
                E[b, a] += 1 if a != b else 0
                if a == b:
                    E[a, a] = 1
                Zl = [None] * len(types)
                Zl[ti] = E
                Tt = family_tables(tabs, types, Wf, Zl, float_mode=True)
                col = np.concatenate([osum_float(Tt[f], *orb[f]) if Tt[f] is not None else np.zeros(orb[f][1]) for f in FAMILIES])
                cand_cols.append(col)
                cand_idx.append((ti, a, b))
    Gf = np.array(cand_cols).T
    log('gram candidate columns %s' % (Gf.shape,))
    # column selection: equality columns first (pivoted QR), then Gram columns on the orthogonal complement
    Call = np.hstack([Lf, Gf])
    cn = np.linalg.norm(Call, axis=0)
    cn[cn == 0] = 1.0
    C = Call / cn
    nL = Lf.shape[1]
    # 1) basis of the equality span
    QL, RL, pL = sla.qr(C[:, :nL], mode='economic', pivoting=True)
    dL = np.abs(np.diag(RL))
    rL = int((dL > 1e-9 * dL[0]).sum())
    selL = pL[:rL].tolist()
    QLb = QL[:, :rL]
    # 2) gram columns completing the span (pivoted QR on the projected columns)
    Gp = C[:, nL:] - QLb @ (QLb.T @ C[:, nL:])
    QG, RG, pG = sla.qr(Gp, mode='economic', pivoting=True)
    dG = np.abs(np.diag(RG))
    rG = int((dG > 1e-9 * max(dG[0], 1e-300)).sum()) if len(dG) else 0
    selG = [nL + j for j in pG[:rG].tolist()]
    sel = sorted(selL + selG)
    rho = len(sel)
    log('system rank (float) %d; selected %d equality + %d gram columns' %
        (rho, sum(1 for s in sel if s < Lf.shape[1]), sum(1 for s in sel if s >= Lf.shape[1])))
    # float check: r in column space?
    rf = np.array([float(Fraction(int(x), D)) for x in r])
    Csel = C[:, sel]
    uf, *_ = np.linalg.lstsq(Csel, rf, rcond=None)
    log('float consistency residual %.3e (|r| %.3e)' % (np.linalg.norm(Csel @ uf - rf), np.linalg.norm(rf)))
    # row selection (rows of the column-normalised matrix)
    Qr, Rr, pr = sla.qr(Csel.T, mode='economic', pivoting=True)
    rows = sorted(pr[:rho].tolist())
    # exact columns
    ex_cols = []
    for s in sel:
        if s < Lf.shape[1]:
            g, o = lidx[s]
            ex_cols.append(lam_column_exact(EQ, orb, g, o))
        else:
            ti, a, b = cand_idx[s - Lf.shape[1]]
            r_ = Wint[ti].shape[1]
            E = np.zeros((r_, r_), dtype=object)
            E[a, b] = 1
            E[b, a] = 1
            Zl = [None] * len(types)
            Zl[ti] = E
            Tt = family_tables(tabs, types, Wint, Zl)
            ex_cols.append(np.concatenate([orbit_sums(Tt[f], *orb[f]) if Tt[f] is not None else np.zeros(orb[f][1], dtype=object) for f in FAMILIES]))
    log('exact columns computed')
    Cex = np.array(ex_cols, dtype=object).T          # nrows x rho
    A = flint.fmpq_mat(rho, rho, [int(Cex[i, j]) for i in rows for j in range(rho)])
    bvec = flint.fmpq_mat(rho, 1, [flint.fmpq(int(r[i]), D) for i in rows])
    u = A.solve(bvec)
    log('exact solve done')
    uu = [Fraction(int(u[i, 0].p), int(u[i, 0].q)) for i in range(rho)]
    pickle.dump(dict(sel=sel, rows=rows, u=[str(x) for x in uu], r=[int(x) for x in r], D=D,
                     cand_idx=cand_idx, lidx=lidx, nL=Lf.shape[1]), open(outp + '.solve.pkl', 'wb'))
    # verify all rows exactly with flint: Cex u == r / D
    Cz = flint.fmpq_mat(nrows, rho, [int(Cex[i, j]) for i in range(nrows) for j in range(rho)])
    prod = Cz * u
    ok = all(prod[i, 0] == flint.fmpq(int(r[i]), D) for i in range(nrows))
    log('all-row exact consistency: %s' % ok)
    # build final Z and lambda
    lam = {}
    Zfin = {ti: [[Fraction(int(Zint[ti][a, b]), den) for b in range(Zint[ti].shape[1])] for a in range(Zint[ti].shape[0])] for ti in kept}
    for j, s in enumerate(sel):
        if s < Lf.shape[1]:
            lam[lidx[s]] = uu[j]
        else:
            ti, a, b = cand_idx[s - Lf.shape[1]]
            Zfin[ti][a][b] += uu[j]
            if a != b:
                Zfin[ti][b][a] += uu[j]
    # PSD checks
    bad = []
    for ti in kept:
        if not charpoly_psd(Zfin[ti]):
            bad.append(ti)
    log('PSD failures: %d of %d' % (len(bad), len(kept)))
    cert = dict(k=k, d=d, types=[types[ti] for ti in kept], N=[res['N'][ti] for ti in kept],
                Z=[[[str(x) for x in row] for row in Zfin[ti]] for ti in kept],
                lam={str(key): str(v) for key, v in lam.items()}, lam_index=[key for key in lam],
                consistent=ok, psd_failures=[int(b) for b in bad])
    pickle.dump(cert, open(outp, 'wb'))
    log('certificate written to %s' % outp)


if __name__ == '__main__':
    main()
