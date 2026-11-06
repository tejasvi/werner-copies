"""Exact tables at an arbitrary integer local dimension n from the exact polynomial local data (uni/ftpoly.pkl):
drop-in replacements for exact_cert.Tables / Equalities that never build modules at dimension n."""
import sys, pickle
sys.path.insert(0, '<ROOT>/dim')
import numpy as np
from exact import ExactLocal, P4, I4, compose, TAU, P0
import exact_cert as EC
from exact_blocks import FAMILY_CUTS, FAMILIES, CUT23, WM2

FTP = pickle.load(open('<ROOT>/dim/uni/ftpoly.pkl', 'rb'))


class PolyLocalExact:
    def __init__(self, cut, n):
        P = FTP[cut]
        self.labels, self.dims, self.off, self.D = P['labels'], P['dims'], P['off'], P['D']
        coef = P['coef']                     # (5, D, 24) Fractions (all integers)
        FT = np.zeros((self.D, 24), dtype=object)
        for k in range(5):
            ck = np.array([[int(x) for x in row] for row in coef[k]], dtype=object)
            FT = FT + ck * (n ** k)
        self.FT = FT

    def rows(self, li):
        return slice(self.off[li], self.off[li + 1])


class PolyTables(EC.Tables):
    def __init__(self, k, n):
        self.k, self.d = k, n
        self.loc = {}
        for c in set(c for f in FAMILIES for c in FAMILY_CUTS[f]) | {(3,), CUT23}:
            self.loc['s', c] = PolyLocalExact(c, n)
            self.loc['a', c] = ExactLocal(2, 4, c)
        tauconj = [I4[compose(compose(TAU, p), TAU)] for p in P4]
        withp0 = [I4[compose(p, P0)] for p in P4]
        self.colmap = {'A': tauconj, 'B': withp0, None: list(range(24)),
                       'A2': [I4[WM2['31'](p)] for p in P4], 'B2': [I4[WM2['22'](p)] for p in P4],
                       'D2': [I4[WM2['13'](p)] for p in P4]}
        self.L = (2 * n ** k) ** 4


_S3 = None


class PolyEqualities(EC.Equalities):
    def __init__(self, k, n):
        global _S3
        self.k, self.d = k, n
        if _S3 is None:
            _S3 = ExactLocal(6, 3, ())          # cut () three-replica data are n-independent (n >= 3)
        s3, a3 = _S3, ExactLocal(2, 3, ())
        a4 = ExactLocal(2, 4, ())
        I24 = np.eye(24, dtype=object)
        self.groups = []
        for f, slot in (('31', 0), ('22', 0), ('13', 3)):
            S = s3.FT.dot(EC.delete_matrix(n, slot))
            A = a4.FT.dot(2 * I24 - EC.embed_matrix(slot).dot(EC.delete_matrix(2, slot)))
            self.groups.append(dict(name='stiefel' + f, parts=[(f, S, A, 1)]))
        for (f1, s1, o1), (f2, s2, o2), name in [(('31', 2, (0, 1, 3)), ('22', 2, (0, 1, 3)), 'aab'),
                                                (('22', 1, (0, 2, 3)), ('13', 1, (3, 0, 2)), 'abb')]:
            p1 = (f1, s3.FT.dot(EC.delete_matrix(n, s1, o1)), a3.FT.dot(EC.delete_matrix(2, s1, o1)), 1)
            p2 = (f2, s3.FT.dot(EC.delete_matrix(n, s2, o2)), a3.FT.dot(EC.delete_matrix(2, s2, o2)), -1)
            self.groups.append(dict(name=name, parts=[p1, p2]))
