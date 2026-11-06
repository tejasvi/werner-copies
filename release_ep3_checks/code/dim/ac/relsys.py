"""Anchor-relative float system builder (shared)."""
import pickle
import numpy as np


class RelSys:
    def __init__(self, rel):
        self.rel = rel
        self.kept, self.F, self.Fmax, self.Lden = rel['kept'], rel['F'], rel['Fmax'], rel['Lden']
        self.L = {ti: np.array(rel['Lnum'][ti], dtype=float) / self.Lden for ti in self.kept}
        self.dim = {ti: self.L[ti].shape[0] for ti in self.kept}
        self.ent = {ti: [(a, b) for a in range(self.dim[ti]) for b in range(a, self.dim[ti])] for ti in self.kept}
        self.off, o = {}, 0
        for ti in self.kept:
            self.off[ti] = o
            o += len(self.ent[ti])
        self.NY = o
        self.selG = [self.off[ti] + self.ent[ti].index((min(a, b), max(a, b))) for (ti, a, b) in rel['sel_gram']]

    def system(self, n):
        D = np.load('<ROOT>/dim/lk/cols_n%d.npz' % n)
        Gf, idx, Lf, c, lidx = D['Gf'], D['idx'], D['Lf'], D['c'], D['lidx']
        pos = {}
        for j, (ti, a, b) in enumerate(idx):
            pos.setdefault(int(ti), {})[(int(a), int(b))] = j
        R = np.zeros((Gf.shape[0], self.NY))
        for ti in self.kept:
            P = pos[ti]
            es = sorted(P)
            Gt = Gf[:, [P[e] for e in es]]
            sc = float(n) ** (-2 * self.F[ti])
            Lt = self.L[ti]
            C = np.zeros((len(es), len(self.ent[ti])))
            for j, (a, b) in enumerate(self.ent[ti]):
                M = np.outer(Lt[:, a], Lt[:, b])
                M = sc * (M + M.T) if a != b else sc * M
                C[:, j] = [M[c_, d_] for (c_, d_) in es]
            R[:, self.off[ti]:self.off[ti] + len(self.ent[ti])] = Gt @ C
        lmap = {(int(r[0]), tuple(int(x) for x in r[1:])): j for j, r in enumerate(lidx)}
        E = Lf[:, [lmap[(g, tuple(o_))] for (g, o_) in self.rel['sel_eq']]]
        return R, E, c
