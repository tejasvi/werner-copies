"""Extensions of the cert relaxation: additional valid PSD maps.

gram2: coupled Gram of word class delta=(1,-1):  rows u' = (a, a, a~, b~)  [slot-(0,1) symmetric]
                                                  and  v'' = (a, b, b~, b~)  [slot-(2,3) symmetric],
       G' = [[A', B'], [B'^T, D']] on the cut-(2,3) modules,
       A' = Y31^{G23},  D' = (V_pD Y13 V_pD^*)^{G23}, pD = (1,2,3,0),  B' = (Y22 V_q)^{G23}, q = (1,3,0,2)
       (word maps checked explicitly in b2/check_wordmaps.py).
"""
import numpy as np
from relax import Relaxation, LocalNum, P4, I4, compose, inverse

CUT23 = (2, 3)
PD = (1, 2, 3, 0)
QB = (1, 3, 0, 2)
H01 = [(0, 1, 2, 3), (1, 0, 2, 3)]
H23 = [(0, 1, 2, 3), (0, 1, 3, 2)]


def word_map(fn):
    M = np.zeros((24, 24))
    for a, p in enumerate(P4):
        M[I4[fn(p)], a] = 1
    return M


class RelaxationExt(Relaxation):
    def ensure_cut(self, cut):
        if ('s', cut) not in self.loc:
            self.loc['s', cut] = LocalNum(self.d, 4, cut)
            self.loc['a', cut] = LocalNum(2, 4, cut)

    def extract2(self, X, ob1, ob2, cut):
        ls, la = self.loc['s', cut], self.loc['a', cut]
        k = self.k
        sl = [slice(None)] + [ls.rows(i) for i in ob1['st']] + [la.rows(ob1['ai'])]
        Y = X[tuple(sl)]
        K = Y.shape[0]
        dims = ob1['dims']
        shp = [K]
        for x in dims:
            shp += [x, x]
        Y = Y.reshape(shp)
        order = [0] + [1 + 2 * i for i in range(k + 1)] + [2 + 2 * i for i in range(k + 1)]
        n = int(np.prod(dims))
        Y = Y.transpose(order).reshape(K, n, n)
        return np.einsum('ia,kij,jb->kab', ob1['U'], Y, ob2['U'], optimize=True)

    def gram2_blocks(self):
        """Returns list of dicts per output irrep tuple: st, ai, m1, m2, FA (nvar31,m1,m1), FB (nvar22,m1,m2),
        FD (nvar13,m2,m2).  No site-symmetry splitting (whole representative block)."""
        cut = CUT23
        self.ensure_cut(cut)
        obs1 = self.output_blocks(cut, H01)
        obs2 = self.output_blocks(cut, H23)
        key2 = {(ob['st'], ob['ai']): ob for ob in obs2}
        pairs = [(ob, key2[(ob['st'], ob['ai'])]) for ob in obs1 if (ob['st'], ob['ai']) in key2]
        ls0, la0 = self.loc['s', ()], self.loc['a', ()]
        ls, la = self.loc['s', cut], self.loc['a', cut]
        maps = {'31': word_map(lambda p: p),
                '22': word_map(lambda p: compose(p, QB)),
                '13': word_map(lambda p: compose(compose(PD, p), inverse(PD)))}
        out = [dict(st=o1['st'], ai=o1['ai'], m1=o1['m'], m2=o2['m']) for o1, o2 in pairs]
        for f, Pm in maps.items():
            smap = ls.FT @ Pm @ ls0.IF
            amap = la.FT @ Pm @ la0.IF
            for j, (o1, o2) in enumerate(pairs):
                shape = {'31': (o1['m'], o1['m']), '22': (o1['m'], o2['m']), '13': (o2['m'], o2['m'])}[f]
                out[j]['F' + f] = np.zeros((self.nvar[f],) + shape)

            def cb(b, off, X, f=f):
                for j, (o1, o2) in enumerate(pairs):
                    l, r = {'31': (o1, o1), '22': (o1, o2), '13': (o2, o2)}[f]
                    out[j]['F' + f][off:off + X.shape[0]] = self.extract2(X, l, r, cut)
            self.apply_maps(f, smap, amap, callback=cb)
        return out

    def eval_gram2(self, blocks, y):
        """min eigenvalue (and relative) of every gram2 block at the variable vector y."""
        res = []
        for B in blocks:
            ys = {f: y[self.foff[f]:self.foff[f] + self.nvar[f]] for f in ('31', '22', '13')}
            A = np.tensordot(ys['31'], B['F31'], axes=1)
            Bc = np.tensordot(ys['22'], B['F22'], axes=1)
            D = np.tensordot(ys['13'], B['F13'], axes=1)
            G = np.block([[A, Bc], [Bc.T, D]])
            G = (G + G.T) / 2
            w = np.linalg.eigvalsh(G)
            res.append((w.min(), np.abs(w).max()))
        return res
