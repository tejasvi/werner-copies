"""Float evaluation of the exact block types (J-coordinates, compressed by exact V bases)."""
import sys

import numpy as np

sys.path.insert(0, '<ROOT>/dim')
from relax import P4, I4, TAU, P0, FAMILIES, FAMILY_CUTS
from local import compose
from exact import ExactLocal


class TypedEvaluator:
    def __init__(self, R, types):
        self.R = R
        self.types = types
        self.k = R.k
        self.locJ = {}
        cuts = set(t['cut'] for t in types)
        for c in cuts:
            self.locJ['s', c] = ExactLocal(R.d, 4, c)
            self.locJ['a', c] = ExactLocal(2, 4, c)
        self.Vb = [np.array(t['Vb'], dtype=float) for t in types]
        self.Vb2 = [np.array(t['Vb2'], dtype=float) if t['kind'] == 'gram2' else None for t in types]

    def maps(self, cut, wordperm=None):
        ls0, la0 = self.R.loc['s', ()], self.R.loc['a', ()]
        out = []
        for typ, l0 in (('s', ls0), ('a', la0)):
            FT = self.locJ[typ, cut].FT.astype(float)
            if wordperm is not None:
                Pm = np.zeros((24, 24))
                for a, p in enumerate(P4):
                    Pm[I4[wordperm(p)], a] = 1
                FT = FT @ Pm
            out.append(FT @ l0.IF)
        return out

    def full_tensor(self, f, yf, cut, wordperm=None):
        smap, amap = self.maps(cut, wordperm)
        acc = [None]

        def cb(b, off, X):
            T = np.tensordot(yf[off:off + X.shape[0]], X, axes=(0, 0))
            acc[0] = T if acc[0] is None else acc[0] + T
        self.R.apply_maps(f, smap, amap, callback=cb)
        return acc[0]

    def extract(self, F, t):
        ls, la = self.locJ['s', t['cut']], self.locJ['a', t['cut']]
        sl = tuple([ls.rows(i) for i in t['st']] + [la.rows(t['ai'])])
        Y = F[sl]
        shp = []
        for x in t['dims']:
            shp += [x, x]
        Y = Y.reshape(shp)
        k = self.k
        order = [2 * i for i in range(k + 1)] + [2 * i + 1 for i in range(k + 1)]
        return Y.transpose(order).reshape(t['n'], t['n'])

    def blocks(self, y):
        """Compressed blocks Vb^T S_J Vb for the variable vector y (all families)."""
        R = self.R
        yf = {f: y[R.foff[f]:R.foff[f] + R.nvar[f]] for f in FAMILIES}
        cache = {}
        out = []
        tauconj = lambda p: compose(compose(TAU, p), TAU)
        withp0 = lambda p: compose(p, P0)
        from relax_ext import PD, QB
        from local import inverse
        wm2 = {'31': lambda p: p, '22': lambda p: compose(p, QB), '13': lambda p: compose(compose(PD, p), inverse(PD))}
        for t, Vb, Vb2 in zip(self.types, self.Vb, self.Vb2):
            if t['kind'] == 'gram2':
                for f in ('31', '22', '13'):
                    if ('g2', f) not in cache:
                        cache['g2', f] = self.full_tensor(f, yf[f], (2, 3), wm2[f])
                A = self.extract(cache['g2', '31'], t)
                B = self.extract(cache['g2', '22'], t)
                D = self.extract(cache['g2', '13'], t)
                S = np.block([[A, B], [B.T, D]])
                n1, r1 = Vb.shape; n2, r2 = Vb2.shape
                W = np.zeros((n1 + n2, r1 + r2)); W[:n1, :r1] = Vb; W[n1:, r1:] = Vb2
                out.append(W.T @ S @ W)
                continue
            if t['kind'] == 'src':
                key = (t['f'], t['cut'])
                if key not in cache:
                    cache[key] = self.full_tensor(t['f'], yf[t['f']], t['cut'])
                S = self.extract(cache[key], t)
                out.append(Vb.T @ S @ Vb)
            else:
                for f, wp in (('31', tauconj), ('22', withp0), ('13', tauconj)):
                    if ('g', f) not in cache:
                        cache['g', f] = self.full_tensor(f, yf[f], (3,), wp)
                A = self.extract(cache['g', '31'], t)
                B = self.extract(cache['g', '22'], t)
                D = self.extract(cache['g', '13'], t)
                S = np.block([[A, B], [B.T, D]])
                W = np.block([[Vb, np.zeros_like(Vb)], [np.zeros_like(Vb), Vb]])
                out.append(W.T @ S @ W)
        return out

    def block_maps(self, f_only=None):
        """Per type: (family-index-array, F) with F (K, m, m) the compressed block of each variable."""
        R = self.R
        res = [None] * len(self.types)
        tauconj = lambda p: compose(compose(TAU, p), TAU)
        withp0 = lambda p: compose(p, P0)
        # source types grouped by (f, cut)
        groups = {}
        for i, t in enumerate(self.types):
            if t['kind'] == 'src':
                groups.setdefault((t['f'], t['cut']), []).append(i)
        for (f, cut), ids in groups.items():
            smap, amap = self.maps(cut)
            Fs = {i: np.zeros((R.nvar[f], self.Vb[i].shape[1], self.Vb[i].shape[1])) for i in ids}

            def cb(b, off, X, ids=ids, Fs=Fs):
                for i in ids:
                    S = np.array([self.extract(Xk, self.types[i]) for Xk in X])
                    Vb = self.Vb[i]
                    Fs[i][off:off + X.shape[0]] = np.einsum('ia,kij,jb->kab', Vb, S, Vb, optimize=True)
            R.apply_maps(f, smap, amap, callback=cb)
            for i in ids:
                a = R.foff[f]
                res[i] = (np.arange(a, a + R.nvar[f]), Fs[i])
        gids = [i for i, t in enumerate(self.types) if t['kind'] == 'gram']
        if gids:
            parts = {}
            for f, wp in (('31', tauconj), ('22', withp0), ('13', tauconj)):
                smap, amap = self.maps((3,), wp)
                Fs = {i: np.zeros((R.nvar[f], self.types[i]['n'], self.types[i]['n'])) for i in gids}

                def cb(b, off, X, Fs=Fs):
                    for i in gids:
                        Fs[i][off:off + X.shape[0]] = np.array([self.extract(Xk, self.types[i]) for Xk in X])
                R.apply_maps(f, smap, amap, callback=cb)
                parts[f] = Fs
            N = R.N
            for i in gids:
                Vb = self.Vb[i]
                n, r = Vb.shape
                W = np.zeros((2 * n, 2 * r))
                W[:n, :r] = Vb
                W[n:, r:] = Vb
                F = np.zeros((N, 2 * r, 2 * r))
                for f, sl in (('31', (slice(0, r), slice(0, r))), ('13', (slice(r, 2 * r), slice(r, 2 * r)))):
                    a = R.foff[f]
                    F[a:a + R.nvar[f], sl[0], sl[1]] = np.einsum('ia,kij,jb->kab', Vb, parts[f][i], Vb, optimize=True)
                a = R.foff['22']
                Bc = np.einsum('ia,kij,jb->kab', Vb, parts['22'][i], Vb, optimize=True)
                F[a:a + R.nvar['22'], :r, r:] = Bc
                F[a:a + R.nvar['22'], r:, :r] = np.transpose(Bc, (0, 2, 1))
                res[i] = (np.arange(N), F)
        g2ids = [i for i, t in enumerate(self.types) if t['kind'] == 'gram2']
        if g2ids:
            from relax_ext import PD, QB
            from local import inverse
            wm2 = {'31': lambda p: p, '22': lambda p: compose(p, QB), '13': lambda p: compose(compose(PD, p), inverse(PD))}
            parts = {}
            for f in ('31', '22', '13'):
                smap, amap = self.maps((2, 3), wm2[f])
                Fs = {i: np.zeros((R.nvar[f], self.types[i]['n'], self.types[i]['n'])) for i in g2ids}

                def cb(b, off, X, Fs=Fs):
                    for i in g2ids:
                        Fs[i][off:off + X.shape[0]] = np.array([self.extract(Xk, self.types[i]) for Xk in X])
                R.apply_maps(f, smap, amap, callback=cb)
                parts[f] = Fs
            N = R.N
            for i in g2ids:
                V1, V2 = self.Vb[i], self.Vb2[i]
                r1, r2 = V1.shape[1], V2.shape[1]
                F = np.zeros((N, r1 + r2, r1 + r2))
                a = R.foff['31']; F[a:a + R.nvar['31'], :r1, :r1] = np.einsum('ia,kij,jb->kab', V1, parts['31'][i], V1, optimize=True)
                a = R.foff['13']; F[a:a + R.nvar['13'], r1:, r1:] = np.einsum('ia,kij,jb->kab', V2, parts['13'][i], V2, optimize=True)
                a = R.foff['22']
                Bc = np.einsum('ia,kij,jb->kab', V1, parts['22'][i], V2, optimize=True)
                F[a:a + R.nvar['22'], :r1, r1:] = Bc
                F[a:a + R.nvar['22'], r1:, :r1] = np.transpose(Bc, (0, 2, 1))
                res[i] = (np.arange(N), F)
        return res
