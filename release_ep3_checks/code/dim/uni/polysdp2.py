"""Strengthened relaxation (cert + gram2) at an ARBITRARY local dimension n >= 4 from n-independent variables and
exact polynomial-in-n local data (uni/ftpoly.pkl), with the multiplier ranges N fixed from a reference run.
Block t is scaled by n^{-2 F_t} (F_t = total contraction number of its site labels); this is a positive scalar per
block, so PSD constraints and the dual face are unchanged.

Usage: polysdp.py n out.pkl [ref_red.pkl] [types.pkl]
"""
import sys, pickle, time, os
sys.path.insert(0, '<ROOT>/dim')
import numpy as np
from relax import Relaxation
from typed_blocks import TypedEvaluator
from exact import ExactLocal
from ipm import IPM

FTP = pickle.load(open('<ROOT>/dim/uni/ftpoly.pkl', 'rb'))


class PolyLocal:
    """site-factor local data at dimension n (float), with label rows scaled by n^{-2f}."""

    def __init__(self, cut, n, scaled=True):
        P = FTP[cut]
        self.labels, self.dims, self.off, self.D = P['labels'], P['dims'], P['off'], P['D']
        coef = np.array(P['coef'], dtype=float)                       # (5, D, 24)
        FT = sum(coef[k] * float(n) ** k for k in range(5))
        self.scale = []
        for li, lab in enumerate(self.labels):
            s = float(n) ** (-2 * lab[0]) if scaled else 1.0
            FT[self.off[li]:self.off[li + 1]] *= s
            self.scale.append(s)
        self.FT = FT
        # metric G = M(identity) per label
        idp = 0      # P4[0] is the identity permutation
        self.G = [FT[self.off[li]:self.off[li + 1], idp].reshape(d_, d_) for li, d_ in enumerate(self.dims)]

    def rows(self, li):
        return slice(self.off[li], self.off[li + 1])


class PolyTE(TypedEvaluator):
    def __init__(self, R, types, n, scaled=True):
        self.R = R
        self.types = types
        self.k = R.k
        self.locJ = {}
        cuts = set(t['cut'] for t in types)
        for c in cuts:
            self.locJ['s', c] = PolyLocal(c, n, scaled)
            loc_a = ExactLocal(2, 4, c)
            loc_a.FT = loc_a.FT.astype(float)
            loc_a.G = [np.array(g, dtype=float) for g in loc_a.G]
            self.locJ['a', c] = loc_a
        self.Vb = [np.array(t['Vb'], dtype=float) for t in types]
        self.Vb2 = [np.array(t['Vb2'], dtype=float) if t['kind'] == 'gram2' else None for t in types]


def sdp_data(R, n):
    R.d = n
    R.L = float((2 * n ** R.k) ** 4)
    c = R.objective()
    tr = R.trace_row('31')
    Eraw = R.equality_rows()
    U, s, Vt = np.linalg.svd(Eraw, full_matrices=False)
    r = int((s > s.max() * 1e-10).sum())
    return c, tr, Vt[:r], s


def build_reduced_blocks(TE, types, Ns, drop_keys):
    maps = TE.block_maps()
    blocks, meta, Rinv = [], [], []
    for i, (t, Nl, mp) in enumerate(zip(types, Ns, maps)):
        key = (t['kind'], t['f'], t['cut'], t['st'], t['ai'], t['irrep'])
        if Nl is None or key in drop_keys or len(Nl[0]) == 0:
            continue
        N = np.array(Nl, dtype=float)
        idx, F = mp
        Fr = np.einsum('ia,kij,jb->kab', N, F, N, optimize=True)
        G = np.ones((1, 1))
        for li in t['st']:
            G = np.kron(G, TE.locJ['s', t['cut']].G[li])
        G = np.kron(G, TE.locJ['a', t['cut']].G[t['ai']])
        w_, V_ = np.linalg.eigh((G + G.T) / 2)
        Gh = (V_ * np.sqrt(np.maximum(w_, 0))) @ V_.T
        Vb = np.array(t['Vb'], dtype=float)
        if t['kind'] == 'gram':
            n_ = Gh.shape[0]
            Gh = np.block([[Gh, np.zeros((n_, n_))], [np.zeros((n_, n_)), Gh]])
            Vb = np.block([[Vb, np.zeros_like(Vb)], [np.zeros_like(Vb), Vb]])
        elif t['kind'] == 'gram2':
            n_ = Gh.shape[0]
            Gh = np.block([[Gh, np.zeros((n_, n_))], [np.zeros((n_, n_)), Gh]])
            V2 = np.array(t['Vb2'], dtype=float)
            Vb = np.block([[Vb, np.zeros((n_, V2.shape[1]))], [np.zeros((n_, Vb.shape[1])), V2]])
        Q_, R_ = np.linalg.qr(Gh @ Vb @ N)
        Ri = np.linalg.inv(R_)
        Fo = np.einsum('ia,kij,jb->kab', Ri, Fr, Ri, optimize=True)
        sc = np.abs(Fo).max()
        if sc == 0:
            continue
        Fo = Fo / sc
        Ri = Ri / np.sqrt(sc)
        blocks.append((idx, np.ascontiguousarray(Fo)))
        meta.append(i)
        Rinv.append(Ri)
    return blocks, meta, Rinv


def main():
    n = float(sys.argv[1]); outp = sys.argv[2]
    ref = sys.argv[3] if len(sys.argv) > 3 else '<ROOT>/dim/runs/red2_k3_d6.pkl'
    tpath = sys.argv[4] if len(sys.argv) > 4 else '<ROOT>/dim/runs/exact_types2_k3_d6.pkl'
    t0 = time.time()
    R = Relaxation(3, 5, verbose=False)
    types = pickle.load(open(tpath, 'rb'))
    Ns = pickle.load(open(ref, 'rb'))['N']
    drop = {(t['kind'], t['f'], t['cut'], t['st'], t['ai'], t['irrep']) for t in types
            if t['kind'] == 'src' and t['f'] == '22' and t['cut'] == (0, 2) and t['st'] == (5, 5, 5) and t['ai'] == 2 and t['irrep'] == 'triv'}
    TE = PolyTE(R, types, n, scaled=False)
    blocks, meta, Rinv = build_reduced_blocks(TE, types, Ns, drop)
    c, tr, E, Esv = sdp_data(R, n)
    print('n=%g: reduced blocks %d (total dim %d), equality rank %d (sv ratio %.1e), %.0fs' %
          (n, len(blocks), sum(F.shape[1] for _, F in blocks), E.shape[0], Esv[E.shape[0] - 1] / Esv[0], time.time() - t0), flush=True)
    Et = np.vstack([E, tr[None, :]]); bt = np.zeros(Et.shape[0]); bt[-1] = 1.0
    H0 = np.zeros((R.N, R.N))
    for idx, F in blocks:
        A = F.reshape(F.shape[0], -1)
        H0[np.ix_(idx, idx)] += A @ A.T
    U_, s_, Vt_ = np.linalg.svd(Et, full_matrices=True)
    Zt = Vt_[int((s_ > s_.max() * 1e-10).sum()):].T
    Hz = Zt.T @ H0 @ Zt
    wz, Vz = np.linalg.eigh((Hz + Hz.T) / 2)
    Lin = Zt @ Vz[:, wz < 1e-10 * wz.max()]
    if os.environ.get('LIN_DIM'):
        Lin = Zt @ Vz[:, :int(os.environ['LIN_DIM'])]
    print('lineality', Lin.shape[1], flush=True)
    if Lin.shape[1]:
        Et = np.vstack([Et, Lin.T]); bt = np.concatenate([bt, np.zeros(Lin.shape[1])])
    solver = IPM(c, Et, bt, blocks, verbose=True)
    res = solver.solve(maxit=int(os.environ.get('IPM_MAXIT', 80)), tol=float(os.environ.get('IPM_TOL', 5e-8)))
    res['type_index'] = meta
    res['N'] = Ns
    res['Z_exact_basis'] = [Ri @ Dm @ Ri.T for Ri, Dm in zip(Rinv, res['D'])]
    res['n'] = n
    pickle.dump(res, open(outp, 'wb'), protocol=4)
    ev = [np.linalg.eigvalsh((D + D.T) / 2) for D in res['D']]
    per = sorted(w.min() / w.max() for w in ev)
    print('final pobj %.3e dobj %.3e; per-block margin worst %.2e p1 %.2e; time %.0fs' %
          (res['pobj'], res['dobj'], per[0], per[len(per) // 100], time.time() - t0), flush=True)


if __name__ == '__main__':
    main()
