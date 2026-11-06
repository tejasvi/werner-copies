"""Exact multiplier ranges N' (complement of rationalised zero-mode ranges R and physical kernels K, in
exact V coordinates) and the numeric re-solve of the relaxation restricted to them."""
import pickle
import sys
import time
from fractions import Fraction

import numpy as np
import flint

sys.path.insert(0, '<ROOT>/dim')
from exact_blocks import qnullspace, primitive_columns


def exact_N_from_R(Rex, rat, types, drop):
    """N' = exact columns spanning a complement of K (approximate) inside V cap R^perp (R exact)."""
    import scipy.linalg as sla
    out = []
    for i, (Rrows, r, t) in enumerate(zip(Rex, rat, types)):
        key = (t['kind'], t['f'], t['cut'], t['st'], t['ai'], t['irrep'])
        v = len(t['Vb'][0])
        vt = 2 * v if t['kind'] == 'gram' else v
        if t['kind'] == 'gram2':
            vt = v + len(t['Vb2'][0])
        if key in drop:
            out.append(None)
            continue
        if Rrows:
            M = flint.fmpq_mat(len(Rrows), vt, [flint.fmpq(Fraction(x).numerator, Fraction(x).denominator) for row in Rrows for x in row])
            P = qnullspace(M)
        else:
            P = flint.fmpq_mat(vt, vt, [1 if a == b else 0 for a in range(vt) for b in range(vt)])
        m = P.ncols()
        if m and r['K']:
            Pf = np.array([[float(P[a, b]) for b in range(m)] for a in range(vt)])
            Kf = np.array([[float(x) for x in row] for row in r['K']]).T     # vt x kappa
            c, *_ = np.linalg.lstsq(Pf, Kf, rcond=None)                    # m x kappa
            _, _, piv = sla.qr(c.T, pivoting=True, mode='economic')
            dropc = set(piv[:Kf.shape[1]].tolist())
            keepc = [j for j in range(m) if j not in dropc]
            Pk = flint.fmpq_mat(vt, len(keepc), [P[a, j] for a in range(vt) for j in keepc])
            P = Pk
        P = primitive_columns(P) if P.ncols() else P
        out.append([[int(P[a, b]) for b in range(P.ncols())] for a in range(P.nrows())])
    return out


def exact_N(rat, types, drop):
    out = []
    bad = 0
    for i, (r, t) in enumerate(zip(rat, types)):
        key = (t['kind'], t['f'], t['cut'], t['st'], t['ai'], t['irrep'])
        v = len(t['Vb'][0])
        v = v  # V dimension (single copy); gram doubles
        vt = 2 * v if t['kind'] == 'gram' else v
        if key in drop:
            out.append(None)
            continue
        rows = [list(row) for row in r['R']] + [list(row) for row in r['K']]
        if rows:
            M = flint.fmpq_mat(len(rows), vt, [flint.fmpq(x.numerator, x.denominator) for row in rows for x in row])
            # exact orthogonality check R . K = 0
            nR = len(r['R'])
            for a in range(nR):
                for b in range(nR, len(rows)):
                    s = sum(rows[a][j] * rows[b][j] for j in range(vt))
                    if s != 0:
                        bad += 1
            N = qnullspace(M)
        else:
            N = flint.fmpq_mat(vt, vt, [1 if a == b else 0 for a in range(vt) for b in range(vt)])
        N = primitive_columns(N) if N.ncols() else N
        out.append([[int(N[a, b]) for b in range(N.ncols())] for a in range(N.nrows())])
    return out, bad


if __name__ == '__main__':
    from relax import Relaxation
    from typed_blocks import TypedEvaluator
    from ipm import IPM
    k, d = int(sys.argv[1].split(',')[0]), int(sys.argv[1].split(',')[1])
    types = pickle.load(open(sys.argv[2], 'rb'))
    rat = pickle.load(open(sys.argv[3], 'rb'))
    sdp = pickle.load(open(sys.argv[4], 'rb'))
    outp = sys.argv[5]
    phys = [pickle.load(open(p, 'rb'))['y'] for p in sys.argv[6:]]
    t0 = time.time()
    R = Relaxation(k, d, verbose=False)
    TE = TypedEvaluator(R, types)
    maps = TE.block_maps()
    print('block maps %.1fs' % (time.time() - t0), flush=True)
    # linear kernels per type (common kernel over null(E)); drop types whose physical kernel is larger
    E = sdp['E']
    U_, s_, Vt_ = np.linalg.svd(E, full_matrices=True)
    Zn = Vt_[int((s_ > s_.max() * 1e-10).sum()):].T
    drop = set()
    for i, (t, mp) in enumerate(zip(types, maps)):
        idx, F = mp
        Mz = np.tensordot(Zn[idx].T, F, axes=(1, 0))
        S = np.einsum('kij,kjl->il', Mz, Mz)
        w = np.linalg.eigvalsh((S + S.T) / 2)
        klin = int((w < 1e-9 * max(np.abs(w).max(), 1e-300)).sum())
        if len(rat[i]['K']) > klin:
            key = (t['kind'], t['f'], t['cut'], t['st'], t['ai'], t['irrep'])
            print('dropping type', i, key, 'phys kernel', len(rat[i]['K']), 'linear', klin, flush=True)
            drop.add(key)
    import os
    if os.environ.get('FORCE_DROP_ANOM'):
        for t in types:
            key = (t['kind'], t['f'], t['cut'], t['st'], t['ai'], t['irrep'])
            if t['kind'] == 'src' and t['f'] == '22' and t['cut'] == (0, 2) and t['st'] == (5, 5, 5) and t['ai'] == 2 and t['irrep'] in os.environ['FORCE_DROP_ANOM'].split(','):
                print('force-dropping anomalous type', key, flush=True)
                drop.add(key)
    if os.environ.get('FIXED_N'):
        Ns = pickle.load(open(os.environ['FIXED_N'], 'rb'))['N']
        print('exact N loaded from', os.environ['FIXED_N'], flush=True)
    elif os.environ.get('EXACT_R'):
        Rex = pickle.load(open(os.environ['EXACT_R'], 'rb'))
        Ns = exact_N_from_R(Rex, rat, types, drop)
        print('exact N built from exact R, %.1fs' % (time.time() - t0), flush=True)
    else:
        Ns, bad = exact_N(rat, types, drop)
        print('exact N built, R.K nonorthogonal pairs: %d, %.1fs' % (bad, time.time() - t0), flush=True)
    blocks, meta, Rinv = [], [], []
    for i, (t, Nl, mp) in enumerate(zip(types, Ns, maps)):
        if Nl is None or len(Nl[0]) == 0:
            continue
        N = np.array(Nl, dtype=float)
        idx, F = mp
        Fr = np.einsum('ia,kij,jb->kab', N, F, N, optimize=True)
        # orthonormalise w.r.t. the module metric: A = G^{1/2} Vb N = Q R
        G = np.ones((1, 1))
        for li in t['st']:
            G = np.kron(G, TE.locJ['s', t['cut']].G[li].astype(float))
        G = np.kron(G, TE.locJ['a', t['cut']].G[t['ai']].astype(float))
        w_, V_ = np.linalg.eigh(G)
        Gh = (V_ * np.sqrt(w_)) @ V_.T
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
        blocks.append((idx, np.ascontiguousarray(Fo)))
        meta.append(i)
        Rinv.append(Ri)
    print('reduced blocks %d, total dim %d, %.1fs' % (len(blocks), sum(F.shape[1] for _, F in blocks), time.time() - t0), flush=True)
    Et = np.vstack([sdp['E'], sdp['tr']['31'][None, :]])
    bt = np.zeros(Et.shape[0])
    bt[-1] = 1.0
    # lineality: directions in null(Et) on which every reduced block vanishes
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
    print('lineality dimension', Lin.shape[1], 'smallest kept eig %.2e' % (wz[wz >= 1e-10 * wz.max()].min() / wz.max()), flush=True)
    if Lin.shape[1]:
        Et = np.vstack([Et, Lin.T])
        bt = np.concatenate([bt, np.zeros(Lin.shape[1])])
    y0 = sum(phys) / len(phys) if phys else None
    if Lin.shape[1] and y0 is not None:
        y0 = y0 - Lin @ (Lin.T @ y0)
    solver = IPM(sdp['c'], Et, bt, blocks, verbose=True)
    import os
    if os.environ.get('IPM_COLD'):
        res = solver.solve(maxit=100, tol=1e-10, init_scale=float(os.environ.get('IPM_COLD')))
    else:
        res = solver.solve(maxit=int(os.environ.get('IPM_MAXIT', 100)), tol=float(os.environ.get('IPM_TOL', 1e-10)), y0=y0)
    res['type_index'] = meta
    res['N'] = Ns
    res['Rinv'] = Rinv
    res['Z_exact_basis'] = [Ri @ Dm @ Ri.T for Ri, Dm in zip(Rinv, res['D'])]
    res['lineality'] = Lin
    pickle.dump(res, open(outp, 'wb'), protocol=4)
    print('final pobj %.12e dobj %.12e' % (res['pobj'], res['dobj']), flush=True)
