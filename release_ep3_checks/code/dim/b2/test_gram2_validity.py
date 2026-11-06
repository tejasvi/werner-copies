"""Numerical backing of every step of the gram2 validity proof (GRAM2_VALIDITY.md / progress.md section).

Part L (literal operators on V = H (x) Q, H = (C^d)^{x3}, Q = C^2, index x*2+q; d = 3..8):
  L1 isometric lifting of random physical inputs C (rank 1 and 2, non-normal):  A^*A = I, C = A B^*/2,
     ||C||_F^2 = 1/2, ||B||_F^2 = 2, |a| = |b| = 1, Tr_H P_a = I_Q/2, C_xy = sum_r a_xr conj(b_yr).
  L2 objective as swap expectation: <a,b| F_Q prod_{i in S} F_i |a,b> = ||Tr_S C||_F^2 for all S, so
     <a,b|Z|a,b> = q_3(C).
  L3 literal gram2 rules on the product sources Y31 = (aaab)(aaab)^*, Y22 = (aabb)(aabb)^*, Y13 = (bbba)(bbba)^*:
     A'(Y31)[i;j] = Y31[i0 i1 j2 j3; j0 j1 i2 i3] = u'_i conj(u'_j),
     B'(Y22)[i;j] = Y22[i0 i1 j2 j3; i2 j0 i3 j1] = u'_i conj(v''_j),
     D'(Y13)[i;j] = Y13[i1 j2 j3 i0; j1 i2 i3 j0] = v''_i conj(v''_j),
     u' = a (x) a (x) conj a (x) conj b, v'' = a (x) b (x) conj b (x) conj b   (random samples of (i, j) in (V^4)^2);
     an alternative cross rule Y22[i0 i1 j2 j3; j0 i2 j1 i3] gives the same block (bosonic slot swaps).
  L3b the verifier's word-level literal operators (verify_cert.gram2_*_op) equal the rules applied to every V_p
     on (C^n)^{x4}, n = 2..8.
  L4 bosonic rows: u'_{i0 i1 i2 i3} = u'_{i1 i0 i2 i3}, v''_{i0 i1 i2 i3} = v''_{i0 i1 i3 i2}.
  L5 covariance: g = U1 (x) U2 (x) U3 (x) R (Haar): (g a, g b) lifts U C U^* (U = U1 (x) U2 (x) U3), q_3 unchanged;
     site permutations and complex conjugation preserve q_3 and map liftings to liftings.
Part T (the typed blocks actually used in the certificates, polynomial local data at n = d = 4..8):
  random physical points -- general support-2 points (any rank<=2 C on (C^2)^{x3} embedded in (C^d)^{x3}) and
  support-d factorised points (C = (Phi Psi^*) (x) (u v^*)/2) -- give twirled, site-symmetrised, real moment vectors y;
  every gram2 block and every other typed block is PSD (lambda_min >= -1e-12 lambda_max), E y = 0, tr y = 1,
  c.y = q_3(C).
Usage: test_gram2_validity.py [L|T|LT]"""
import sys, itertools, time
sys.path.insert(0, '<ROOT>/dim')
sys.path.insert(0, '<ROOT>/dim/lk')
sys.path.insert(0, '<ROOT>/dim/uni')
import numpy as np

rng = np.random.default_rng(20261019)
t0 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
parts = sys.argv[1] if len(sys.argv) > 1 else 'LT'


def haar(n):
    Z = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    Q, R = np.linalg.qr(Z)
    return Q * (np.diag(R) / np.abs(np.diag(R)))


def q3(C, d):
    T = C.reshape([d] * 6)
    tot = 0.0
    for S in itertools.product((0, 1), repeat=3):
        L = 'abcdef'
        rows = ''.join(L[i] for i in range(3))
        cols = ''.join(L[i] if S[i] else L[3 + i] for i in range(3))
        out = ''.join(L[i] for i in range(3) if not S[i]) + ''.join(L[3 + i] for i in range(3) if not S[i])
        Y = np.einsum(rows + cols + '->' + out, T)
        tot += (-0.5) ** sum(S) * np.sum(np.abs(Y) ** 2)
    return tot


def lifting(C, d):
    Hd = d ** 3
    U, s, Vh = np.linalg.svd(C)
    A = U[:, :2].copy()                      # isometry whose range contains range(C) (rank 1 or 2)
    B = 2 * C.conj().T @ A
    a = (A / np.sqrt(2)).reshape(-1)         # index x*2 + r
    b = (B / np.sqrt(2)).reshape(-1)
    return A, B, a, b


def swap_expect(a, b, d, S):
    a4 = a.reshape(d, d, d, 2); b4 = b.reshape(d, d, d, 2)
    X, Y = 'abcd', 'efgh'
    sw = [i in S for i in range(3)] + [True]
    ka = ''.join(Y[f] if sw[f] else X[f] for f in range(4))
    kb = ''.join(X[f] if sw[f] else Y[f] for f in range(4))
    return np.einsum('%s,%s,%s,%s->' % (X, Y, ka, kb), a4.conj(), b4.conj(), a4, b4)


def trS_norm2(C, d, S):
    T = C.reshape([d] * 6)
    L = 'abcdef'
    cols = ''.join(L[i] if i in S else L[3 + i] for i in range(3))
    out = ''.join(L[i] for i in range(3) if i not in S) + ''.join(L[3 + i] for i in range(3) if i not in S)
    return np.sum(np.abs(np.einsum('abc' + cols + '->' + out, T)) ** 2)


def partL():
    worst = {}
    upd = lambda k, v: worst.__setitem__(k, max(worst.get(k, 0.0), float(v)))
    for d in range(3, 9):
        Hd = d ** 3; Vd = 2 * Hd
        for trial in range(4):
            rk = 1 if trial == 0 else 2
            X = rng.normal(size=(Hd, rk)) + 1j * rng.normal(size=(Hd, rk))
            Yv = rng.normal(size=(Hd, rk)) + 1j * rng.normal(size=(Hd, rk))
            C = X @ Yv.conj().T
            C = C / np.linalg.norm(C) / np.sqrt(2)                     # ||C||_F^2 = 1/2
            A, B, a, b = lifting(C, d)
            upd('L1 A^*A = I', np.abs(A.conj().T @ A - np.eye(2)).max())
            upd('L1 C = AB^*/2', np.abs(C - A @ B.conj().T / 2).max())
            upd('L1 ||B||^2 = 2', abs(np.linalg.norm(B) ** 2 - 2))
            upd('L1 |a|,|b| = 1', max(abs(np.linalg.norm(a) - 1), abs(np.linalg.norm(b) - 1)))
            a2 = a.reshape(Hd, 2); b2 = b.reshape(Hd, 2)
            upd('L1 Tr_H P_a = I/2', np.abs(a2.T @ a2.conj() - np.eye(2) / 2).max())
            upd('L1 C_xy = sum_r a conj b', np.abs(C - a2 @ b2.conj().T).max())
            qz = 0.0
            for S in itertools.chain.from_iterable(itertools.combinations(range(3), r) for r in range(4)):
                e = swap_expect(a, b, d, S)
                upd('L2 swap expectation = ||Tr_S C||^2', abs(e - trS_norm2(C, d, S)))
                qz += (-0.5) ** len(S) * e
            upd('L2 <a,b|Z|a,b> = q3(C)', abs(qz - q3(C, d)))
            # L3: literal rules on random index samples
            ns = 200000
            i = rng.integers(0, Vd, size=(4, ns)); j = rng.integers(0, Vd, size=(4, ns))
            ac, bc = a.conj(), b.conj()
            up = a[i[0]] * a[i[1]] * ac[i[2]] * bc[i[3]]
            uq = a[j[0]] * a[j[1]] * ac[j[2]] * bc[j[3]]
            vp = a[i[0]] * b[i[1]] * bc[i[2]] * bc[i[3]]
            vq = a[j[0]] * b[j[1]] * bc[j[2]] * bc[j[3]]
            Y31 = lambda I, J: a[I[0]] * a[I[1]] * a[I[2]] * b[I[3]] * ac[J[0]] * ac[J[1]] * ac[J[2]] * bc[J[3]]
            Y22 = lambda I, J: a[I[0]] * a[I[1]] * b[I[2]] * b[I[3]] * ac[J[0]] * ac[J[1]] * bc[J[2]] * bc[J[3]]
            Y13 = lambda I, J: b[I[0]] * b[I[1]] * b[I[2]] * a[I[3]] * bc[J[0]] * bc[J[1]] * bc[J[2]] * ac[J[3]]
            Ar = Y31((i[0], i[1], j[2], j[3]), (j[0], j[1], i[2], i[3]))
            Br = Y22((i[0], i[1], j[2], j[3]), (i[2], j[0], i[3], j[1]))
            Br2 = Y22((i[0], i[1], j[2], j[3]), (j[0], i[2], j[1], i[3]))     # alternative rule
            Dr = Y13((i[1], j[2], j[3], i[0]), (j[1], i[2], i[3], j[0]))
            sc = max(np.abs(up).max(), 1e-300) ** 2
            upd("L3 A'(Y31) = u'u'^*", np.abs(Ar - up * uq.conj()).max() / sc)
            upd("L3 B'(Y22) = u'v''^*", np.abs(Br - up * vq.conj()).max() / sc)
            upd("L3 alternative cross rule = same", np.abs(Br2 - Br).max() / sc)
            upd("L3 D'(Y13) = v''v''^*", np.abs(Dr - vp * vq.conj()).max() / sc)
            # L4 bosonic rows
            upd("L4 u' (01)-symmetric", np.abs(up - a[i[1]] * a[i[0]] * ac[i[2]] * bc[i[3]]).max())
            upd("L4 v'' (23)-symmetric", np.abs(vp - a[i[0]] * b[i[1]] * bc[i[3]] * bc[i[2]]).max())
            # L5 covariance under local unitaries, site permutations and conjugation
            Us = [haar(d) for _ in range(3)]; Rq = haar(2)
            g = np.kron(np.kron(np.kron(Us[0], Us[1]), Us[2]), Rq)
            ga, gb = g @ a, g @ b
            Ug = np.kron(np.kron(Us[0], Us[1]), Us[2])
            ga2, gb2 = ga.reshape(Hd, 2), gb.reshape(Hd, 2)
            Cg = ga2 @ gb2.conj().T
            upd('L5 (ga,gb) lifts U C U^*', np.abs(Cg - Ug @ C @ Ug.conj().T).max())
            upd('L5 (ga,gb) isometric: Tr_H P_ga = I/2', np.abs(ga2.T @ ga2.conj() - np.eye(2) / 2).max())
            upd('L5 q3 invariant (local unitaries)', abs(q3(Cg, d) - q3(C, d)))
            perm = rng.permutation(3)
            Cp = C.reshape([d] * 6).transpose(list(perm) + [3 + p for p in perm]).reshape(Hd, Hd)
            upd('L5 q3 invariant (site permutation)', abs(q3(Cp, d) - q3(C, d)))
            upd('L5 q3 invariant (conjugation)', abs(q3(C.conj(), d) - q3(C, d)))
        log('L d=%d done' % d)
    # L3b: verifier word-level literal operators vs the rules on all V_p, n = 2..8
    import verify_cert as V
    for n in range(2, 9):
        N4 = n ** 4
        I = np.arange(N4)
        dig = np.array(np.unravel_index(I, (n,) * 4))           # (4, N4)
        err = 0.0
        for p in V.PERMS:
            Vp = {}
            for (r, c), val in V.perm_op(n, p).items():
                Vp[(r, c)] = Vp.get((r, c), 0) + val
            # dense rule application through the index maps: out[i, j] = Vp[row(i,j), col(i,j)]
            for name, fn, rule in (('A', V.gram2_diag_a_op, lambda i, j: ((i[0], i[1], j[2], j[3]), (j[0], j[1], i[2], i[3]))),
                                   ('B', V.gram2_cross_op, lambda i, j: ((i[0], i[1], j[2], j[3]), (i[2], j[0], i[3], j[1]))),
                                   ('D', V.gram2_diag_d_op, lambda i, j: ((i[1], j[2], j[3], i[0]), (j[1], i[2], i[3], j[0])))):
                lit = fn(n, p)
                # every literal entry must come from the rule, and the rule's nonzeros must be exactly the literal ones
                for (r, c), val in lit.items():
                    ri = np.unravel_index(r, (n,) * 4); ci = np.unravel_index(c, (n,) * 4)
                    rr, cc = rule(ri, ci)
                    err = max(err, abs(val - Vp.get((np.ravel_multi_index(rr, (n,) * 4), np.ravel_multi_index(cc, (n,) * 4)), 0)))
                # count check: rule(V_p) has exactly len(Vp) nonzeros (it is a re-indexing of a 0/1 matrix)
                err = max(err, abs(len(lit) - len(Vp)))
        upd('L3b verifier literal ops = rules on all V_p (n=2..8)', err)
        log('L3b n=%d done' % n)
    for k_, v in worst.items():
        print('  %-55s max error %.3e' % (k_, v))
    print('PART L: %s' % ('PASS (all <= 1e-12)' if max(worst.values()) <= 1e-12 else 'CHECK'))


def partT():
    import pickle
    from relax import Relaxation, FAMILIES, FAMILY_GROUP
    from polysdp2 import PolyTE, sdp_data
    import physical as ph
    from fastmom import moments
    from factmom import prod_moments
    from zm_fast_y import x_from_t
    types = pickle.load(open('<ROOT>/dim/runs/exact_types2_k3_d6.pkl', 'rb'))
    isg2 = np.array([t['kind'] == 'gram2' for t in types])
    R = Relaxation(3, 5, verbose=False)
    PAT = {'31': 'aaab', '22': 'aabb', '13': 'bbba'}
    overall = 0.0
    for d in range(4, 9):
        TE = PolyTE(R, types, float(d), scaled=False)
        maps = TE.block_maps()
        c, tr, E, Esv = sdp_data(R, float(d))
        log('T d=%d: block maps for %d types (%d gram2)' % (d, len(maps), isg2.sum()))
        for kind in ['gen'] * 4 + ['fac'] * 3:
            if kind == 'gen':
                Hs = 8
                Aq, _ = np.linalg.qr(rng.normal(size=(Hs, 2)) + 1j * rng.normal(size=(Hs, 2)))
                a = (Aq / np.sqrt(2)).reshape(-1)
                b = rng.normal(size=2 * Hs) + 1j * rng.normal(size=2 * Hs); b /= np.linalg.norm(b)
                vec = {'31': [a, a, a, b], '22': [a, a, b, b], '13': [b, b, b, a]}
                ts = {f: moments(vec[f], [2, 2, 2, 2])[0] for f in FAMILIES}
                C = a.reshape(Hs, 2) @ b.reshape(Hs, 2).conj().T
                qC = q3(C, 2)
            else:
                Phi, _ = np.linalg.qr(rng.normal(size=(d, 2)) + 1j * rng.normal(size=(d, 2)))
                u = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)); u /= np.linalg.norm(u)
                Psi = rng.normal(size=(d, 2)) + 1j * rng.normal(size=(d, 2))
                v = rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d))
                nb = np.linalg.norm(Psi) * np.linalg.norm(v)
                Psi /= np.linalg.norm(Psi); v /= np.linalg.norm(v)
                fa, fb = Phi / np.sqrt(2), Psi                     # a = (Phi/sqrt2) (x) u, b = Psi (x) v (unit)
                ts = {}
                for f in FAMILIES:
                    A_ = [fa if ch == 'a' else fb for ch in PAT[f]]
                    B_ = [u if ch == 'a' else v for ch in PAT[f]]
                    ts[f] = prod_moments(A_, B_, A_, B_)
                a = np.einsum('xq,yz->xyzq', fa, u).reshape(-1); b = np.einsum('xq,yz->xyzq', fb, v).reshape(-1)
                C = a.reshape(d ** 3, 2) @ b.reshape(d ** 3, 2).conj().T
                qC = q3(C, d)
            R.d = d; R.L = float((2 * d ** 3) ** 4)
            y = np.zeros(R.N)
            for f in FAMILIES:
                yf, _ = ph.coords_from_x(R, f, x_from_t(R, ts[f]))
                y[R.foff[f]:R.foff[f] + R.nvar[f]] = yf
            # negativity measured against the global scale of this point (blocks that vanish at the point are
            # exactly zero up to rounding; a per-block ratio would be meaningless for them)
            negs, tops = np.zeros(len(maps)), np.zeros(len(maps))
            for ti, (idx, F) in enumerate(maps):
                Bm = np.tensordot(y[idx], F, axes=(0, 0))
                Bm = (Bm + Bm.T) / 2
                w = np.linalg.eigvalsh(Bm)
                negs[ti] = max(0.0, -w[0]); tops[ti] = max(abs(w).max(), 0.0)
            scale = tops.max()
            worst_all = negs.max() / scale
            worst_g2 = negs[isg2].max() / scale
            g2_scale = tops[isg2].max() / scale
            eqv = np.abs(E @ y).max()
            log('  %s point: max(-lambda_min)/global lambda_max: gram2 %.2e (gram2 blocks reach %.2f of global), all types %.2e ; |E y| %.1e ; tr y - 1 %.1e ; c.y - q3(C) %.1e' % (
                kind, worst_g2, g2_scale, worst_all, eqv, abs(tr @ y - 1), abs(c @ y - qC)))
            overall = max(overall, worst_all, eqv / 1e0, abs(tr @ y - 1), abs(c @ y - qC))
    print('PART T: %s (worst %.2e)' % ('PASS (<= 1e-12)' if overall <= 1e-12 else 'CHECK', overall))


if 'L' in parts:
    partL()
if 'T' in parts:
    partT()
