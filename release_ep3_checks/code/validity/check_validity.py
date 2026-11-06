#!/usr/bin/env python3
"""Literal validity checks for the k = 3 four-replica moment relaxation (Zenodo families + gram2).

What is checked (see VALIDITY.md for the proof these checks support):

 A. Block maps.  For every block family used by the certificates, an independent dense implementation of
    the index rule is applied to the rank-one physical sources Y31 = |aaab><aaab|, Y22 = |aabb><aabb|,
    Y13 = |bbba><bbba| (random complex a, b in C^n, n = 2, 3) and compared with the Gram matrix
    |w><w| of the explicit vector w(a, b).  Then each VERIFIER's own local map (the code that defines the
    certificate functional) is compared with the dense rule on all 24 permutation operators V_p, which
    span the commutant in which the verifiers evaluate the functional.
      * verify_cert4.py: entry_rule/entry_op for every row-pattern pair in every certfile4;
      * verify_cert.py (both copies, dim/ and cert/): perm_op with cut (source partial transposes),
        the Zenodo coupled Gram maps A, B, D and the gram2 maps A2, B2, D2.
 B. Equalities.  The verifiers' local partial-trace ('del') and contrast ('stiefel_aux') maps against dense
    partial traces; then a literal dense check on physical sources with V = H (x) Q, H = C^dH (dH = 2, 3):
    every Stiefel contrast at an a-slot and every marginal equality used by the certificates vanishes;
    contrasts at b-slots do NOT vanish (so the slot audit in E is necessary).
 C. Objective, k = 3, d = 3..8: lifting C = A B^*/2 (A isometry), the swap identity
    <a,b| F_Q prod_{i in S} F_i |a,b> = ||Tr_S C||_F^2 for all S, and c = <a,b|Z|a,b> = q_3(C) (three
    independent evaluations of q_3).  Also Tr_H |a><a| = I/2, |a| = |b| = 1.
 D. The verifiers' word formula for the objective equals Tr[Z_03 (x)_l V_{w_l}] literally.
 E. Audit of the certificate DATA (equality groups, block kinds/cuts, module dimensions) for every
    certificate file: the verifiers take the equality functionals and (v2) the source cuts from the file,
    so validity requires each listed equality to be a valid physical identity.
Run:  <ROOT>/cert/venv/bin/python -I check_validity.py
"""
import importlib.util
import glob
import itertools
import os
import pickle
import sys

import numpy as np

HOME = os.path.expanduser('~')
CERT = os.path.join(HOME, '<ROOT>/cert')
DIM = os.path.join(HOME, '<ROOT>/dim')
TOL = 1e-12
rng = np.random.default_rng(20261019)
FAIL = []


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


V4 = load('v4', os.path.join(CERT, 'verify_cert4.py'))
VD = load('vdim', os.path.join(DIM, 'verify_cert.py'))
VC2 = load('vcert2', os.path.join(CERT, 'verify_cert.py'))
QF = load('qform', os.path.join(HOME, '<ROOT>/lib/qform.py'))
PERMS = tuple(itertools.permutations(range(4)))
LET = {'31': 'aaab', '22': 'aabb', '13': 'bbba'}


def report(name, err, tol=TOL):
    ok = err <= tol
    print('  %-62s max err %.2e  %s' % (name, err, 'ok' if ok else 'FAIL'))
    if not ok:
        FAIL.append(name)


def kron(*vs):
    o = np.ones(1, dtype=complex)
    for v in vs:
        o = np.kron(o, v)
    return o


def dense(ent, N):
    M = np.zeros((N, N))
    for (r, c), v in ent.items():
        M[r, c] += v
    return M


# ---------------------------------------------------------------- independent dense primitives
def vp_dense(n, p):
    """V_p sends tensor factor i to factor p[i]:  V_p (v_0 (x) .. (x) v_3) = (x)_s w_s, w_{p[i]} = v_i.
    Built from the action on the standard basis by tensor-axis transposition (independent of the verifiers)."""
    N = n ** 4
    M = np.zeros((N, N))
    for col in range(N):
        e = np.zeros(N)
        e[col] = 1
        T = e.reshape((n,) * 4)
        # output axis p[i] carries input axis i  <=>  out = T.transpose(inv) with inv[p[i]] = i
        inv = [0] * 4
        for i in range(4):
            inv[p[i]] = i
        M[:, col] = T.transpose(inv).ravel()
    return M


def pt_dense(Y, n, cut, m=4):
    """Partial transpose of the replica slots in `cut` (swap row/col index of those slots)."""
    T = Y.reshape((n,) * (2 * m))
    ax = list(range(2 * m))
    for s in cut:
        ax[s], ax[m + s] = ax[m + s], ax[s]
    return T.transpose(ax).reshape(n ** m, n ** m)


def rule_dense(Y, n, rule):
    """out[i; j] = Y[k(i, j); l(i, j)], rule(i, j) -> (k, l) given as tuples of ('i'|'j', slot)."""
    kpos, lpos = rule
    T = Y.reshape((n,) * 8)
    # output axis e (0..3 = i_slot, 4..7 = j_slot) is input axis carrying the same index
    src_of = {}
    for s in range(4):
        src_of[(kpos[s][0], kpos[s][1])] = s
        src_of[(lpos[s][0], lpos[s][1])] = 4 + s
    axes = [src_of[('i', e)] for e in range(4)] + [src_of[('j', e)] for e in range(4)]
    return T.transpose(axes).reshape(n ** 4, n ** 4)


def ptrace_slot(Y, n, slot, order, m=4):
    """Tr over replica `slot` of an operator on (C^n)^{x m}; survivors relabelled: new slot t = old order[t]."""
    T = Y.reshape((n,) * (2 * m))
    T = np.trace(T, axis1=slot, axis2=m + slot)
    surv = [s for s in range(m) if s != slot]
    pos = {s: t for t, s in enumerate(surv)}
    ax = [pos[o] for o in order] + [m - 1 + pos[o] for o in order]
    return T.transpose(ax).reshape(n ** (m - 1), n ** (m - 1))


def family_Y(f, vec):
    x = kron(*[vec[c] for c in LET[f]])
    return np.outer(x, x.conj())


def pattern_vec(pat, vec):
    return kron(*[(vec[l].conj() if c else vec[l]) for (l, c) in pat])


# ---------------------------------------------------------------- A. block maps
def check_A():
    print('A. block maps')
    pats = set()
    for fn in sorted(glob.glob(os.path.join(CERT, 'runs/vm_certs/certfile4_k3_d*.pkl'))):
        c = pickle.load(open(fn, 'rb'))
        for b in c['blocks']:
            pats.add(tuple(b['rows']))
    print('  row-pattern sets in certfile4 files: %d' % len(pats))
    for pr in sorted(pats):
        print('    ', pr)
    for n in (2, 3):
        vec = {'a': rng.normal(size=n) + 1j * rng.normal(size=n), 'b': rng.normal(size=n) + 1j * rng.normal(size=n)}
        Ys = {f: family_Y(f, vec) for f in LET}
        Vp = {p: vp_dense(n, p) for p in PERMS}
        # sanity: independent V_p vs both verifiers' perm_op, and V_p on product vectors
        e1 = max(np.abs(dense(V4.perm_op(n, p), n ** 4) - Vp[p]).max() for p in PERMS)
        e2 = max(np.abs(dense(VD.perm_op(n, p), n ** 4) - Vp[p]).max() for p in PERMS)
        vs = [rng.normal(size=n) + 1j * rng.normal(size=n) for _ in range(4)]
        e3 = 0
        for p in PERMS:
            w = [None] * 4
            for i in range(4):
                w[p[i]] = vs[i]
            e3 = max(e3, np.abs(Vp[p] @ kron(*vs) - kron(*w)).max())
        report('n=%d V_p: v4 perm_op, dim perm_op, product action' % n, max(e1, e2, e3))
        # v4: every pattern pair -> physical Gram entry, and entry_op == dense rule on all V_p
        eA, eB = 0.0, 0.0
        for pr in sorted(pats):
            rows = [V4.parse_pattern(u) for u in pr]
            for r in rows:
                for s in rows:
                    f, kpos, lpos = V4.entry_rule(r, s)
                    E = rule_dense(Ys[f], n, (kpos, lpos))
                    W = np.outer(pattern_vec(r, vec), pattern_vec(s, vec).conj())
                    eA = max(eA, np.abs(E - W).max())
                    for p in PERMS:
                        eB = max(eB, np.abs(dense(V4.entry_op(n, p, kpos, lpos), n ** 4)
                                            - rule_dense(Vp[p], n, (kpos, lpos))).max())
        report('n=%d v4 entry_rule: entry(Y_f) == |u_r><u_s| (all pairs)' % n, eA)
        report('n=%d v4 entry_op(V_p) == dense rule(V_p), all p, all pairs' % n, eB)
        # v2 (dim and cert round 1): source partial transposes, every family, every cut
        eS, eT = 0.0, 0.0
        for f in LET:
            for r in range(5):
                for cut in itertools.combinations(range(4), r):
                    w = kron(*[(vec[l].conj() if s in cut else vec[l]) for s, l in enumerate(LET[f])])
                    eS = max(eS, np.abs(pt_dense(Ys[f], n, cut) - np.outer(w, w.conj())).max())
        for r in range(5):
            for cut in itertools.combinations(range(4), r):
                for p in PERMS:
                    eT = max(eT, np.abs(dense(VD.perm_op(n, p, cut), n ** 4) - pt_dense(Vp[p], n, cut)).max(),
                             np.abs(dense(VC2.perm_op(n, p, cut), n ** 4) - pt_dense(Vp[p], n, cut)).max())
        report('n=%d source PT: Y_f^Gamma_T == |w><w| (3 families x 16 cuts)' % n, eS)
        report('n=%d v2 perm_op(n,p,cut) == dense PT(V_p) (dim + cert v2)' % n, eT)
        # Zenodo coupled Gram (paper eq. 17-19): u = a a b a*, v = b b a b*
        u = kron(vec['a'], vec['a'], vec['b'], vec['a'].conj())
        v = kron(vec['b'], vec['b'], vec['a'], vec['b'].conj())
        tau = (0, 1, 3, 2)
        A_map = lambda Y: pt_dense(Vp[tau] @ Y @ Vp[tau].T, n, (3,))
        ruleB = ((('i', 0), ('i', 1), ('i', 2), ('j', 3)), (('i', 3), ('j', 2), ('j', 0), ('j', 1)))
        e = max(np.abs(A_map(Ys['31']) - np.outer(u, u.conj())).max(),
                np.abs(rule_dense(Ys['22'], n, ruleB) - np.outer(u, v.conj())).max(),
                np.abs(A_map(Ys['13']) - np.outer(v, v.conj())).max())
        report('n=%d Zenodo Gram: A(Y31)=uu*, B(Y22)=uv*, D(Y13)=vv*' % n, e)
        e = 0
        for p in PERMS:
            tpt = V4.compose(V4.compose(tau, p), tau)
            for mod in (VD, VC2):
                e = max(e, np.abs(dense(mod.perm_op(n, tpt, (3,)), n ** 4) - A_map(Vp[p])).max(),
                        np.abs(dense(mod.gram_cross_op(n, p), n ** 4) - rule_dense(Vp[p], n, ruleB)).max())
        report('n=%d v2 Gram maps A (tau p tau, cut 3), B == dense, all p' % n, e)
        # gram2: u' = a a a* b*, v'' = a b b* b*  (rules from the docstrings of dim/verify_cert.py)
        u2 = kron(vec['a'], vec['a'], vec['a'].conj(), vec['b'].conj())
        v2 = kron(vec['a'], vec['b'], vec['b'].conj(), vec['b'].conj())
        rA2 = ((('i', 0), ('i', 1), ('j', 2), ('j', 3)), (('j', 0), ('j', 1), ('i', 2), ('i', 3)))
        rB2 = ((('i', 0), ('i', 1), ('j', 2), ('j', 3)), (('i', 2), ('j', 0), ('i', 3), ('j', 1)))
        rD2 = ((('i', 1), ('j', 2), ('j', 3), ('i', 0)), (('j', 1), ('i', 2), ('i', 3), ('j', 0)))
        e = max(np.abs(rule_dense(Ys['31'], n, rA2) - np.outer(u2, u2.conj())).max(),
                np.abs(rule_dense(Ys['22'], n, rB2) - np.outer(u2, v2.conj())).max(),
                np.abs(rule_dense(Ys['13'], n, rD2) - np.outer(v2, v2.conj())).max())
        report("n=%d gram2: A2(Y31)=u'u'*, B2(Y22)=u'v''*, D2(Y13)=v''v''*" % n, e)
        e = 0
        for p in PERMS:
            e = max(e, np.abs(dense(VD.gram2_diag_a_op(n, p), n ** 4) - rule_dense(Vp[p], n, rA2)).max(),
                    np.abs(dense(VD.gram2_cross_op(n, p), n ** 4) - rule_dense(Vp[p], n, rB2)).max(),
                    np.abs(dense(VD.gram2_diag_d_op(n, p), n ** 4) - rule_dense(Vp[p], n, rD2)).max())
        report('n=%d dim gram2 literal ops A2, B2, D2 == dense rules, all p' % n, e)
        # the full 2x2 Gram blocks are |w><w| with w = u (+) v: PSD with rank one
        for nm, (x, y, Ax, Bx, Dx) in {
                'Zenodo': (u, v, A_map(Ys['31']), rule_dense(Ys['22'], n, ruleB), A_map(Ys['13'])),
                'gram2': (u2, v2, rule_dense(Ys['31'], n, rA2), rule_dense(Ys['22'], n, rB2),
                          rule_dense(Ys['13'], n, rD2))}.items():
            G = np.block([[Ax, Bx], [Bx.conj().T, Dx]])
            w = np.concatenate([x, y])
            ev = np.linalg.eigvalsh(G)
            report('n=%d %s block == |w><w|; min eig %.1e' % (n, nm, ev.min() / ev.max()),
                   np.abs(G - np.outer(w, w.conj())).max())


# ---------------------------------------------------------------- B. equalities
def lift(C, dH, nsites):
    """C on (C^dH)^{x nsites}, rank <= 2, normalised ||C||^2 = 1/2 -> (A, B, a, b) with C = A B^*/2."""
    U, s, Vh = np.linalg.svd(C)
    r = int((s > 1e-12 * s[0]).sum())
    assert r <= 2
    A = U[:, :2].copy()                          # isometry whose range contains ran C (rank 1: any 2nd column)
    B = 2 * C.conj().T @ A
    a = A.reshape(-1) / np.sqrt(2)               # index (x, r) -> x*2 + r : V = H (x) Q, Q last
    b = B.reshape(-1) / np.sqrt(2)
    return A, B, a, b


def rand_rank2(N, rank=2):
    X = rng.normal(size=(N, rank)) + 1j * rng.normal(size=(N, rank))
    Y = rng.normal(size=(N, rank)) + 1j * rng.normal(size=(N, rank))
    C = X @ Y.conj().T
    return C / np.linalg.norm(C) / np.sqrt(2)


def stiefel_contrast(Y, dH, slot):
    """S_r(Y) = Tr_{H_r} Y - (I_Q/2)_r (x) Tr_{V_r} Y on V^{x4}, V = C^dH (x) C^2 (Q last in each replica)."""
    n = 2 * dH
    T = Y.reshape([dH, 2] * 4 + [dH, 2] * 4)         # axes: (h_s, q_s) for s = 0..3, then bras
    # Tr_{H_slot}: contract h_slot ket with h_slot bra
    TH = np.trace(T, axis1=2 * slot, axis2=8 + 2 * slot)  # remaining axes: kets without h_slot, bras without h_slot
    # Tr_{V_slot} then reinsert I_Q/2 at q_slot
    TV = np.trace(TH, axis1=2 * slot, axis2=7 + 2 * slot)  # q_slot ket at position 2*slot, bra at 7+2*slot
    I2 = np.eye(2) / 2
    TV2 = np.multiply.outer(TV, I2)                  # appended axes: q ket, q bra (at the end)
    nax = TV2.ndim
    # move the appended q ket to position 2*slot and the q bra to position 7 + 2*slot
    order = list(range(nax - 2))
    order.insert(2 * slot, nax - 2)
    order.insert(7 + 2 * slot, nax - 1)
    TV2 = TV2.transpose(order)
    return np.abs(TH - TV2).max()


def check_B():
    print('B. equalities')
    # B1: verifiers' local partial-trace maps vs dense partial traces (all slots, all survivor orders used)
    for n in (2, 3):
        e = 0
        for p in PERMS:
            Vp = vp_dense(n, p)
            for slot in range(4):
                surv = [s for s in range(4) if s != slot]
                for order in itertools.permutations(surv):
                    D = ptrace_slot(Vp, n, slot, order)
                    for mod in (V4, VD, VC2):
                        fac, q = mod.partial_trace_replica(n, p, slot, order)
                        Q3 = np.zeros((n ** 3, n ** 3))
                        for (r, c), v in mod.perm3_op(n, q).items() if hasattr(mod, 'perm3_op') else mod.perm_op(n, q).items():
                            Q3[r, c] += v
                        e = max(e, np.abs(fac * Q3 - D).max())
        report('n=%d verifiers partial_trace_replica == dense Tr_slot (all orders)' % n, e)
    # B2: 'stiefel_aux' operator on the auxiliary qubit: 2 V_p - I_slot (x) Tr_slot V_p
    n = 2
    e = 0
    for p in PERMS:
        Vp = vp_dense(n, p)
        for slot in range(4):
            surv = tuple(s for s in range(4) if s != slot)
            D3 = ptrace_slot(Vp, n, slot, surv)
            # embed back: I on `slot`, D3 on the survivors (natural order)
            T = np.multiply.outer(D3.reshape((n,) * 6), np.eye(n))      # axes k_surv(3), l_surv(3), k_slot, l_slot
            ax_k = list(range(3))
            ax_k.insert(slot, 6)
            ax_l = [3, 4, 5]
            ax_l.insert(slot, 7)
            E = T.transpose(ax_k + ax_l).reshape(n ** 4, n ** 4)
            ref = 2 * Vp - E
            # verifier construction (identical code in v4 and dim): 2 V_p - fac V_e
            fac, q = V4.partial_trace_replica(n, p, slot, surv)
            ee = [None] * 4
            ee[slot] = slot
            for i_new, i_old in enumerate(surv):
                ee[i_old] = surv[q[i_new]]
            M = 2 * Vp - fac * vp_dense(n, tuple(ee))
            e = max(e, np.abs(M - ref).max())
    report("n=2 'stiefel_aux' map == 2 V_p - I_slot (x) Tr_slot V_p", e)
    # B3: physical literal check, V = C^dH (x) C^2 (one site), random rank-2 and rank-1 C
    for dH in (2, 3):
        for rank in (2, 1):
            C = rand_rank2(dH, rank) if dH >= rank else None
            A, B, a, b = lift(C, dH, 1)
            vec = {'a': a, 'b': b}
            Ys = {f: family_Y(f, vec) for f in LET}
            n = 2 * dH
            e_st = max(stiefel_contrast(Ys['31'], dH, s) for s in (0, 1, 2))
            e_st = max(e_st, max(stiefel_contrast(Ys['22'], dH, s) for s in (0, 1)), stiefel_contrast(Ys['13'], dH, 3))
            report('dH=%d rank %d: Stiefel contrasts at all a-slots vanish' % (dH, rank), e_st)
            bad = min([stiefel_contrast(Ys['31'], dH, 3), stiefel_contrast(Ys['22'], dH, 2),
                       stiefel_contrast(Ys['22'], dH, 3)] + [stiefel_contrast(Ys['13'], dH, s) for s in (0, 1, 2)])
            print('  dH=%d rank %d: contrasts at b-slots are NONZERO (min max-entry %.2e) -> slot audit needed'
                  % (dH, rank, bad))
            if bad < 1e-6:
                FAIL.append('b-slot contrast unexpectedly zero')
            m1 = np.abs(ptrace_slot(Ys['31'], n, 2, (0, 1, 3)) - ptrace_slot(Ys['22'], n, 2, (0, 1, 3))).max()
            m2 = np.abs(ptrace_slot(Ys['22'], n, 1, (0, 2, 3)) - ptrace_slot(Ys['13'], n, 1, (3, 0, 2))).max()
            tr = max(abs(np.trace(Ys[f]) - 1) for f in LET)
            report('dH=%d rank %d: marginals aab, abb equal; traces 1' % (dH, rank), max(m1, m2, tr))


# ---------------------------------------------------------------- C. objective, k = 3, d = 3..8
def swap_expect(a, b, d, S):
    """<a (x) b| F_Q prod_{i in S} F_i |a (x) b>, a, b in (C^d)^{x3} (x) C^2."""
    A4 = a.reshape(d, d, d, 2)
    B4 = b.reshape(d, d, d, 2)
    lx = ['x1', 'x2', 'x3', 'r']
    ly = ['y1', 'y2', 'y3', 's']
    swapped = set(['Q']) | set(S)
    sw = {0: 1 in swapped, 1: 2 in swapped, 2: 3 in swapped, 3: True}
    # (F (a(x)b))[x, y] = a[x'] b[y'] with x'_i = y_i on swapped slots
    xa = [ly[i] if sw[i] else lx[i] for i in range(4)]
    yb = [lx[i] if sw[i] else ly[i] for i in range(4)]
    sym = {}
    letters = iter('abcdefgh')
    for t in lx + ly:
        sym[t] = next(letters)
    expr = '%s,%s,%s,%s->' % (''.join(sym[t] for t in lx), ''.join(sym[t] for t in ly),
                               ''.join(sym[t] for t in xa), ''.join(sym[t] for t in yb))
    return np.einsum(expr, A4.conj(), B4.conj(), A4, B4, optimize=True)


def ptrace_norm2(C, d, S):
    X = C.reshape((d,) * 6)
    Y = X
    rem = 3
    for m in sorted(S, reverse=True):             # site labels 1..3 -> row axis m-1, column axis rem+m-1
        Y = np.trace(Y, axis1=m - 1, axis2=rem + m - 1)
        rem -= 1
    return float(np.sum(np.abs(Y) ** 2))


def check_C():
    print('C. objective and lifting, k = 3')
    subsets = [S for r in range(4) for S in itertools.combinations((1, 2, 3), r)]
    for d in range(3, 9):
        N = d ** 3
        inputs = [rand_rank2(N, 2) for _ in range(2)] + [rand_rank2(N, 1)]
        # structured: P (x) |0><0| (x) |0><0| (zero mode) and GHZ-type
        e0 = np.zeros(d)
        e0[0] = 1
        e1 = np.zeros(d)
        e1[1] = 1
        P = np.outer(e0, e0) + np.outer(e1, e1)
        Cz = np.kron(np.kron(P, np.outer(e0, e0)), np.outer(e0, e0))
        g0, g1 = kron(e0, e0, e0), kron(e1, e1, e1)
        Cg = np.outer(g0, g0) - np.outer(g1, g1)
        for Cs in (Cz, Cg):
            inputs.append(Cs / np.linalg.norm(Cs) / np.sqrt(2))
        emax, eiso, eq3, qs = 0.0, 0.0, 0.0, []
        for C in inputs:
            A, B, a, b = lift(C, d, 3)
            ra = a.reshape(N, 2)
            eiso = max(eiso, np.abs(A.conj().T @ A - np.eye(2)).max(), abs(np.linalg.norm(a) - 1),
                       abs(np.linalg.norm(b) - 1), np.abs(A @ B.conj().T / 2 - C).max(),
                       np.abs(ra.T @ ra.conj() - np.eye(2) / 2).max())   # Tr_H |a><a| = I_Q/2
            q_rep = 0.0
            for S in subsets:
                val = swap_expect(a, b, d, S)
                emax = max(emax, abs(val - ptrace_norm2(C, d, S)))
                q_rep += (-0.5) ** len(S) * val.real
            q_pt = sum((-0.5) ** len(S) * ptrace_norm2(C, d, S) for S in subsets)
            q_qf = QF.qval(C, d, 3, 0.5)
            eq3 = max(eq3, abs(q_rep - q_pt), abs(q_qf - q_pt))
            qs.append(q_pt)
        report('d=%d lifting: A*A=I, |a|=|b|=1, C=AB*/2, Tr_H Pa=I/2' % d, eiso)
        report('d=%d swap identity <ab|F_Q F_S|ab> = ||Tr_S C||^2 (8 S)' % d, emax)
        report('d=%d c=<ab|Z|ab> == q_3 (partial traces) == qform.qval' % d, eq3)
        print('      q_3 values: %s' % ', '.join('%.4f' % x for x in qs))


# ---------------------------------------------------------------- D. objective word formula
def check_D():
    print('D. verifiers objective word formula')
    swap = (3, 1, 2, 0)
    for n in (2, 3):
        F03 = vp_dense(n, swap)
        e = 0
        for p in PERMS:
            Vp = vp_dense(n, p)
            zs = 2 * np.trace(Vp) - np.trace(vp_dense(n, V4.compose(swap, p)))
            e = max(e, abs(zs - 2 * np.trace((np.eye(n ** 4) - F03 / 2) @ Vp)),
                    abs(np.trace(vp_dense(n, V4.compose(swap, p))) - np.trace(F03 @ Vp)))
        report('n=%d 2TrV_p - TrV_(swap p) == 2Tr[(I-F03/2)V_p]; TrV_(swap p)==Tr[F03 V_p]' % n, e)
    # product formula over local factors: one site (n=2) and Q (n=2), V = C^2 (x) C^2, words (p_site, p_Q)
    n_s, n_q = 2, 2
    nV = n_s * n_q

    def word_op(ps, pq):
        # operator on V^{x4} with V = site (x) Q: (x)_s (site_s (x) q_s); build as V_ps (x) V_pq then reorder
        M = np.kron(vp_dense(n_s, ps), vp_dense(n_q, pq))      # axes: site0..3, q0..3
        T = M.reshape([n_s] * 4 + [n_q] * 4 + [n_s] * 4 + [n_q] * 4)
        ax = []
        for s in range(4):
            ax += [s, 4 + s]
        axk = ax
        axb = [8 + x for x in ax]
        return T.transpose(axk + axb).reshape(nV ** 4, nV ** 4)

    Zsite = np.eye(n_s ** 4) - vp_dense(n_s, swap) / 2
    Z = np.kron(Zsite, vp_dense(n_q, swap))
    T = Z.reshape([n_s] * 4 + [n_q] * 4 + [n_s] * 4 + [n_q] * 4)
    ax = []
    for s in range(4):
        ax += [s, 4 + s]
    Zr = T.transpose(ax + [8 + x for x in ax]).reshape(nV ** 4, nV ** 4)
    e = 0
    for _ in range(40):
        ps, pq = PERMS[rng.integers(24)], PERMS[rng.integers(24)]
        lhs = np.trace(Zr @ word_op(ps, pq))
        zs = 2 * np.trace(vp_dense(n_s, ps)) - np.trace(vp_dense(n_s, V4.compose(swap, ps)))
        za = np.trace(vp_dense(n_q, V4.compose(swap, pq)))
        e = max(e, abs(lhs - zs * za / 2))
    report('k=1: Tr[Z_03 (V_ps (x) V_pq)] == (zs * za)/2^k (40 random words)', e)


# ---------------------------------------------------------------- E. audit of certificate data
def audit_eq_groups(c, fn):
    d = c['d']
    k = c['k']
    errs = []
    for g, info in c['eq_groups'].items():
        if not info['lambda']:
            continue
        classes = {}
        for part in info['parts']:
            f, sign, loc = part['family'], part['sign'], part['local']
            if f not in LET:
                errs.append('%s: unknown family %s' % (g, f))
                continue
            if len(loc) != k + 1:
                errs.append('%s: %d local factors' % (g, len(loc)))
            slots = set(l[1] for l in loc)
            orders = set(tuple(l[2]) for l in loc)
            ns = [l[0] for l in loc]
            kinds = [l[3] for l in loc]
            if len(slots) != 1:
                errs.append('%s: mixed slots %s' % (g, slots))
            slot = loc[0][1]
            surv = tuple(s for s in range(4) if s != slot)
            if ns[:k] != [d] * k or ns[k] != 2:
                errs.append('%s: local dims %s' % (g, ns))
            if any(kd != 'del' for kd in kinds[:k]) or kinds[k] not in ('del', 'stiefel_aux'):
                errs.append('%s: kinds %s' % (g, kinds))
            if kinds[k] == 'stiefel_aux':
                if LET[f][slot] != 'a':
                    errs.append('%s: Stiefel contrast at a %s-slot (slot %d of %s)' % (g, LET[f][slot], slot, f))
                if any(tuple(l[2]) != surv for l in loc[:k]):
                    errs.append('%s: Stiefel site factors not in natural survivor order' % g)
            else:
                if len(orders) != 1 or sorted(loc[0][2]) != list(surv):
                    errs.append('%s: orders %s' % (g, orders))
                letters = ''.join(LET[f][s] for s in loc[0][2])
                key = (letters, tuple(tuple(l[4]) for l in loc))
                classes[key] = classes.get(key, 0) + sign
        for key, tot in classes.items():
            if tot != 0:
                errs.append('%s: marginal class %s does not cancel (signed sum %s)' % (g, key[0], tot))
    return errs


def audit_file(fn):
    c = pickle.load(open(fn, 'rb'))
    d, k = c['d'], c['k']
    errs = audit_eq_groups(c, fn)
    kinds = {}
    for b in c['blocks']:
        mods = list(b['modules'])
        ns = [int(m.split('|')[0]) for m in mods]
        if ns[:k] != [d] * k or ns[k] != 2:
            errs.append('block with module dims %s' % ns)
        cuts = set(m.split('|')[1] for m in mods)
        if 'rows' in b:                       # v4 format: rows drive the entry rule; check every pair resolves
            rows = [V4.parse_pattern(u) for u in b['rows']]
            for r in rows:
                for s in rows:
                    V4.entry_rule(r, s)
            if len(cuts) != 1:
                errs.append('v4 block with mixed module cuts %s' % cuts)
            key = tuple(b['rows'])
        else:                                 # v2 format: 'src' takes the cut from EACH module key
            if b['kind'] == 'src':
                if len(cuts) != 1:
                    errs.append('src block with mixed cuts %s (NOT a whole-replica transpose)' % cuts)
                if b['family'] not in LET:
                    errs.append('src block family %s' % b['family'])
            elif b['kind'] not in ('gram', 'gram2'):
                errs.append('unknown block kind %s' % b['kind'])
            key = (b['kind'], b.get('family'), cuts.pop() if len(cuts) == 1 else 'MIXED')
        kinds[key] = kinds.get(key, 0) + 1
    return c, errs, kinds


def check_E():
    print('E. audit of certificate data')
    files = (sorted(glob.glob(os.path.join(CERT, 'runs/certfile_k3_d*.pkl')))
             + sorted(glob.glob(os.path.join(CERT, 'runs/vm_certs/certfile4_k3_d*.pkl')))
             + sorted(glob.glob(os.path.join(DIM, 'runs/certfile2_k3_d*.pkl'))))
    for fn in files:
        c, errs, kinds = audit_file(fn)
        rel = fn.replace(HOME + '/<ROOT>/', '')
        print('  %-44s d=%2d blocks %4d, eq groups %s : %s' % (rel, c['d'], len(c['blocks']),
                                                             sorted(c['eq_groups']), 'ok' if not errs else errs[:5]))
        if errs:
            FAIL.append('audit ' + rel)
    print('  block kinds of the last file:', sorted(kinds.items(), key=lambda kv: str(kv[0])))


if __name__ == '__main__':
    which = sys.argv[1:] or ['A', 'B', 'C', 'D', 'E']
    for w in which:
        {'A': check_A, 'B': check_B, 'C': check_C, 'D': check_D, 'E': check_E}[w]()
    print('ALL CHECKS PASS' if not FAIL else 'FAILURES: %s' % FAIL)
