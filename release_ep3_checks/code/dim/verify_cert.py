#!/usr/bin/env python3
"""Independent exact verifier for the k-copy Werner endpoint certificate.

Claim verified: for every complex d^k x d^k matrix C of rank <= 2,
    q_k(C) = sum_{J subset [k]} (-1/2)^{|J|} ||Tr_J C||_F^2 >= 0,
via the moment relaxation of Zenodo 23134454 (three moment families X31, X22, X13 on four replicas of
V = (C^d)^{xk} x C^2).  The certificate supplies, for each multiplier t, a rational embedding
J_t = (x)_l J_{t,l} of local modules (integer matrices, given explicitly), a rational matrix W_t and a
rational PSD Z_t; and rational multipliers lambda for the linear equalities.  This script recomputes
EVERYTHING it needs from literal tensor operators (permutation operators, partial transposes, partial
traces, the Gram index rule); it imports nothing from the construction code.

Checks:
  1. every Z_t is exactly symmetric PSD (integer characteristic polynomial sign test);
  2. the linear functional  L = c - sum_t <W Z W^T, J^T (.)^Gamma J> - lambda.E
     vanishes on the whole source space S_f of every family f, i.e. its sum over every orbit of
     permutation words (orbits of G_f x G_f x site permutations x inversion) is exactly zero.
Then for every physical tuple: q_k(C) = c(X) = sum_t <B_t, PSD> + 0 >= 0.
"""
import argparse
import itertools
import json
import math
import pickle
import sys
import time
from fractions import Fraction

import numpy as np
import flint

PERMS = tuple(itertools.permutations(range(4)))
IDX = {p: i for i, p in enumerate(PERMS)}
P3 = tuple(itertools.permutations(range(3)))
IDX3 = {p: i for i, p in enumerate(P3)}


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(q)))


def inverse(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


def cycles(p):
    seen, c = set(), 0
    for i in range(len(p)):
        if i not in seen:
            c += 1
            j = i
            while j not in seen:
                seen.add(j)
                j = p[j]
    return c


# ------------------------------------------------------------ literal operators
def perm_op(n, p, cut=()):
    """Literal (V_p)^{Gamma_cut} on (C^n)^{x m}, m = len(p): dict {(row, col): 1}.
    V_p sends tensor factor i to factor p[i]; Gamma swaps row/col digits at the slots in cut."""
    m = len(p)
    ent = {}
    for src in itertools.product(range(n), repeat=m):
        tgt = [0] * m
        for i in range(m):
            tgt[p[i]] = src[i]
        row, col = list(tgt), list(src)
        for s in cut:
            row[s], col[s] = col[s], row[s]
        r = 0
        c = 0
        for x in row:
            r = r * n + x
        for x in col:
            c = c * n + x
        ent[(r, c)] = ent.get((r, c), 0) + 1
    return ent


def gram_cross_op(n, p):
    """Literal B(V_p) with B(Y)[i0 i1 i2 i3; j0 j1 j2 j3] = Y[i0 i1 i2 j3; i3 j2 j0 j1]."""
    m = 4
    out = {}
    Y = perm_op(n, p)
    for (r, c), v in Y.items():
        rd = [(r // n ** (m - 1 - s)) % n for s in range(m)]
        cd = [(c // n ** (m - 1 - s)) % n for s in range(m)]
        # Y[a; b] with a = (i0, i1, i2, j3), b = (i3, j2, j0, j1)
        i0, i1, i2, j3 = rd
        i3, j2, j0, j1 = cd
        R = ((i0 * n + i1) * n + i2) * n + i3
        C = ((j0 * n + j1) * n + j2) * n + j3
        out[(R, C)] = out.get((R, C), 0) + v
    return out


def _digits(r, n, m=4):
    return [(r // n ** (m - 1 - s)) % n for s in range(m)]


def _index(ds, n):
    r = 0
    for x in ds:
        r = r * n + x
    return r


def gram2_cross_op(n, p):
    """Literal B'(V_p), B'(Y)[i0 i1 i2 i3; j0 j1 j2 j3] = Y[i0 i1 j2 j3; i2 j0 i3 j1]
    (rows u' = a (x) a (x) conj(a) (x) conj(b), columns v'' = a (x) b (x) conj(b) (x) conj(b))."""
    out = {}
    for (r, c), v in perm_op(n, p).items():
        rd, cd = _digits(r, n), _digits(c, n)
        i = (rd[0], rd[1], cd[0], cd[2])
        j = (cd[1], cd[3], rd[2], rd[3])
        key = (_index(i, n), _index(j, n))
        out[key] = out.get(key, 0) + v
    return out


def gram2_diag_a_op(n, p):
    """Literal A'(V_p), A'(Y)[i; j] = Y[i0 i1 j2 j3; j0 j1 i2 i3]  (u' u'^* from Y31 = (aaab)(aaab)^*)."""
    out = {}
    for (r, c), v in perm_op(n, p).items():
        rd, cd = _digits(r, n), _digits(c, n)
        i = (rd[0], rd[1], cd[2], cd[3])
        j = (cd[0], cd[1], rd[2], rd[3])
        key = (_index(i, n), _index(j, n))
        out[key] = out.get(key, 0) + v
    return out


def gram2_diag_d_op(n, p):
    """Literal D'(V_p), D'(Y)[i; j] = Y[i1 j2 j3 i0; j1 i2 i3 j0]  (v'' v''^* from Y13 = (bbba)(bbba)^*)."""
    out = {}
    for (r, c), v in perm_op(n, p).items():
        rd, cd = _digits(r, n), _digits(c, n)
        i = (rd[3], rd[0], cd[1], cd[2])
        j = (cd[3], cd[0], rd[1], rd[2])
        key = (_index(i, n), _index(j, n))
        out[key] = out.get(key, 0) + v
    return out


def sandwich(J, ent, J2=None):
    """J^T Op J2 for a sparse literal operator (integer numpy object arrays)."""
    J2 = J if J2 is None else J2
    OJ = np.zeros((J.shape[0], J2.shape[1]), dtype=object)
    for (r, c), v in ent.items():
        OJ[r, :] += v * J2[c, :]
    return J.T.dot(OJ)


def partial_trace_replica(n, p, slot, order):
    """Literal Tr_slot V_p on (C^n)^{x4}, survivors relabelled by `order`: returns (factor, q) with
    Tr_slot V_p = factor * V_q on (C^n)^{x3}.  Computed from matrix entries."""
    ent = perm_op(n, p)
    m = 4
    res = {}
    for (r, c), v in ent.items():
        rd = [(r // n ** (m - 1 - s)) % n for s in range(m)]
        cd = [(c // n ** (m - 1 - s)) % n for s in range(m)]
        if rd[slot] != cd[slot]:
            continue
        rr = 0
        cc = 0
        for s in order:
            rr = rr * n + rd[s]
            cc = cc * n + cd[s]
        res[(rr, cc)] = res.get((rr, cc), 0) + v
    # identify with factor * V_q (q in S_3)
    for q in P3:
        Vq = perm_op(n, q)
        keys = set(Vq)
        if set(res) == keys:
            vals = set(res[x] for x in keys)
            if len(vals) == 1:
                return vals.pop(), q
    raise AssertionError('partial trace not a multiple of a permutation operator')


# ------------------------------------------------------------ helpers
def fz(A):
    A = np.asarray(A, dtype=object)
    return flint.fmpz_mat(A.shape[0], A.shape[1], [int(x) for x in A.ravel()])


def from_fz(M, shape):
    return np.array([int(x) for x in M.entries()], dtype=object).reshape(shape)


def mode_product(T, A, axis):
    Tm = np.moveaxis(T, axis, 0)
    shp = Tm.shape
    R = fz(A) * fz(Tm.reshape(shp[0], -1))
    R = from_fz(R, (A.shape[0],) + shp[1:])
    return np.moveaxis(R, 0, axis)


def frac_parse(s):
    return Fraction(s)


def psd_charpoly(Z):
    n = len(Z)
    den = 1
    for row in Z:
        for x in row:
            den = den * x.denominator // math.gcd(den, x.denominator)
    M = flint.fmpz_mat(n, n, [int(x * den) for row in Z for x in row])
    if M != M.transpose():
        return False
    cp = M.charpoly()
    co = [int(cp[i]) for i in range(n + 1)]
    return all(((-1) ** kk) * co[n - kk] >= 0 for kk in range(n + 1))


FAMILY_GROUP = {
    '31': [p + (3,) for p in P3],
    '13': [p + (3,) for p in P3],
    '22': [(0, 1, 2, 3), (1, 0, 2, 3), (0, 1, 3, 2), (1, 0, 3, 2)],
}
FAMILIES = ('31', '22', '13')


def word_orbits(k, f):
    nl = k + 1
    gidx = [IDX[g] for g in FAMILY_GROUP[f]]
    mul = [[IDX[compose(p, q)] for q in PERMS] for p in PERMS]
    inv = [IDX[inverse(p)] for p in PERMS]
    sp = list(itertools.permutations(range(k)))
    oid = -np.ones((24,) * nl, dtype=np.int64)
    n = 0
    for w in itertools.product(range(24), repeat=nl):
        if oid[w] >= 0:
            continue
        stack = [w]
        oid[w] = n
        while stack:
            u = stack.pop()
            imgs = [tuple(mul[mul[g][x]][h] for x in u) for g in gidx for h in gidx]
            imgs.append(tuple(inv[x] for x in u))
            for s in sp:
                v = [None] * nl
                for i in range(k):
                    v[s[i]] = u[i]
                v[k] = u[k]
                imgs.append(tuple(v))
            for v in imgs:
                if oid[v] < 0:
                    oid[v] = n
                    stack.append(v)
        n += 1
    return oid, n


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('cert')
    args = ap.parse_args()
    t0 = time.time()
    log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
    if args.cert.endswith('.json.gz'):
        import gzip
        cert = json.load(gzip.open(args.cert, 'rt'))
    else:
        cert = pickle.load(open(args.cert, 'rb'))
    k, d = cert['k'], cert['d']
    nl = k + 1
    L = (2 * d ** k) ** 4
    log('k=%d d=%d, %d multipliers, %d equality multipliers' % (k, d, len(cert['blocks']), len(cert['lam'])))
    # ---- 1. PSD
    nbad = 0
    for b in cert['blocks']:
        Z = [[frac_parse(x) for x in row] for row in b['Z']]
        if not psd_charpoly(Z):
            nbad += 1
    log('PSD check: %d failures' % nbad)
    # ---- local literal maps: M[(n, cut, J-key)][p] = J^T V_p^Gamma J  (and gram maps)
    Jmods = {key: np.array(J, dtype=object) for key, J in cert['modules'].items()}
    opcache = {}

    def op(n, p, cut):
        key = (n, p, cut)
        if key not in opcache:
            opcache[key] = perm_op(n, p, cut)
        return opcache[key]

    Mcache = {}

    def local_maps(mkey, mapkind):
        """24 x (dim^2) integer matrix: column layout a*dim+b of J^T Op(p) J for p in PERMS."""
        if (mkey, mapkind) in Mcache:
            return Mcache[mkey, mapkind]
        ns, cuts, label = mkey.split('|')
        n = int(ns)
        cut = tuple(int(x) for x in cuts.split(',') if x != '')
        J = Jmods[mkey]
        rows = []
        tau = (0, 1, 3, 2)
        for p in PERMS:
            if mapkind is None:
                E = op(n, p, tuple(cut))
            elif mapkind == 'A':
                E = op(n, compose(compose(tau, p), tau), (3,))
            elif mapkind == 'B':
                E = gram_cross_op(n, p)
            elif mapkind == 'A2':
                E = gram2_diag_a_op(n, p)
            elif mapkind == 'B2':
                E = gram2_cross_op(n, p)
            elif mapkind == 'D2':
                E = gram2_diag_d_op(n, p)
            M = sandwich(J, E)
            rows.append(M.ravel())
        A = np.array(rows, dtype=object)       # 24 x dim^2
        Mcache[mkey, mapkind] = A
        return A

    # ---- 2. tables per family
    orb = {f: word_orbits(k, f) for f in FAMILIES}
    log('orbits: %s' % {f: orb[f][1] for f in FAMILIES})
    # orbit sums are linear: accumulate, per family, the exact orbit sums of every contribution
    def orbit_sum_vector(T, f):
        oid, n = orb[f]
        flat = T.ravel()
        o = oid.ravel()
        order = np.argsort(o, kind='stable')
        so = o[order]
        starts = np.flatnonzero(np.r_[True, so[1:] != so[:-1]])
        vals = np.add.reduceat(flat[order], starts)
        out = [0] * n
        for idx, v in zip(so[starts], vals):
            out[int(idx)] = int(v)
        return out

    accum = {f: [Fraction(0)] * orb[f][1] for f in FAMILIES}

    def add_orbit_sums(f, T, den, sign=1):
        vec = orbit_sum_vector(T, f)
        A = accum[f]
        for i, v in enumerate(vec):
            if v:
                A[i] += Fraction(sign * v, den)

    contribs = []
    for b in cert['blocks']:
        W = np.array(b['W'], dtype=object)
        Wden = int(b.get('Wden', 1))
        Z = [[frac_parse(x) for x in row] for row in b['Z']]
        zden = 1
        for row in Z:
            for x in row:
                zden = zden * x.denominator // math.gcd(zden, x.denominator)
        Zi = np.array([[int(x * zden) for x in row] for row in Z], dtype=object)
        B = W.dot(Zi).dot(W.T)                    # true B = this / (zden * Wden^2)
        bden = zden * Wden * Wden
        mods = list(b['modules'])   # 'n|cut|label' per local factor
        dims = [Jmods[m].shape[1] for m in mods]
        n = int(np.prod(dims))
        parts = []
        if b['kind'] == 'src':
            parts.append((b['family'], B, None, 1))
        elif b['kind'] == 'gram2':
            parts.append(('31', B[:n, :n], 'A2', 1))
            parts.append(('22', B[:n, n:], 'B2', 2))
            parts.append(('13', B[n:, n:], 'D2', 1))
        else:
            parts.append(('31', B[:n, :n], 'A', 1))
            parts.append(('22', B[:n, n:], 'B', 2))
            parts.append(('13', B[n:, n:], 'A', 1))
        for fam, Bp, mk, mult in parts:
            T = np.asarray(Bp, dtype=object).reshape(dims + dims)
            order = []
            for i in range(nl):
                order += [i, nl + i]
            T = T.transpose(order).reshape([x * x for x in dims])
            for l in range(nl):
                T = mode_product(T, local_maps(mods[l], mk), l)
            add_orbit_sums(fam, mult * T, bden, sign=-1)
    log('block tables computed and orbit-summed')
    # objective
    swap = (3, 1, 2, 0)
    trace = lambda ent: sum(v for (r, c), v in ent.items() if r == c)
    # literal traces: 2 Tr[(I - F_03/2) V_p] on a site, Tr[F_03 V_p] on the auxiliary qubit
    zs = [2 * trace(op(d, p, ())) - trace(op(d, compose(swap, p), ())) for p in PERMS]
    za = [trace(op(2, compose(swap, p), ())) for p in PERMS]
    C = np.array(1, dtype=object)
    for l in range(k):
        C = np.multiply.outer(C, np.array(zs, dtype=object))
    C = np.multiply.outer(C, np.array(za, dtype=object))
    cden = (2 ** k) * L
    # equality multipliers
    eqmods = {key: np.array(J, dtype=object) for key, J in cert['eq_modules'].items()}

    def eq_local(n, slot, order, kind, mkeys):
        """Rows: output coordinates (entries of the listed modules, concatenated); columns: words p.
        kind 'del' = Tr_slot V_p (survivors in `order`) in 3-replica modules;
        'stiefel_aux' = 2 V_p - I_slot (x) Tr_slot V_p in 4-replica modules."""
        return np.vstack([eq_local1(n, slot, order, kind, mk) for mk in mkeys])

    def eq_local1(n, slot, order, kind, mkey):
        J = eqmods[mkey]
        cols = []
        for p in PERMS:
            if kind == 'del':
                fac, q = partial_trace_replica(n, p, slot, order)
                M = fac * sandwich(J, op(n, q, ()))
            else:
                fac, q = partial_trace_replica(n, p, slot, tuple(i for i in range(4) if i != slot))
                # embed q with slot fixed (I on replica slot)
                nat = tuple(i for i in range(4) if i != slot)
                e = [None] * 4
                e[slot] = slot
                for i_new, i_old in enumerate(nat):
                    e[i_old] = nat[q[i_new]]
                M = 2 * sandwich(J, op(n, p, ())) - fac * sandwich(J, op(n, tuple(e), ()))
            cols.append(M.ravel())
        return np.array(cols, dtype=object).T

    groups = cert['eq_groups']
    lam_contribs = []
    for gname, ginfo in groups.items():
        lamv = {tuple(o): frac_parse(v) for o, v in ginfo['lambda']}
        if not lamv:
            continue
        lden = 1
        for v in lamv.values():
            lden = lden * v.denominator // math.gcd(lden, v.denominator)
        for part in ginfo['parts']:
            fam, sign = part['family'], part['sign']
            Es = [eq_local(*part['local'][l]) for l in range(nl)]
            shp = [E.shape[0] for E in Es]
            Lt = np.zeros(shp, dtype=object)
            for o, v in lamv.items():
                Lt[o] += int(v * lden)
            T = Lt
            for l in range(nl):
                T = mode_product(T, Es[l].T, l)
            add_orbit_sums(fam, sign * T, lden, sign=-1)
    add_orbit_sums('31', C, cden, sign=1)
    log('equality and objective tables computed and orbit-summed')
    # ---- check: every orbit sum of  c - sum_t T_t - T_lambda  vanishes
    ok = True
    for f in FAMILIES:
        nz = sum(1 for v in accum[f] if v != 0)
        log('family %s: orbits %d, nonzero orbit sums %d' % (f, orb[f][1], nz))
        ok = ok and nz == 0
    status = 'EXACT_CERTIFICATE_PASS' if (ok and nbad == 0) else 'FAIL'
    log(status)
    return status


if __name__ == '__main__':
    main()
