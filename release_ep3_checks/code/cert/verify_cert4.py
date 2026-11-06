#!/usr/bin/env python3
"""Independent exact verifier (v4) for k-copy Werner endpoint certificates, any k (k = 4 feasible).

Claim verified: for every complex d^k x d^k matrix C of rank <= 2,
    q_k(C) = sum_{J subset [k]} (-1/2)^{|J|} ||Tr_J C||_F^2 >= 0,
via the four-replica moment relaxation of Zenodo 23134454 (moment families X31, X22, X13 on four replicas
of V = (C^d)^{xk} x C^2: X_f = E |x_0 x_1 x_2 x_3><x_0 x_1 x_2 x_3| with letter patterns 31 = aaab,
22 = aabb, 13 = bbba, a = isometric lifting, b = partner vector).

Every PSD multiplier is a GRAM block: the certificate lists, per block, row patterns u_r (one letter in {a, b}
per replica slot plus a conjugation flag, all rows with the same flags) and local modules J (integer matrices,
one per site and one for the auxiliary qubit).  The (r, s) entry of the block is the operator
|u_r><u_s| (partial transpose on the conjugated slots), which this script derives LITERALLY from the
patterns: the four unconjugated and the four conjugated vector factors of u_r (x) conj(u_s) are matched with
the ket and bra slots of the family whose letters they carry.  A block with a single row is a whole-replica
partial transpose X_f^{Gamma}; two-row blocks are the coupled Gram blocks.  Each block's multiplier is
B = W Z W^T (W integer, Z rational PSD) in the concatenated module coordinates.

Checks (exact):
  1. every Z is symmetric PSD (integer characteristic polynomial sign test);
  2. the functional  L = c - sum_blocks sum_{r,s} <B_rs, J^T |u_r><u_s|(.) J> - lambda.E  vanishes on the
     source space of every family: its sum over every orbit of permutation words (orbits of G_f x G_f x site
     permutations x inversion, G_f = slot permutations preserving the family's letters) is exactly zero.
Contributions are accumulated per (family, entry rule, cut) in the direct sum of all local modules of that
cut, so only one tensor contraction per group is needed (k = 4: 24^5 words).
Nothing is imported from the construction code.
"""
import argparse
import itertools
import json
import math
import pickle
import sys
import time
from fractions import Fraction

sys.set_int_max_str_digits(0)   # certificates may carry rationals with more than 4300 digits

import numpy as np
import flint

PERMS = tuple(itertools.permutations(range(4)))
IDX = {p: i for i, p in enumerate(PERMS)}
P3 = tuple(itertools.permutations(range(3)))
FAMILY_LETTERS = {'31': 'aaab', '22': 'aabb', '13': 'bbba'}


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(q)))


def inverse(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


# ------------------------------------------------------------ literal operators
def digits(x, n, m):
    return [(x // n ** (m - 1 - s)) % n for s in range(m)]


def undigits(ds, n):
    r = 0
    for x in ds:
        r = r * n + x
    return r


def perm_op(n, p):
    """Literal V_p on (C^n)^{x4}: V_p sends tensor factor i to factor p[i].  dict {(row, col): 1}."""
    ent = {}
    for src in itertools.product(range(n), repeat=4):
        tgt = [0] * 4
        for i in range(4):
            tgt[p[i]] = src[i]
        ent[(undigits(tgt, n), undigits(src, n))] = 1
    return ent


def parse_pattern(s):
    """'a a b* b' -> (('a', 0), ('a', 0), ('b', 1), ('b', 0))"""
    out = []
    for tok in s.split():
        out.append((tok[0], 1 if tok.endswith('*') else 0))
    assert len(out) == 4 and all(l in 'ab' for l, _ in out)
    return tuple(out)


def entry_rule(u, v):
    """Literal index rule of the entry |u><v| (partial transpose on the conjugated slots).
    Returns (family, kpos, lpos): entry[i; j] = X_f[k; l] with k_s = (i or j)[slot] as given by kpos[s] =
    ('i' | 'j', slot), similarly l from lpos."""
    assert all(cu == cv for (_, cu), (_, cv) in zip(u, v)), 'rows must share conjugation flags'
    unconj, conj = [], []
    for i in range(4):
        (lu, c), (lv, _) = u[i], v[i]
        if c == 0:
            unconj.append(('i', i, lu))      # component u_i[i_i]
            conj.append(('j', i, lv))        # conj(v_i[j_i])
        else:
            unconj.append(('j', i, lv))      # conj(conj(v_i[j_i]))
            conj.append(('i', i, lu))        # conj(u_i[i_i])
    letters = ''.join(sorted(x[2] for x in unconj))
    assert letters == ''.join(sorted(x[2] for x in conj)), 'unbalanced entry'
    fam = [f for f, L in FAMILY_LETTERS.items() if ''.join(sorted(L)) == letters]
    assert len(fam) == 1, 'no moment family for letters %s' % letters
    f = fam[0]
    L = FAMILY_LETTERS[f]

    def assign(factors):
        used = [False] * 4
        pos = []
        for s in range(4):
            for t, fac in enumerate(factors):
                if not used[t] and fac[2] == L[s]:
                    used[t] = True
                    pos.append((fac[0], fac[1]))
                    break
        assert len(pos) == 4
        return tuple(pos)
    return f, assign(unconj), assign(conj)


def entry_op(n, p, kpos, lpos):
    """Literal operator entry[i; j] = V_p[k; l] (k, l from (i, j) by the rule)."""
    out = {}
    for (r, c), v in perm_op(n, p).items():
        kd, ld = digits(r, n, 4), digits(c, n, 4)
        idig, jdig = [None] * 4, [None] * 4
        for s in range(4):
            for (which, slot), val in ((kpos[s], kd[s]), (lpos[s], ld[s])):
                (idig if which == 'i' else jdig)[slot] = val
        key = (undigits(idig, n), undigits(jdig, n))
        out[key] = out.get(key, 0) + v
    return out


def sandwich(J, ent):
    OJ = np.zeros((J.shape[0], J.shape[1]), dtype=object)
    for (r, c), v in ent.items():
        OJ[r, :] += v * J[c, :]
    return J.T.dot(OJ)


def partial_trace_replica(n, p, slot, order):
    """Literal Tr_slot V_p on (C^n)^{x4}, survivors relabelled by `order`: (factor, q) with
    Tr_slot V_p = factor * V_q on (C^n)^{x3}."""
    res = {}
    for (r, c), v in perm_op(n, p).items():
        rd, cd = digits(r, n, 4), digits(c, n, 4)
        if rd[slot] != cd[slot]:
            continue
        key = (undigits([rd[s] for s in order], n), undigits([cd[s] for s in order], n))
        res[key] = res.get(key, 0) + v
    for q in P3:
        Vq = {}
        for src in itertools.product(range(n), repeat=3):
            tgt = [0] * 3
            for i in range(3):
                tgt[q[i]] = src[i]
            Vq[(undigits(tgt, n), undigits(src, n))] = 1
        if set(res) == set(Vq):
            vals = set(res.values())
            if len(vals) == 1:
                return vals.pop(), q
    raise AssertionError('partial trace not a multiple of a permutation operator')


def perm3_op(n, q):
    ent = {}
    for src in itertools.product(range(n), repeat=3):
        tgt = [0] * 3
        for i in range(3):
            tgt[q[i]] = src[i]
        ent[(undigits(tgt, n), undigits(src, n))] = 1
    return ent


# ------------------------------------------------------------ exact helpers
def fz(A):
    A = np.asarray(A, dtype=object)
    return flint.fmpz_mat(A.shape[0], A.shape[1], [int(x) for x in A.ravel()])


def mode_product(T, A, axis):
    """T integer object tensor, A integer matrix (r x T.shape[axis])."""
    Tm = np.moveaxis(T, axis, 0)
    shp = Tm.shape
    R = fz(A) * fz(Tm.reshape(shp[0], -1))
    R = np.array([int(x) for x in R.entries()], dtype=object).reshape((A.shape[0],) + shp[1:])
    return np.moveaxis(R, 0, axis)


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


def family_group(f):
    L = FAMILY_LETTERS[f]
    return [g for g in PERMS if all(L[g[i]] == L[i] for i in range(4))]


def word_orbits(k, f):
    """Orbit id of every word w in S4^{k+1} under (g, h) in G_f x G_f: w_l -> g w_l h (all l at once),
    inversion w_l -> w_l^{-1}, and permutations of the k site components.  Union-find by min-label
    propagation over the generator maps (and their inverses, applied as scatter-min)."""
    nl = k + 1
    n = 24 ** nl
    codes = np.arange(n, dtype=np.int64)
    pw = [24 ** (nl - 1 - l) for l in range(nl)]
    dg = [(codes // pw[l]) % 24 for l in range(nl)]
    mul = np.array([[IDX[compose(p, q)] for q in PERMS] for p in PERMS])
    inv = np.array([IDX[inverse(p)] for p in PERMS])
    enc = lambda ds: sum(x * pw[l] for l, x in enumerate(ds))
    maps = []
    for g in family_group(f):
        gi = IDX[g]
        maps.append(enc([mul[gi][x] for x in dg]))
        maps.append(enc([mul[x, gi] for x in dg]))
    maps.append(enc([inv[x] for x in dg]))
    for s in itertools.permutations(range(k)):
        ds = [None] * nl
        for i in range(k):
            ds[s[i]] = dg[i]
        ds[k] = dg[k]
        maps.append(enc(ds))
    del dg
    lab = codes.copy()
    while True:
        old = lab.copy()
        for m in maps:                       # the generator set is closed under inverses
            np.minimum(lab, lab[m], out=lab)
        lab = lab[lab]
        if np.array_equal(lab, old):
            break
    uniq, oid = np.unique(lab, return_inverse=True)
    return oid.reshape((24,) * nl), len(uniq)


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
    log('k=%d d=%d, %d multiplier blocks' % (k, d, len(cert['blocks'])))
    # ---- 1. PSD
    Zs = []
    nbad = 0
    for b in cert['blocks']:
        Z = [[Fraction(x) for x in row] for row in b['Z']]
        Zs.append(Z)
        if not psd_charpoly(Z):
            nbad += 1
    log('PSD check: %d failures' % nbad)
    # ---- orbits
    fams = sorted(set(entry_rule(parse_pattern(u), parse_pattern(v))[0]
                      for b in cert['blocks'] for u in b['rows'] for v in b['rows']) | {'31', '22', '13'})
    orb = {}
    for f in fams:
        orb[f] = word_orbits(k, f)
    log('orbits: %s' % {f: orb[f][1] for f in fams})
    accum = {f: [Fraction(0)] * orb[f][1] for f in fams}

    def add_orbit_sums(f, T, den, sign):
        oid, n = orb[f]
        flat = np.asarray(T, dtype=object).ravel()
        o = oid.ravel()
        order = np.argsort(o, kind='stable')
        so = o[order]
        starts = np.flatnonzero(np.r_[True, so[1:] != so[:-1]])
        vals = np.add.reduceat(flat[order], starts)
        A = accum[f]
        for idx, v in zip(so[starts], vals):
            if v:
                A[int(idx)] += Fraction(sign * int(v), den)

    Jmods = {key: np.array(J, dtype=object) for key, J in cert['modules'].items()}
    # ---- 2. block contributions, grouped by (family, rule, cut of the modules)
    groups = {}
    dens = []
    for bi, b in enumerate(cert['blocks']):
        rows = [parse_pattern(u) for u in b['rows']]
        mods = list(b['modules'])
        cut = mods[0].split('|')[1]
        assert all(m.split('|')[1] == cut for m in mods), 'mixed cuts in one block'
        dims = [Jmods[m].shape[1] for m in mods]
        n = int(np.prod(dims))
        W = np.array(b['W'], dtype=object)
        assert W.shape[0] == len(rows) * n
        Z = Zs[bi]
        zden = 1
        for row in Z:
            for x in row:
                zden = zden * x.denominator // math.gcd(zden, x.denominator)
        Wden = int(b.get('Wden', 1))
        dens.append(zden * Wden * Wden)
        for r in range(len(rows)):
            for s in range(len(rows)):
                f, kpos, lpos = entry_rule(rows[r], rows[s])
                groups.setdefault((f, kpos, lpos, cut), []).append((bi, r, s))
    Dg = 1
    for x in dens:
        Dg = Dg * x // math.gcd(Dg, x)
    log('%d contribution groups; global denominator %d bits' % (len(groups), Dg.bit_length()))
    Zint = {}

    def scaled_Z(bi):
        """(integer Z as fmpz_mat, multiplier) with B = W Z W^T * multiplier / Dg."""
        if bi not in Zint:
            Z = Zs[bi]
            zden = 1
            for row in Z:
                for x in row:
                    zden = zden * x.denominator // math.gcd(zden, x.denominator)
            Wden = int(cert['blocks'][bi].get('Wden', 1))
            Zint[bi] = (flint.fmpz_mat(len(Z), len(Z), [int(x * zden) for row in Z for x in row]),
                        Dg // (zden * Wden * Wden))
        return Zint[bi]

    for gi, ((f, kpos, lpos, cut), items) in enumerate(sorted(groups.items(), key=lambda kv: str(kv[0]))):
        # labels of this cut used by the group, per factor type (site modules n = d, aux modules n = 2)
        labs = {'s': [], 'a': []}
        bymods = {}
        for bi, r, s in items:
            mods = tuple(cert['blocks'][bi]['modules'])
            bymods.setdefault(mods, []).append((bi, r, s))
            for l, m in enumerate(mods):
                typ = 'a' if l == k else 's'
                if m not in labs[typ]:
                    labs[typ].append(m)
        off = {}
        A = {}
        for typ in ('s', 'a'):
            o = 0
            cols = []
            for m in labs[typ]:
                J = Jmods[m]
                nn = int(m.split('|')[0])
                off[m] = o
                o += J.shape[1] ** 2
                rowsA = []
                for p in PERMS:
                    rowsA.append(sandwich(J, entry_op(nn, p, kpos, lpos)).ravel())
                cols.append(np.array(rowsA, dtype=object))        # 24 x dim^2
            A[typ] = np.hstack(cols) if cols else np.zeros((24, 0), dtype=object)
        Ds, Da = A['s'].shape[1], A['a'].shape[1]
        acc = np.zeros([Ds] * k + [Da], dtype=object)
        for mods, its in bymods.items():
            dims = [Jmods[m].shape[1] for m in mods]
            n = int(np.prod(dims))
            Bsum = flint.fmpz_mat(n, n)
            for bi, r, s in its:
                W = cert['blocks'][bi]['W']
                Wr = flint.fmpz_mat(n, len(W[0]), [int(x) for row in W[r * n:(r + 1) * n] for x in row])
                Ws = flint.fmpz_mat(n, len(W[0]), [int(x) for row in W[s * n:(s + 1) * n] for x in row])
                Zi, mult = scaled_Z(bi)
                Bsum += (Wr * Zi * Ws.transpose()) * mult
            T = np.array([int(x) for x in Bsum.entries()], dtype=object).reshape(dims + dims)
            order = []
            for i in range(nl):
                order += [i, nl + i]
            T = T.transpose(order).reshape([x * x for x in dims])
            sl = tuple(slice(off[m], off[m] + Jmods[m].shape[1] ** 2) for m in mods)
            acc[sl] += T
        for l in range(nl):
            acc = mode_product(acc, (A['a'] if l == k else A['s']), l)
        add_orbit_sums(f, acc, Dg, sign=-1)
        log('group %d/%d (%s, cut %s, %d contributions) done' % (gi + 1, len(groups), f, cut, len(items)))
    # ---- objective: 2 Tr[(I - F_03/2) V_p] per site, Tr[F_03 V_p] on the auxiliary qubit, / (2^k L)
    swap = (3, 1, 2, 0)
    trace = lambda ent: sum(v for (r, c), v in ent.items() if r == c)
    zs = [2 * trace(perm_op(d, p)) - trace(perm_op(d, compose(swap, p))) for p in PERMS]
    za = [trace(perm_op(2, compose(swap, p))) for p in PERMS]
    C = np.array(1, dtype=object)
    for l in range(k):
        C = np.multiply.outer(C, np.array(zs, dtype=object))
    C = np.multiply.outer(C, np.array(za, dtype=object))
    add_orbit_sums('31', C, (2 ** k) * L, sign=1)
    # ---- equality multipliers
    eqmods = {key: np.array(J, dtype=object) for key, J in cert['eq_modules'].items()}

    def eq_local1(n, slot, order, kind, mkey):
        J = eqmods[mkey]
        cols = []
        for p in PERMS:
            if kind == 'del':
                fac, q = partial_trace_replica(n, p, slot, order)
                M = fac * sandwich(J, perm3_op(n, q))
            else:                                   # 'stiefel_aux': 2 V_p - I_slot (x) Tr_slot V_p
                fac, q = partial_trace_replica(n, p, slot, tuple(i for i in range(4) if i != slot))
                nat = tuple(i for i in range(4) if i != slot)
                e = [None] * 4
                e[slot] = slot
                for i_new, i_old in enumerate(nat):
                    e[i_old] = nat[q[i_new]]
                M = 2 * sandwich(J, perm_op(n, p)) - fac * sandwich(J, perm_op(n, tuple(e)))
            cols.append(M.ravel())
        return np.array(cols, dtype=object).T

    def eq_local(n, slot, order, kind, mkeys):
        return np.vstack([eq_local1(n, slot, tuple(order), kind, mk) for mk in mkeys])

    for gname, ginfo in cert['eq_groups'].items():
        lamv = {tuple(o): Fraction(v) for o, v in ginfo['lambda']}
        if not lamv:
            continue
        lden = 1
        for v in lamv.values():
            lden = lden * v.denominator // math.gcd(lden, v.denominator)
        for part in ginfo['parts']:
            fam, sign = part['family'], part['sign']
            Es = [eq_local(*part['local'][l]) for l in range(nl)]
            Lt = np.zeros([E.shape[0] for E in Es], dtype=object)
            for o, v in lamv.items():
                Lt[o] += int(v * lden)
            T = Lt
            for l in range(nl):
                T = mode_product(T, Es[l].T, l)
            add_orbit_sums(fam, sign * T, lden, sign=-1)
    log('objective and equality contributions done')
    ok = True
    for f in fams:
        nz = sum(1 for v in accum[f] if v != 0)
        log('family %s: orbits %d, nonzero orbit sums %d' % (f, orb[f][1], nz))
        ok = ok and nz == 0
    status = 'EXACT_CERTIFICATE_PASS' if (ok and nbad == 0) else 'FAIL'
    log(status)
    return status


if __name__ == '__main__':
    main()
