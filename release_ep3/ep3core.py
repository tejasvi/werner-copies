"""ep3core -- standalone core of the EP_3 certificate verifier (nothing is imported from the construction code).

Relaxation (four-replica moment relaxation of Zenodo 23134454, k = 3 sites + 1 auxiliary qubit): a certificate at
local dimension n consists of PSD Gram multipliers Z_t (one per type t: row patterns u_r, one module per site and an
auxiliary module) and equality multipliers lambda; it is valid iff the functional
    L = c - sum_t sum_{r,s} <B^t_rs, J^T |u_r><u_s|(.) J> - lambda . E
vanishes on every orbit of permutation words (B^t = W Z_t W^T).  This file implements L in closed form for EVERY n:

  * site modules are COMPRESSIONS J(n) = D(n) C by diagram vectors D_key(n) = sum_{j in [n]^f} e_x (x = j on the
    contraction pairs, fixed 'top' values 0,1,.. on the other non-cut slots, 'bottom' values n-1, n-2,.. on the other
    cut slots) with a fixed integer matrix C;
  * <D_a(n)| O |D_b(n)> for a partially transposed permutation operator O is computed by LOOP COUNTING: the graph of
    the operator's matching and the pair edges of D_a, D_b splits into free cycles (factor n each) and paths between
    two fixed values (factor [values equal]); top and bottom values never coincide for n >= 4 (asserted), so every
    entry is eps * n^c with eps in {0,1} and c <= #pair edges <= 4;
  * auxiliary modules (local dimension 2) are literal integer matrices;
  * three-replica equality modules have f = 0 (no cycles: n-independent); partial traces Tr_slot V_p = n^[p(s)=s] V_q;
  * the objective is the closed trace formula.
Any compression of a PSD operator is PSD, so the relaxation defined this way is valid at every n >= 4 (Theorem V's
argument); the verifier map is a polynomial in n by construction, with the degree bounds used by the verifier.
"""
import itertools
import math
from fractions import Fraction

import numpy as np
import flint

PERMS = tuple(itertools.permutations(range(4)))
IDX = {p: i for i, p in enumerate(PERMS)}
P3 = tuple(itertools.permutations(range(3)))
FAMILY_LETTERS = {'31': 'aaab', '22': 'aabb', '13': 'bbba'}
FAMILIES = ('31', '22', '13')


def compose(p, q):
    return tuple(p[q[i]] for i in range(len(q)))


def inverse(p):
    r = [0] * len(p)
    for i, j in enumerate(p):
        r[j] = i
    return tuple(r)


def ncycles(p):
    seen, c = set(), 0
    for i in range(len(p)):
        if i not in seen:
            c += 1
            j = i
            while j not in seen:
                seen.add(j)
                j = p[j]
    return c


# ------------------------------------------------------------------ words and orbits
def family_group(f):
    L = FAMILY_LETTERS[f]
    return [g for g in PERMS if all(L[g[i]] == L[i] for i in range(4))]


def word_orbits(k, f):
    """Orbit id of every word w in S4^{k+1} under (g, h) in G_f x G_f (w_l -> g w_l h for all l at once), inversion
    w_l -> w_l^{-1}, and permutations of the k site components (union-find by min-label propagation)."""
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
        for m in maps:
            np.minimum(lab, lab[m], out=lab)
        lab = lab[lab]
        if np.array_equal(lab, old):
            break
    uniq, oid = np.unique(lab, return_inverse=True)
    return oid.reshape((24,) * nl), len(uniq)


# ------------------------------------------------------------------ entry rules (literal, from the row patterns)
def parse_pattern(s):
    out = []
    for tok in s.split():
        out.append((tok[0], 1 if tok.endswith('*') else 0))
    assert len(out) == 4 and all(l in 'ab' for l, _ in out)
    return tuple(out)


def entry_rule(u, v):
    """Index rule of the entry |u><v| (partial transpose on the conjugated slots): (family, kpos, lpos) with
    entry[i; j] = X_f[k; l], k_s = (i or j)[slot] given by kpos[s] = ('i' | 'j', slot), l likewise by lpos."""
    assert all(cu == cv for (_, cu), (_, cv) in zip(u, v)), 'rows must share conjugation flags'
    unconj, conj = [], []
    for i in range(4):
        (lu, c), (lv, _) = u[i], v[i]
        if c == 0:
            unconj.append(('i', i, lu))
            conj.append(('j', i, lv))
        else:
            unconj.append(('j', i, lv))
            conj.append(('i', i, lu))
    letters = ''.join(sorted(x[2] for x in unconj))
    assert letters == ''.join(sorted(x[2] for x in conj)), 'unbalanced entry'
    fam = [f for f, L in FAMILY_LETTERS.items() if ''.join(sorted(L)) == letters]
    assert len(fam) == 1
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


# ------------------------------------------------------------------ literal operators (auxiliary qubit, cross-checks)
def digits(x, n, m):
    return [(x // n ** (m - 1 - s)) % n for s in range(m)]


def undigits(ds, n):
    r = 0
    for x in ds:
        r = r * n + x
    return r


def perm_op(n, p, m=4):
    ent = {}
    for src in itertools.product(range(n), repeat=m):
        tgt = [0] * m
        for i in range(m):
            tgt[p[i]] = src[i]
        ent[(undigits(tgt, n), undigits(src, n))] = 1
    return ent


def entry_op(n, p, kpos, lpos):
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
    J = np.asarray(J, dtype=object)
    OJ = np.zeros(J.shape, dtype=object)
    for (r, c), v in ent.items():
        OJ[r, :] += v * J[c, :]
    return J.T.dot(OJ)


def tr_replica(p, slot, order):
    """Closed form of Tr_slot V_p on four replicas, survivors relabelled by `order`: returns (e, q) with
    Tr_slot V_p = n^e V_q (e = 1 iff p fixes the slot)."""
    if p[slot] == slot:
        e = 1
        image = {i: p[i] for i in range(4) if i != slot}
    else:
        e = 0
        pre = inverse(p)[slot]
        image = {i: p[i] for i in range(4) if i != slot}
        image[pre] = p[slot]
    pos = {s: t for t, s in enumerate(order)}
    q = [None] * 3
    for i, j in image.items():
        q[pos[i]] = pos[j]
    return e, tuple(q)


# ------------------------------------------------------------------ diagram calculus
def op_edges(p, kpos, lpos):
    """Perfect matching on the 8 index positions (i-slots 0..3, j-slots 4..7) of entry_op(n, p, kpos, lpos)."""
    pos = lambda t: t[1] if t[0] == 'i' else 4 + t[1]
    return [(pos(kpos[p[i]]), pos(lpos[i])) for i in range(4)]


def perm_edges(q, m):
    """Matching of V_q on (C^n)^{xm} as an entry (rows = positions 0..m-1, columns m..2m-1): tgt[q[i]] = src[i]."""
    return [(q[i], m + i) for i in range(m)]


def gram_monomial(key_a, key_b, edges, m, nfix=None):
    """<D_a| O |D_b> = eps * n^cycles for all n >= 4 (eps in {0, 1}); with nfix = n: the value at that n exactly
    (top value t and bottom value n-1-r coincide iff t == n-1-r)."""
    adj = [[] for _ in range(2 * m)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    val = [None] * (2 * m)
    for base, key in ((0, key_a), (m, key_b)):
        pairs, fa, fb = key
        for a, b in pairs:
            adj[base + a].append(base + b)
            adj[base + b].append(base + a)
        for s, t in fa:
            val[base + s] = ('t', t)
        for s, r in fb:
            val[base + s] = ('b', r)
    for x in range(2 * m):
        assert len(adj[x]) == (1 if val[x] is not None else 2), 'malformed diagram key'
    seen = [False] * (2 * m)
    cycles, eps = 0, 1
    for st in range(2 * m):
        if seen[st]:
            continue
        comp, stack = [], [st]
        seen[st] = True
        while stack:
            x = stack.pop()
            comp.append(x)
            for y in adj[x]:
                if not seen[y]:
                    seen[y] = True
                    stack.append(y)
        fixed = [val[x] for x in comp if val[x] is not None]
        if not fixed:
            cycles += 1
            continue
        assert len(fixed) == 2
        (ka, va), (kb, vb) = fixed
        if ka == kb:
            if va != vb:
                eps = 0
        else:
            t, r = (va, -1 - vb) if ka == 't' else (vb, -1 - va)
            if nfix is None:
                assert t + r + 1 <= 3, 'top/bottom values could coincide for some n >= 4'
                eps = 0
            elif t != nfix - 1 - r:
                eps = 0
    return eps, cycles


class DiagramModule:
    """Compressed module J(n) = D(n) C (C integer, rows = diagram keys)."""

    def __init__(self, m, keys, C):
        self.m = m
        self.keys = [tuple(tuple(tuple(y) for y in x) for x in key) for key in keys]
        self.C = np.array([[int(x) for x in row] for row in C], dtype=object)
        self.dim = self.C.shape[1]
        self.f = len(self.keys[0][0])
        self.cache = {}

    def local_poly(self, edges):
        """{c: integer matrix dim x dim} with J^T O J = sum_c n^c M_c (O given by its matching)."""
        key = tuple(sorted(edges))
        if key not in self.cache:
            K = len(self.keys)
            G = {}
            for a in range(K):
                for b in range(K):
                    eps, c = gram_monomial(self.keys[a], self.keys[b], edges, self.m)
                    if eps:
                        G.setdefault(c, np.zeros((K, K), dtype=object))[a, b] += 1
            out = {c: self.C.T.dot(Gc).dot(self.C) for c, Gc in G.items()}
            assert all(c <= 2 * self.f for c in out), 'degree bound #cycles <= 2f violated'
            self.cache[key] = out
        return self.cache[key]

    def local_fixed(self, n, edges):
        """J(n)^T O J(n) at one integer n >= 1 (used for n < 4, where top/bottom collisions are possible)."""
        key = ('fixed', n, tuple(sorted(edges)))
        if key not in self.cache:
            K = len(self.keys)
            G = np.zeros((K, K), dtype=object)
            for a in range(K):
                for b in range(K):
                    eps, c = gram_monomial(self.keys[a], self.keys[b], edges, self.m, nfix=n)
                    G[a, b] = eps * n ** c
            self.cache[key] = self.C.T.dot(G).dot(self.C)
        return self.cache[key]

    def local_at(self, n, edges):
        if isinstance(n, int) and n < 4:
            return self.local_fixed(n, edges)
        P = self.local_poly(edges)
        out = np.zeros((self.dim, self.dim), dtype=object)
        for c, M in P.items():
            out = out + M * (n ** c)
        return out

    def local_s(self, s, edges):
        """s-scaled local map s^{2f} J(1/s)^T O J(1/s) = sum_c M_c s^{2f-c} (a polynomial in s; s may be 0)."""
        P = self.local_poly(edges)
        out = np.zeros((self.dim, self.dim), dtype=object)
        for c, M in P.items():
            out = out + M * (s ** (2 * self.f - c))
        return out


def objective_tensor_s(s, k):
    """c in s-scaled form (identical to objective_tensor at s = 1/n): per site 2 s^{4-c(p)} - s^{4-c(swap p)},
    divided by 2^k * 16; returns (tensor of Fractions/ints, denominator)."""
    swap = (3, 1, 2, 0)
    zs = [2 * s ** (4 - ncycles(p)) - s ** (4 - ncycles(compose(swap, p))) for p in PERMS]
    za = [2 ** ncycles(compose(swap, p)) for p in PERMS]
    C = np.array(1, dtype=object)
    for l in range(k):
        C = np.multiply.outer(C, np.array(zs, dtype=object))
    C = np.multiply.outer(C, np.array(za, dtype=object))
    return C, (2 ** k) * 16


def objective_tensor(n, k):
    """c on family '31' words before orbit summation, as (integer tensor, denominator)."""
    swap = (3, 1, 2, 0)
    zs = [2 * n ** ncycles(p) - n ** ncycles(compose(swap, p)) for p in PERMS]
    za = [2 ** ncycles(compose(swap, p)) for p in PERMS]
    C = np.array(1, dtype=object)
    for l in range(k):
        C = np.multiply.outer(C, np.array(zs, dtype=object))
    C = np.multiply.outer(C, np.array(za, dtype=object))
    L = (2 * n ** k) ** 4
    return C, (2 ** k) * L


# ------------------------------------------------------------------ exact helpers
def fz(A):
    A = np.asarray(A, dtype=object)
    return flint.fmpz_mat(A.shape[0], A.shape[1], [int(x) for x in A.ravel()])


def mode_product(T, A, axis):
    Tm = np.moveaxis(T, axis, 0)
    shp = Tm.shape
    R = fz(A) * fz(Tm.reshape(shp[0], -1))
    R = np.array([int(x) for x in R.entries()], dtype=object).reshape((A.shape[0],) + shp[1:])
    return np.moveaxis(R, 0, axis)


def psd_charpoly(Z):
    """Exact PSD test of a rational symmetric matrix by the sign pattern of its characteristic polynomial."""
    n = len(Z)
    den = 1
    for row in Z:
        for x in row:
            den = den * Fraction(x).denominator // math.gcd(den, Fraction(x).denominator)
    M = flint.fmpz_mat(n, n, [int(Fraction(x) * den) for row in Z for x in row])
    if M != M.transpose():
        return False
    cp = M.charpoly()
    co = [int(cp[i]) for i in range(n + 1)]
    return all(((-1) ** kk) * co[n - kk] >= 0 for kk in range(n + 1))


# ------------------------------------------------------------------ the verifier functional at local dimension n
def parse_site_key(key):
    """'<anything>|cut|f%d_lam_mu' -> (cut tuple, (f, lam, mu))."""
    _, cut, lab = key.split('|')
    cut = tuple(int(x) for x in cut.split(',')) if cut else ()
    f, lam, mu = lab.split('_')
    f = int(f[1:])
    lam = () if lam == 'e' else tuple(int(x) for x in lam)
    mu = () if mu == 'e' else tuple(int(x) for x in mu)
    return cut, (f, lam, mu)


class Relaxation:
    """The certificate functional L at local dimension n (mode 'n') or in s-SCALED form at s (mode 's', s = 1/n):
    site maps s^{2f} J(1/s)^T O J(1/s), site equality maps s^{1-e} J3^T V_q J3, objective in s-form.  In mode 's'
    the block multipliers passed in are P_t = Z_t / s^{delta_t} and the equality multipliers mu = lambda / s^k, so the
    returned orbit sums equal those of mode 'n' at n = 1/s (they are polynomials in s).
    blocks: list of dicts (kind, family, rows, modules = [site keys] * k + [aux key], W integer matrix);
    diagrams: {(m, cut): {label: (keys, C)}}; aux: {key: integer matrix (local dimension 2)};
    eq_groups: {name: {'parts': [{'family', 'sign', 'local': [(site|aux, slot, order, kind, mkeys)] * (k+1)}]}}."""

    def __init__(self, k, blocks, diagrams, aux, eq_groups, orbits):
        self.k, self.blocks, self.aux, self.eq_groups, self.orb = k, blocks, aux, eq_groups, orbits
        self.dmod = {}
        for (m, cut), labs in diagrams.items():
            for lab, (keys, C) in labs.items():
                self.dmod[(m, tuple(cut), tuple(lab))] = DiagramModule(m, keys, C)
        self.groups = {}
        for bi, b in enumerate(blocks):
            rows = [parse_pattern(u) for u in b['rows']]
            cut = b['modules'][0].split('|')[1]
            assert all(x.split('|')[1] == cut for x in b['modules'])
            for r in range(len(rows)):
                for s_ in range(len(rows)):
                    f, kpos, lpos = entry_rule(rows[r], rows[s_])
                    self.groups.setdefault((f, kpos, lpos, cut), []).append((bi, r, s_))
        self.gkeys = sorted(self.groups, key=str)
        self.auxcache = {}

    def site_module(self, key, m=4):
        cut, lab = parse_site_key(key)
        return self.dmod[(m, cut, lab)]

    def local_rows(self, key, typ, x, kpos, lpos, smode):
        """24 x dim^2 matrix: row p = vec(J^T entry_op(p) J) (site maps s-scaled in mode 's')."""
        if typ == 's':
            M = self.site_module(key)
            ev = M.local_s if smode else M.local_at
            return np.array([ev(x, op_edges(p, kpos, lpos)).ravel() for p in PERMS], dtype=object)
        ck = (key, kpos, lpos)
        if ck not in self.auxcache:
            J = np.array(self.aux[key], dtype=object)
            self.auxcache[ck] = np.array([sandwich(J, entry_op(2, p, kpos, lpos)).ravel() for p in PERMS],
                                         dtype=object)
        return self.auxcache[ck]

    def dims(self, key, typ):
        return self.site_module(key).dim if typ == 's' else len(self.aux[key][0])

    def contributions(self, x, smode, items_of_group, Zint, Dg, accum, sign=-1, Ldens=None):
        """Add sign * sum_blocks <B, local maps> / Dg to the orbit sums (local maps evaluated at x exactly; if they
        are rational, Ldens = common denominator handled by the caller through Dg)."""
        k, nl = self.k, self.k + 1
        for g in self.gkeys:
            items = items_of_group(g)
            if not items:
                continue
            f, kpos, lpos, cut = g
            labs = {'s': [], 'a': []}
            bymods = {}
            for bi, r, s_ in items:
                mods = tuple(self.blocks[bi]['modules'])
                bymods.setdefault(mods, []).append((bi, r, s_))
                for l, m in enumerate(mods):
                    typ = 'a' if l == k else 's'
                    if m not in labs[typ]:
                        labs[typ].append(m)
            off, A = {}, {}
            for typ in ('s', 'a'):
                o, cols = 0, []
                for m in labs[typ]:
                    off[m] = o
                    o += self.dims(m, typ) ** 2
                    cols.append(self.local_rows(m, typ, x, kpos, lpos, smode))
                A[typ] = np.hstack(cols)
            # rational x: scale the site maps to integers (common denominator) and remember the factor
            den_s = 1
            for v in A['s'].ravel():
                den_s = den_s * Fraction(v).denominator // math.gcd(den_s, Fraction(v).denominator)
            As = np.array([[int(Fraction(v) * den_s) for v in row] for row in A['s']], dtype=object)
            Ds, Da = As.shape[1], A['a'].shape[1]
            acc = np.zeros([Ds] * k + [Da], dtype=object)
            for mods, its in bymods.items():
                dims = [self.dims(m, 'a' if l == k else 's') for l, m in enumerate(mods)]
                nn = int(np.prod(dims))
                Bsum = flint.fmpz_mat(nn, nn)
                for bi, r, s_ in its:
                    W = self.blocks[bi]['W']
                    Wr = flint.fmpz_mat(nn, len(W[0]), [int(v) for row in W[r * nn:(r + 1) * nn] for v in row])
                    Ws = flint.fmpz_mat(nn, len(W[0]), [int(v) for row in W[s_ * nn:(s_ + 1) * nn] for v in row])
                    Bsum += Wr * Zint[bi] * Ws.transpose()
                T = np.array([int(v) for v in Bsum.entries()], dtype=object).reshape(dims + dims)
                order = []
                for i in range(nl):
                    order += [i, nl + i]
                T = T.transpose(order).reshape([v * v for v in dims])
                sl = tuple(slice(off[m], off[m] + self.dims(m, 'a' if l == k else 's') ** 2)
                           for l, m in enumerate(mods))
                acc[sl] += T
            for l in range(nl):
                acc = mode_product(acc, A['a'] if l == k else As, l)
            self.add_orbit_sums(accum, f, acc, Dg * den_s ** k, sign)

    def add_orbit_sums(self, accum, f, T, den, sign):
        oid, nor = self.orb[f]
        flat = np.asarray(T, dtype=object).ravel()
        o = oid.ravel()
        order = np.argsort(o, kind='stable')
        so = o[order]
        starts = np.flatnonzero(np.r_[True, so[1:] != so[:-1]])
        vals = np.add.reduceat(flat[order], starts)
        Acc = accum[f]
        for idx, v in zip(so[starts], vals):
            if v:
                Acc[int(idx)] += Fraction(sign * v, den) if isinstance(v, Fraction) else Fraction(sign * int(v), den)

    def eq_local(self, x, spec, smode):
        """Equality local map rows for one slot (site: x = n or s; aux: local dimension 2)."""
        n0, slot, order, kind, mkeys = spec
        site = (n0 == 'S') if isinstance(n0, str) else (n0 != 2)
        blocks = []
        for mk in mkeys:
            cols = []
            for p in PERMS:
                if kind == 'del':
                    e, q = tr_replica(p, slot, tuple(order))
                    if site:
                        _, lab3 = parse_site_key('x||' + mk.split('|')[-1])     # 'eq3|<n>|label': cut ()
                        Mq = self.dmod[(3, (), lab3)].local_at(1, perm_edges(q, 3))   # f = 0: n-independent
                        M = (x ** (1 - e) if smode else x ** e) * Mq
                    else:
                        Mq = sandwich(np.array(self.aux[mk], dtype=object), perm_op(2, q, 3))
                        M = (2 ** e) * Mq
                else:                                      # 'stiefel_aux': 2 V_p - I_slot (x) Tr_slot V_p (aux only)
                    assert not site
                    J = np.array(self.aux[mk], dtype=object)
                    nat = tuple(i for i in range(4) if i != slot)
                    e, q = tr_replica(p, slot, nat)
                    ee = [None] * 4
                    ee[slot] = slot
                    for i_new, i_old in enumerate(nat):
                        ee[i_old] = nat[q[i_new]]
                    M = 2 * sandwich(J, perm_op(2, p)) - (2 ** e) * sandwich(J, perm_op(2, tuple(ee)))
                cols.append(np.asarray(M, dtype=object).ravel())
            blocks.append(np.array(cols, dtype=object).T)
        return np.vstack(blocks)

    def residual(self, x, Zs, lam, smode=False):
        """Orbit sums of L ({family: [Fraction]}).  Mode 'n' (smode False): x = n, Zs = Z_t, lam = lambda.
        Mode 's': x = s (Fraction), Zs = P_t = Z_t / s^delta_t, lam = mu = lambda / s^k."""
        k = self.k
        accum = {f: [Fraction(0)] * self.orb[f][1] for f in FAMILIES}
        Dg = 1
        for Z in Zs:
            for row in Z:
                for v in row:
                    Dg = Dg * Fraction(v).denominator // math.gcd(Dg, Fraction(v).denominator)
        Zint = [flint.fmpz_mat(len(Z), len(Z), [int(Fraction(v) * Dg) for row in Z for v in row]) for Z in Zs]
        self.contributions(x, smode, lambda g: self.groups[g], Zint, Dg, accum, sign=-1)
        C, den = objective_tensor_s(x, k) if smode else objective_tensor(x, k)
        dC = 1
        for v in np.asarray(C, dtype=object).ravel():
            dC = dC * Fraction(v).denominator // math.gcd(dC, Fraction(v).denominator)
        Ci = np.array([int(Fraction(v) * dC) for v in np.asarray(C, dtype=object).ravel()], dtype=object).reshape(C.shape)
        self.add_orbit_sums(accum, '31', Ci, den * dC, 1)
        for gname, ginfo in self.eq_groups.items():
            lamv = lam.get(gname, {})
            if not lamv:
                continue
            lden = 1
            for v in lamv.values():
                lden = lden * Fraction(v).denominator // math.gcd(lden, Fraction(v).denominator)
            for part in ginfo['parts']:
                Es = [self.eq_local(x, part['local'][l], smode) for l in range(k + 1)]
                eden = 1
                for E_ in Es:
                    for v in E_.ravel():
                        eden = eden * Fraction(v).denominator // math.gcd(eden, Fraction(v).denominator)
                Es = [np.array([[int(Fraction(v) * eden) for v in row] for row in E_], dtype=object) for E_ in Es]
                Lt = np.zeros([E_.shape[0] for E_ in Es], dtype=object)
                for o, v in lamv.items():
                    Lt[tuple(o)] += int(Fraction(v) * lden)
                T = Lt
                for l in range(k + 1):
                    T = mode_product(T, Es[l].T, l)
                self.add_orbit_sums(accum, part['family'], part['sign'] * T, lden * eden ** (k + 1), -1)
        return accum


# ------------------------------------------------------------------ columns modulo primes (batched per type)
def mode_product_mod(T, A, axis, p):
    """T int64 tensor (entries in [0, p)), A int64 matrix (r x T.shape[axis]) with entries in [0, p): A x_axis T mod p.
    Requires p < 2^26 and T.shape[axis] <= 16, so every partial sum stays below 2^56."""
    Tm = np.moveaxis(T, axis, 0)
    shp = Tm.shape
    assert shp[0] <= 16
    R = (A @ Tm.reshape(shp[0], -1)) % p
    return np.moveaxis(R.reshape((A.shape[0],) + shp[1:]), 0, axis)


def orbit_sums_mod(T, oid_flat, order, starts, so_starts, nor, p):
    """T int64 tensor (..., 24^{k+1}) mod p -> (..., nor) orbit sums mod p."""
    flat = T.reshape(T.shape[0], -1)[:, order]
    out = np.zeros((T.shape[0], nor), dtype=np.int64)
    sums = np.add.reduceat(flat, starts, axis=1) % p          # each orbit <= 24^4 terms < 2^29 -> < 2^48
    out[:, so_starts] = sums
    return out


class ColumnEngine:
    """Verifier columns (contribution of single Gram entries / equality items) modulo a prime p, at x = n (mode 'n')
    or x = s (mode 's', s-scaled columns s^{delta_t} V_t(1/s) and s^k e(1/s)); x is given as an integer mod p."""

    def __init__(self, rx):
        self.rx = rx
        self.ord = {}
        for f in FAMILIES:
            oid, nor = rx.orb[f]
            o = oid.ravel()
            order = np.argsort(o, kind='stable')
            so = o[order]
            starts = np.flatnonzero(np.r_[True, so[1:] != so[:-1]])
            self.ord[f] = (order, starts, so[starts], nor)
        self.block_pairs = {}
        for g, items in rx.groups.items():
            for bi, r, s_ in items:
                self.block_pairs.setdefault(bi, []).append((g, r, s_))
        self.lcache = {}

    def local_mod(self, key, typ, x, smode, kpos, lpos, p):
        ck = (key, typ, x, smode, kpos, lpos, p)
        if ck not in self.lcache:
            A = self.rx.local_rows(key, typ, x, kpos, lpos, smode)
            self.lcache[ck] = np.array([[int(v) % p for v in row] for row in A], dtype=np.int64)
        return self.lcache[ck]

    def type_columns(self, x, smode, bi, Zlist, p, chunk=48):
        """Zlist: integer symmetric matrices (r_t x r_t) -> {family: int64 array (len(Zlist), n_orbits)} of the
        contribution sum_{r,s} <W_r Z W_s^T, local maps> modulo p (no sign).  Processed in chunks (memory)."""
        if len(Zlist) > chunk:
            parts = [self.type_columns(x, smode, bi, Zlist[i:i + chunk], p, chunk) for i in range(0, len(Zlist), chunk)]
            return {f: np.concatenate([q[f] for q in parts], axis=0) for f in parts[0]}
        rx, k = self.rx, self.rx.k
        b = rx.blocks[bi]
        mods = b['modules']
        dims = [rx.dims(m, 'a' if l == k else 's') for l, m in enumerate(mods)]
        nn = int(np.prod(dims))
        assert p < 2 ** 26 and len(b['W'][0]) <= 64        # products < 2^52, sums over <= 64 terms < 2^58
        W = np.array([[int(v) % p for v in row] for row in b['W']], dtype=np.int64)
        out = {}
        Zs = np.array([[[int(v) % p for v in row] for row in Z] for Z in Zlist], dtype=np.int64)
        for (g, r, s_) in self.block_pairs[bi]:
            f, kpos, lpos, cut = g
            Wr, Ws = W[r * nn:(r + 1) * nn], W[s_ * nn:(s_ + 1) * nn]
            WZ = np.einsum('ia,nab->nib', Wr, Zs) % p
            B = np.einsum('nib,jb->nij', WZ, Ws) % p
            T = B.reshape([len(Zlist)] + dims + dims)
            order = [0]
            for i in range(k + 1):
                order += [1 + i, 1 + (k + 1) + i]
            T = T.transpose(order).reshape([len(Zlist)] + [v * v for v in dims])
            for l, m in enumerate(mods):
                A = self.local_mod(m, 'a' if l == k else 's', x, smode, kpos, lpos, p)
                T = mode_product_mod(T, A, 1 + l, p)
            ordr, starts, sost, nor = self.ord[f]
            cs = orbit_sums_mod(T, None, ordr, starts, sost, nor, p)
            out[f] = (out[f] + cs) % p if f in out else cs
        return out

    def eq_columns(self, x, smode, items, p):
        """For each item (group, o): the contribution of mu (or lambda) = 1 for that item, modulo p (no sign)."""
        rx, k = self.rx, self.rx.k
        out = {f: np.zeros((len(items), rx.orb[f][1]), dtype=np.int64) for f in FAMILIES}
        cache = {}
        for j, (g, o) in enumerate(items):
            for pi_, part in enumerate(rx.eq_groups[g]['parts']):
                key = (g, pi_)
                if key not in cache:
                    cache[key] = [np.array([[int(v) % p for v in row] for row in rx.eq_local(x, part['local'][l], smode)],
                                           dtype=np.int64) for l in range(k + 1)]
                Es = cache[key]
                T = Es[0][o[0]]
                for l in range(1, k + 1):
                    T = np.multiply.outer(T, Es[l][o[l]]) % p
                order, starts, sost, nor = self.ord[part['family']]
                sums = np.add.reduceat(T.ravel()[order], starts) % p
                f = part['family']
                out[f][j, sost] = (out[f][j, sost] + (part['sign'] % p) * sums) % p
        return out


# ------------------------------------------------------------------ the relaxation is fixed by this code, not by data
GRAM_ROWS = ('a a b a*', 'b b a b*')                  # coupled Gram class of Zenodo 23134454
GRAM2_ROWS = ('a a a* b*', 'a b b* b*')               # second coupled Gram class (gram2)
EQ_CANON = {
    'stiefel31': [('31', 1, [('S', 0, (1, 2, 3), 'del')] * 3 + [('A', 0, (1, 2, 3), 'stiefel_aux')])],
    'stiefel22': [('22', 1, [('S', 0, (1, 2, 3), 'del')] * 3 + [('A', 0, (1, 2, 3), 'stiefel_aux')])],
    'stiefel13': [('13', 1, [('S', 3, (0, 1, 2), 'del')] * 3 + [('A', 3, (0, 1, 2), 'stiefel_aux')])],
    'aab': [('31', 1, [('S', 2, (0, 1, 3), 'del')] * 3 + [('A', 2, (0, 1, 3), 'del')]),
            ('22', -1, [('S', 2, (0, 1, 3), 'del')] * 3 + [('A', 2, (0, 1, 3), 'del')])],
    'abb': [('22', 1, [('S', 1, (0, 2, 3), 'del')] * 3 + [('A', 1, (0, 2, 3), 'del')]),
            ('13', -1, [('S', 1, (3, 0, 2), 'del')] * 3 + [('A', 1, (3, 0, 2), 'del')])],
}


def check_definition(pkg):
    """Assert that the certificate only uses the validated multiplier classes and equality functionals:
    single-row blocks = whole-replica partial transposes of a family's moment operator (letters of the family, the
    starred slots = the modules' cut); two-row blocks = the gram / gram2 classes; equality groups = the five canonical
    groups (Stiefel contrasts at the a-replicas, AAB / ABB marginals).  Module bases are arbitrary compressions."""
    k = pkg['k']
    for t in pkg['types']:
        rows = tuple(t['rows'])
        cut = t['modules'][0].split('|')[1]
        cutset = set(int(x) for x in cut.split(',')) if cut else set()
        assert all(m.split('|')[1] == cut for m in t['modules'])
        assert len(t['modules']) == k + 1 and t['modules'][k].startswith('A|') and all(
            m.startswith('S|') for m in t['modules'][:k])
        if t['kind'] == 'src':
            assert len(rows) == 1
            pat = parse_pattern(rows[0])
            letters = ''.join(sorted(l for l, _ in pat))
            assert letters in {''.join(sorted(L)) for L in FAMILY_LETTERS.values()}
            assert {i for i, (_, c) in enumerate(pat) if c} == cutset
            assert entry_rule(pat, pat)[0] == t['family']
        elif t['kind'] == 'gram':
            assert rows == GRAM_ROWS and cutset == {3}
        elif t['kind'] == 'gram2':
            assert rows == GRAM2_ROWS and cutset == {2, 3}
        else:
            raise AssertionError('unknown multiplier class %s' % t['kind'])
    assert set(pkg['eq_groups']) == set(EQ_CANON)
    for g, parts in EQ_CANON.items():
        got = pkg['eq_groups'][g]['parts']
        assert len(got) == len(parts)
        for (fam, sign, specs), part in zip(parts, got):
            assert part['family'] == fam and part['sign'] == sign
            assert [tuple(x[:4]) for x in part['local']] == [tuple(sp) for sp in specs]
    return True
