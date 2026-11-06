"""Uniform (diagram) form of the module bases J(n): for every (m, cut, label) find an n-independent rational matrix C
with J(n) = D(n) C, where the columns of D(n) are the diagram vectors
    D_{pairs, fill}(n) = sum_{j_1..j_f in [n]} e_x,   x = j_i on the contraction pair (a_i, b_i) (a_i non-cut, b_i cut),
                         top values 0,1,.. (rows of lam) on the other non-cut slots, n-1, n-2,.. (rows of mu) on the
                         other cut slots (all distinct fillings).
Checked exactly for n in NS.  Consequence (loop counting): <D_i(n)| V_p^Gamma |D_j(n)> = n^{#free loops} x [fixed
values consistent], so FT(n) = C^T [<D|V^Gamma|D>](n) C is a polynomial of degree <= 4 for EVERY n >= 4 and equals the
interpolated ftpoly data.   Usage: diagram_check.py"""
import sys, itertools, time
sys.path.insert(0, '<ROOT>/dim')
import sympy as sp
from local import module_data, labels


def fillings(slots, values):
    out = set()
    for perm in itertools.permutations(values):
        out.add(tuple(zip(slots, perm)))
    return sorted(out)


def candidates(m, cut, lab, n):
    f, lam, mu = lab
    nc = [s for s in range(m) if s not in cut]
    cs = list(cut)
    top = [r for r, x in enumerate(lam) for _ in range(x)]
    bot = [-1 - r for r, x in enumerate(mu) for _ in range(x)]        # symbolic: -1-r means value n-1-r
    out = []
    for A in itertools.combinations(nc, f):
        for B in itertools.permutations(cs, f):
            pairs = list(zip(A, B))
            rest_nc = [s for s in nc if s not in A]
            rest_c = [s for s in cs if s not in B]
            for fa in fillings(rest_nc, top):
                for fb in fillings(rest_c, bot):
                    key = (tuple(sorted(pairs)), fa, fb)
                    out.append(key)
    out = sorted(set(out))
    vecs = []
    for pairs, fa, fb in out:
        v = {}
        for js in itertools.product(range(n), repeat=len(pairs)):
            x = [None] * m
            for (a, b), j in zip(pairs, js):
                x[a] = j; x[b] = j
            for s, val in fa:
                x[s] = val
            for s, val in fb:
                x[s] = n + val
            v[tuple(x)] = v.get(tuple(x), 0) + 1
        vecs.append(v)
    return out, vecs


def check(m, cut, n0, NS):
    t0 = time.time()
    ok_all = True
    data0 = module_data(m, cut, n0)
    Cs = {}
    for lab in data0:
        J0, W0 = data0[lab]['J'], data0[lab]['basis']
        keys, vecs = candidates(m, cut, lab, n0)
        Widx = {x: i for i, x in enumerate(W0)}
        Dm = sp.zeros(len(W0), len(vecs))
        for j, v in enumerate(vecs):
            for x, cf in v.items():
                assert x in Widx, ('candidate outside weight space', m, cut, lab, x)
                Dm[Widx[x], j] = cf
        # solve Dm C = J0 (least-norm exact via RREF on [Dm | J0])
        sol, params = Dm.gauss_jordan_solve(J0)
        C = sol.subs({p: 0 for p in params})
        assert Dm * C == J0
        Cs[lab] = (keys, C)
    for n in NS:
        data = module_data(m, cut, n)
        assert list(data) == list(data0), ('label set differs', m, cut, n)
        for lab in data:
            J, W = data[lab]['J'], data[lab]['basis']
            keys, C = Cs[lab]
            keys_n, vecs = candidates(m, cut, lab, n)
            assert keys_n == keys
            Widx = {x: i for i, x in enumerate(W)}
            Dm = sp.zeros(len(W), len(vecs))
            for j, v in enumerate(vecs):
                for x, cf in v.items():
                    Dm[Widx[x], j] = cf
            if Dm * C != J:
                ok_all = False
                print('  MISMATCH m=%d cut=%s n=%d label %s' % (m, cut, n, lab), flush=True)
    print('m=%d cut=%-7s labels %2d: J(n) = D(n) C for n in %s: %s  (%.0fs)' % (m, str(cut), len(data0), NS, ok_all, time.time() - t0), flush=True)
    return ok_all, Cs


if __name__ == '__main__':
    import pickle
    res = {}
    allok = True
    for cut in [(), (3,), (0,), (2,), (0, 1), (0, 2), (2, 3)]:
        ok, Cs = check(4, cut, 8, [4, 5, 6, 7, 9, 10])
        res[(4, cut)] = Cs
        allok &= ok
    ok, Cs = check(3, (), 6, [3, 4, 5, 7, 8])
    res[(3, ())] = Cs
    allok &= ok
    pickle.dump({k: {lab: (keys, [[str(x) for x in C.row(i)] for i in range(C.rows)]) for lab, (keys, C) in v.items()} for k, v in res.items()},
                open('<ROOT>/dim/uni/diagram_C.pkl', 'wb'))
    print('ALL UNIFORM:', allok)
