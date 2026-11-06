"""Physical moment points for the relaxation at general k (four-replica product states).

physical_coords(R, a, b) returns the variable vector y of the twirled, site-averaged,
conjugation-averaged tuple (X_31, X_22, X_13) built from unit vectors a (isometric lifting) and b.
"""
import itertools
import sys

import numpy as np

sys.path.insert(0, '<ROOT>/dim')
from relax import P4, I4, FAMILIES, FAMILY_GROUP
from local import compose, inverse, ncycles, perms

LETTERS = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'
INV4 = [I4[inverse(p)] for p in P4]
MUL4 = np.array([[I4[compose(p, q)] for q in P4] for p in P4])


def moment_tensor(k, d, vecs, G):
    """t[w] = <psi|P_w|psi> for all w in S4^{k+1}, psi = vecs[0] x .. x vecs[3] (each in
    (C^d)^{xk} x C^2), using invariance t[g w h] = t[w] (g, h in G) and t[w^-1] = conj t[w]."""
    nl = k + 1
    shape = [d] * k + [2]
    psis = [np.asarray(v).reshape(shape) for v in vecs]
    gidx = [I4[g] for g in G]
    t = np.zeros((24,) * nl, dtype=complex)
    done = np.zeros((24,) * nl, dtype=bool)
    lett = [[LETTERS[r * nl + l] for l in range(nl)] for r in range(4)]
    bra = ','.join(''.join(lett[s]) for s in range(4))
    ncalls = 0
    for w in itertools.product(range(24), repeat=nl):
        if done[w]:
            continue
        ket = ','.join(''.join(lett[P4[w[l]][r]][l] for l in range(nl)) for r in range(4))
        expr = bra + ',' + ket + '->'
        val = np.einsum(expr, *[p.conj() for p in psis], *psis, optimize='greedy')
        ncalls += 1
        for g in gidx:
            for h in gidx:
                ww = tuple(int(MUL4[MUL4[g, x], h]) for x in w)
                t[ww] = val
                done[ww] = True
                wi = tuple(INV4[x] for x in ww)
                t[wi] = np.conj(val)
                done[wi] = True
    return t, ncalls


def physical_x(k, d, vecs, G, L, nproc=1):
    if nproc > 1:
        t, ncalls = moment_tensor_par(k, d, vecs, G, nproc)
    else:
        t, ncalls = moment_tensor(k, d, vecs, G)
    tt = np.zeros(t.shape)
    for s in perms(k):
        tt += np.transpose(t.real, list(s) + [k])
    t = tt / len(perms(k))
    Gs = np.array([[float(d ** ncycles(compose(inverse(v), w))) for w in P4] for v in P4])
    Ga = np.array([[2.0 ** ncycles(compose(inverse(v), w)) for w in P4] for v in P4])
    pis, pia = np.linalg.pinv(Gs), np.linalg.pinv(Ga)
    x = t
    for l in range(k + 1):
        M = pia if l == k else pis
        x = np.moveaxis(np.tensordot(M, x, axes=(1, l)), 0, l)
    return L * x


def coords_from_x(R, f, x):
    ls, la = R.loc['s', ()], R.loc['a', ()]
    F = x
    for l in range(R.k + 1):
        M = la.FT if l == R.k else ls.FT
        F = np.moveaxis(np.tensordot(M, F, axes=(1, l)), 0, l)
    y = np.zeros(R.nvar[f])
    resid = 0.0
    for b in R.vars[f]:
        ob = dict(st=b['st'], ai=b['ai'], dims=b['dims'], U=b['U'])
        Sh = R.extract(F[None], ob, ())[0]
        coef = np.array([np.sum(B * Sh) for B in b['basis']])
        y[b['off']:b['off'] + len(coef)] = coef
        resid = max(resid, np.abs(Sh - sum(c * B for c, B in zip(coef, b['basis']))).max())
    return y, resid


def ab_from_C(C, k, d):
    """Isometric lifting of a rank<=2 matrix C (d^k x d^k), normalised to ||C||_F^2 = 1/2."""
    C = C / (np.linalg.norm(C) * np.sqrt(2))
    U, s, Vh = np.linalg.svd(C)
    A = U[:, :2]
    B = 2 * C.conj().T @ A
    a = A.reshape(-1) / np.sqrt(2)
    b = B.reshape(-1) / np.sqrt(2)
    return a, b, C


def random_C(k, d, rng):
    D = d ** k
    X = rng.normal(size=(D, 2)) + 1j * rng.normal(size=(D, 2))
    Y = rng.normal(size=(D, 2)) + 1j * rng.normal(size=(D, 2))
    return X @ Y.conj().T


def physical_y(R, a, b, verbose=False, nproc=1):
    vec = {'31': [a, a, a, b], '22': [a, a, b, b], '13': [b, b, b, a]}
    y = np.zeros(R.N)
    for f in FAMILIES:
        x = physical_x(R.k, R.d, vec[f], FAMILY_GROUP[f], R.L, nproc)
        yf, resid = coords_from_x(R, f, x)
        if verbose:
            print(f, 'projection residual %.2e' % resid, flush=True)
        y[R.foff[f]:R.foff[f] + R.nvar[f]] = yf
    return y


def qk(C, k, d):
    T = C.reshape([d] * k + [d] * k)
    tot = 0.0
    for J in itertools.product((0, 1), repeat=k):
        rows = [i for i in range(k) if not J[i]]
        row_l = [LETTERS[i] for i in range(k)]
        col_l = [LETTERS[k + i] if not J[i] else LETTERS[i] for i in range(k)]
        out = ''.join(LETTERS[i] for i in rows) + ''.join(LETTERS[k + i] for i in rows)
        Y = np.einsum(''.join(row_l) + ''.join(col_l) + '->' + out, T)
        tot += (-0.5) ** sum(J) * np.sum(np.abs(Y) ** 2)
    return tot


def _orbit_reps(nl, gidx):
    """Representatives of orbits of S4^{nl} under w -> g w h (g, h in G) and inversion."""
    done = np.zeros((24,) * nl, dtype=bool)
    reps = []
    orbits = []
    for w in itertools.product(range(24), repeat=nl):
        if done[w]:
            continue
        imgs, invs = set(), set()
        for g in gidx:
            for h in gidx:
                ww = tuple(int(MUL4[MUL4[g, x], h]) for x in w)
                imgs.add(ww)
                invs.add(tuple(INV4[x] for x in ww))
        for ww in imgs | invs:
            done[ww] = True
        reps.append(w)
        orbits.append((sorted(imgs), sorted(invs - imgs)))
    return reps, orbits


def _einsum_chunk(args):
    psis, words, nl = args
    lett = [[LETTERS[r * nl + l] for l in range(nl)] for r in range(4)]
    bra = ','.join(''.join(lett[s]) for s in range(4))
    conj = [p.conj() for p in psis]
    out = []
    for w in words:
        ket = ','.join(''.join(lett[P4[w[l]][r]][l] for l in range(nl)) for r in range(4))
        out.append(np.einsum(bra + ',' + ket + '->', *conj, *psis, optimize='greedy'))
    return out


def moment_tensor_par(k, d, vecs, G, nproc=16):
    import multiprocessing as mp
    nl = k + 1
    shape = [d] * k + [2]
    psis = [np.asarray(v).reshape(shape) for v in vecs]
    gidx = [I4[g] for g in G]
    reps, orbits = _orbit_reps(nl, gidx)
    chunks = [reps[i::nproc] for i in range(nproc)]
    with mp.get_context('fork').Pool(nproc) as pool:
        res = pool.map(_einsum_chunk, [(psis, c, nl) for c in chunks])
    vals = {}
    for c, r in zip(chunks, res):
        for w, v in zip(c, r):
            vals[w] = v
    t = np.zeros((24,) * nl, dtype=complex)
    for w, (imgs, invs) in zip(reps, orbits):
        v = vals[w]
        for ww in imgs:
            t[ww] = v
        for ww in invs:
            t[ww] = np.conj(v)
    return t, len(reps)
