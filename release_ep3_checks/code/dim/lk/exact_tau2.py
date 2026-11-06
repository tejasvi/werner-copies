"""Exact genuine generators of T*: copy-symmetrised real moments (orbit-representative coordinates) of exact
Gaussian-integer zero modes and their exact first-order tangent derivatives:
  dense (support 2): J = 1, 2, 3 zero modes, Stiefel tangent of a, sphere tangent of b;
  factorised (support 4): J = 1 zero modes a = Phi (x) u, b = Phi (x) v, tangents psi (x) mu (mu _|_ u), psi' (x) nu (nu _|_ v).
All moments are Gaussian integers computed in float64 with |values| < 2^50 (checked) -> exact.  Generators are kept when
they raise the rank (mod p = 2^61-1); the final rank is recomputed exactly over Q.
Usage: exact_tau2.py out.pkl [target] [seed]"""
import sys, time, pickle
sys.path.insert(0, '<ROOT>/dim')
sys.path.insert(0, '<ROOT>/dim/lk')
import numpy as np
import flint
from fractions import Fraction
from local import perms
from relax import FAMILIES
from tcoords import reps
from fastmom import moments
from factmom import prod_moments_dirs
from exact_zero_modes import zero_mode_vectors

outp = sys.argv[1]; target = int(sys.argv[2]) if len(sys.argv) > 2 else 107
rng = np.random.default_rng(int(sys.argv[3]) if len(sys.argv) > 3 else 29)
k = 3
NA = {'31': 3, '22': 2, '13': 1}; NB = {'31': 1, '22': 2, '13': 3}
PAT = {'31': 'aaab', '22': 'aabb', '13': 'bbba'}
P = 2 ** 61 - 1


def gint(v):
    r = np.round(v.real); i = np.round(v.imag)
    assert np.abs(v.real - r).max() < 1e-6 and np.abs(v.imag - i).max() < 1e-6
    return r + 1j * i


def sym_rep_int(t, f):
    tr = np.round(t.real)
    assert np.abs(t.real - tr).max() < 1e-3 and np.abs(tr).max() < 2.0 ** 50, (np.abs(t.real - tr).max(), np.abs(tr).max())
    tt = np.zeros(t.shape)
    for s in perms(k):
        tt += np.transpose(tr, list(s) + [k])
    R = reps[f]
    return [int(x) for x in tt[R[:, 0], R[:, 1], R[:, 2], R[:, 3]]]


def dense_generators(J):
    ds = 2
    dims = [ds] * k + [2]
    a, b, s_, C, N, g = zero_mode_vectors(J, 2, rng)
    a = gint(a); b = gint(b)
    A = a.reshape(-1, 2)
    G = A.conj().T @ A
    Nn = int(round(G[0, 0].real))
    W = rng.integers(-1, 2, A.shape) + 1j * rng.integers(-1, 2, A.shape)
    H = A.conj().T @ W
    al = gint(2 * Nn * W - A @ (H + H.conj().T)).reshape(-1)
    Wb = rng.integers(-1, 2, b.shape) + 1j * rng.integers(-1, 2, b.shape)
    Nb = int(round(np.vdot(b, b).real)); Na = int(round(np.vdot(a, a).real))
    be = gint(Nb * Wb - np.real(np.vdot(b, Wb)) * b)
    vec = {'31': [a, a, a, b], '22': [a, a, b, b], '13': [b, b, b, a]}
    out = {'tau': [], 'Da': [], 'Db': []}
    for f in FAMILIES:
        da = [al if c == 'a' else 0 * b for c in PAT[f]]
        db = [be if c == 'b' else 0 * a for c in PAT[f]]
        t, dta = moments(vec[f], dims, da)
        _, dtb = moments(vec[f], dims, db)
        den = 6 * Na ** NA[f] * Nb ** NB[f]
        for key, T in (('tau', t), ('Da', dta), ('Db', dtb)):
            out[key] += [Fraction(x, den) for x in sym_rep_int(T, f)]
    spec = dict(kind='dense', J=J, a=a.tolist(), b=b.tolist(), al=al.tolist(), be=be.tolist())
    return out, spec


def j1_factor_generators(ds):
    def gi(*s):
        return rng.integers(-1, 2, s) + 1j * rng.integers(-1, 2, s)
    while True:
        u = gi(ds, ds); v = gi(ds, ds)
        if np.vdot(u, u).real > 0 and np.vdot(v, v).real > 0:
            break
    Phi = np.zeros((ds, 2)); Phi[0, 0] = Phi[1, 1] = 1
    nu2 = int(round(np.vdot(u, u).real)); nv2 = int(round(np.vdot(v, v).real))
    Na, Nb = 2 * nu2, 2 * nv2
    w = gi(ds, ds); mu = gint(nu2 * w - np.vdot(u, w) * u)
    w2 = gi(ds, ds); nu = gint(nv2 * w2 - np.vdot(v, w2) * v)
    psi = gi(ds, 2); psi2 = gi(ds, 2)
    out = {'tau': [], 'Da': [], 'Db': []}
    for f in FAMILIES:
        A = [Phi] * 4
        B = [u if c == 'a' else v for c in PAT[f]]
        den = 6 * Na ** NA[f] * Nb ** NB[f]
        ta, dta = prod_moments_dirs(A, B, [[(psi, mu)] if c == 'a' else [] for c in PAT[f]])
        _, dtb = prod_moments_dirs(A, B, [[(psi2, nu)] if c == 'b' else [] for c in PAT[f]])
        for key, T in (('tau', ta), ('Da', dta), ('Db', dtb)):
            out[key] += [Fraction(x, den) for x in sym_rep_int(T, f)]
    spec = dict(kind='j1fact', ds=ds, u=u.tolist(), v=v.tolist(), psi=psi.tolist(), mu=mu.tolist(), psi2=psi2.tolist(), nu=nu.tolist())
    return out, spec


def modrow(v):
    return [int(x.numerator % P) * pow(x.denominator % P, -1, P) % P for x in v]


if __name__ == '__main__':
    t0 = time.time()
    rows, specs = [], []
    Mp = None
    rank = 0
    it = 0
    sched = ['d1', 'd2', 'd3', 'f4']
    while rank < target and it < 600:
        kind = sched[it % 4]
        gen, spec = j1_factor_generators(4) if kind == 'f4' else dense_generators(int(kind[1]))
        for key in ('tau', 'Da', 'Db'):
            v = gen[key]
            cand = rows + [v]
            M = flint.nmod_mat(len(cand), len(v), [x for r in (rowsmod + [modrow(v)] if rows else [modrow(v)]) for x in r], P) if False else None
            mv = modrow(v)
            Mm = flint.nmod_mat(len(rows) + 1, len(v), [x for r in ([] if not rows else rows_mod) for x in r] + mv, P)
            r = Mm.rank()
            if r > rank:
                rows.append(v)
                rows_mod = (rows_mod if len(rows) > 1 else []) + [mv]
                specs.append(dict(spec, gen=key))
                rank = r
        it += 1
        if it % 8 == 0:
            print('generator sets %d: rank (mod p) %d  %.0fs' % (it, rank, time.time() - t0), flush=True)
    Mq = flint.fmpq_mat(len(rows), len(rows[0]), [flint.fmpq(x.numerator, x.denominator) for r in rows for x in r])
    er = Mq.rank()
    print('kept %d generators from %d sets; exact rank over Q: %d' % (len(rows), it, er), flush=True)
    pickle.dump(dict(tau=[[str(x) for x in r] for r in rows], specs=specs, rank=er), open(outp, 'wb'))
