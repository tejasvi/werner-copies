"""Hypothesis: F_var(n) = G(n)^{-1} T* with T* n-independent (moment coordinates).  Test via left kernels."""
import sys, time
sys.path.insert(0, '<ROOT>/dim')
import numpy as np
from local import compose, inverse, ncycles
from relax import P4, FAMILIES
from exact_cert import word_orbits

k = 3
orb = {f: word_orbits(k, f) for f in FAMILIES}
reps = {}
for f in FAMILIES:
    oid, no = orb[f]
    flat = oid.ravel()
    first = np.full(no, -1)
    idx = np.arange(flat.size)
    order = np.argsort(flat, kind='stable')
    so = flat[order]
    starts = np.flatnonzero(np.r_[True, so[1:] != so[:-1]])
    first[so[starts]] = order[starts]
    reps[f] = np.array(np.unravel_index(first, oid.shape)).T


def Gorb(n):
    Gs = np.array([[float(n) ** ncycles(compose(inverse(v), w)) for w in P4] for v in P4])
    Ga = np.array([[2.0 ** ncycles(compose(inverse(v), w)) for w in P4] for v in P4])
    blocks = []
    for f in FAMILIES:
        oid, no = orb[f]
        M = np.zeros((no, no))
        for i, w in enumerate(reps[f]):
            row = np.einsum('a,b,c,d->abcd', Gs[w[0]], Gs[w[1]], Gs[w[2]], Ga[w[3]])
            M[i] = np.bincount(oid.ravel(), weights=row.ravel(), minlength=no)
        blocks.append(M)
    G = np.zeros((sum(b.shape[0] for b in blocks),) * 2)
    o = 0
    for b in blocks:
        G[o:o + b.shape[0], o:o + b.shape[0]] = b
        o += b.shape[0]
    return G


if __name__ == "__main__":
    t0 = time.time()
    ns = [int(a) for a in sys.argv[1:]]
    Kc = np.load('<ROOT>/dim/lk/Kcommon.npy')
    T = {}
    for n in ns:
        K = np.load('<ROOT>/dim/lk/K_n%d.npy' % n)
        G = Gorb(n)
        print('n=%d G built %.0fs; |G Kc| / |G| = %.2e' % (n, time.time() - t0, np.linalg.norm(G @ Kc) / np.linalg.norm(G)), flush=True)
        M = G @ K
        U, s, _ = np.linalg.svd(M, full_matrices=False)
        r = (s > 1e-9 * s[0]).sum()
        T[n] = U[:, :r]
        print('   rank of G K: %d (sv tail %s)' % (r, ' '.join('%.1e' % x for x in s[r - 3:r + 2])), flush=True)
    for i in range(len(ns)):
        for j in range(i + 1, len(ns)):
            sv = np.linalg.svd(T[ns[i]].T @ T[ns[j]], compute_uv=False)
            print('T%d vs T%d: dims %d %d, cosines min %.6f, #<1-1e-9: %d' % (ns[i], ns[j], T[ns[i]].shape[1], T[ns[j]].shape[1], sv.min(), (sv < 1 - 1e-9).sum()), flush=True)
