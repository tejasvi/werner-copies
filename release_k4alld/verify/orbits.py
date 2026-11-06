"""Orbit labels of the word space S4^5 under H_f = (site permutations) x (left/right G_f, all 5 factors) x (inversion).

Independent implementation: builds the generator index maps and takes connected components (scipy), instead of the
min-label propagation used by the verifier.  Saves orbits.npz with one int32 label array per family.
"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))   # python -I does not add the script dir
import common
import os, sys, time
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
from relax import P4, I4, FAMILY_GROUP, FAMILIES
from local import compose, inverse

t0 = time.time()
NW = 24
N = NW ** 5
Wd = np.indices((NW,) * 5).reshape(5, -1)
enc = lambda ws: (((ws[0] * NW + ws[1]) * NW + ws[2]) * NW + ws[3]) * NW + ws[4]
lmul = lambda g: np.array([I4[compose(g, p)] for p in P4])
rmul = lambda g: np.array([I4[compose(p, g)] for p in P4])
invp = np.array([I4[inverse(p)] for p in P4])
out = {}
for f in FAMILIES:
    gens = []
    for i, j in ((0, 1), (1, 2), (2, 3)):            # site transpositions (sites 0..3; the ancilla is factor 4)
        ws = list(Wd); ws[i], ws[j] = Wd[j], Wd[i]
        gens.append(enc(ws))
    trans = [g for g in FAMILY_GROUP[f] if sum(g[i] != i for i in range(4)) == 2]
    for g in trans:                                    # simultaneous left and right multiplication on all 5 factors
        for m in (lmul(g), rmul(g)):
            gens.append(enc([m[Wd[i]] for i in range(5)]))
    gens.append(enc([invp[Wd[i]] for i in range(5)]))  # inversion on all 5 factors
    rows = np.concatenate([np.arange(N)] * len(gens)); cols = np.concatenate(gens)
    A = coo_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)), shape=(N, N)).tocsr()
    nc, lab = connected_components(A, directed=True, connection='weak')
    out[f] = lab.astype(np.int32)
    # check: every generator maps each orbit into itself
    for g in gens:
        assert np.array_equal(lab, lab[g]), 'generator not orbit-preserving'
    print('[%.0fs] family %s: %d transpositions in G_f, %d orbits, max orbit size %d' % (time.time() - t0, f, len(trans), nc,
          np.bincount(lab).max()), flush=True)
np.savez_compressed(common.W('orbits.npz'), **out)
