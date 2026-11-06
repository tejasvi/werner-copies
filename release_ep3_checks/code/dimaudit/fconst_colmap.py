"""Audit: F_const annihilation must hold for the aux factor AFTER the column maps used by gram/gram2 blocks."""
import sys
sys.path.insert(0, '<ROOT>/dim')
sys.path.insert(0, '<ROOT>/dim/uni')
import numpy as np, flint
from local import compose, inverse, ncycles
from relax import P4
from exact import ExactLocal
from polytables import PolyTables
Ga = np.array([[2 ** ncycles(compose(inverse(v), w)) for w in P4] for v in P4], dtype=np.int64)
kerGa = flint.fmpz_mat(24, 24, [int(x) for x in Ga.ravel()]).nullspace()[0]
K = np.array([[int(kerGa[i, j]) for j in range(24)] for i in range(24)], dtype=object)
T = PolyTables(3, 7)
ok = True
for cut in [(), (3,), (0,), (2,), (0, 1), (0, 2), (2, 3)]:
    FTa = np.array(ExactLocal(2, 4, cut).FT, dtype=object)
    for key, cm in T.colmap.items():
        if (FTa[:, cm].dot(K) != 0).any():
            ok = False
            print('  cut %s colmap %s: FT_a[:, colmap] does NOT annihilate ker(Ga)' % (cut, key))
print('FT_a[:, colmap] annihilates ker(Ga) for all cuts and colmaps %s: %s' % (sorted(map(str, T.colmap)), ok))
