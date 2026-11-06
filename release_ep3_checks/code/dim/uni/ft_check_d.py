"""ExactLocal(d) == FT_poly(d) for all cuts (so per-d certificates are certificates of the polynomial system at n=d)."""
import sys, pickle
sys.path.insert(0, '<ROOT>/dim')
sys.path.insert(0, '<ROOT>/dim/uni')
import numpy as np
from exact import ExactLocal
from polytables import PolyLocalExact
for d in [int(x) for x in sys.argv[1:]]:
    ok = True
    for cut in [(), (3,), (0,), (2,), (0, 1), (0, 2), (2, 3)]:
        A = np.array(ExactLocal(d, 4, cut).FT, dtype=object)
        B = PolyLocalExact(cut, d).FT
        if A.shape != B.shape or (A != B).any():
            ok = False
            print('  d=%d cut %s MISMATCH' % (d, cut), flush=True)
    print('d=%d: ExactLocal == FT_poly for all cuts: %s' % (d, ok), flush=True)
