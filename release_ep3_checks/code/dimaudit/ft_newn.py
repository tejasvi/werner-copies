"""Audit (iii)(a): compare the verifier's literal local data ExactLocal(n) (modules built at dimension n)
with the polynomial data FT_poly(n) at n values not used by the construction (17, 19, 20, 23)."""
import sys, time
sys.path.insert(0, '<ROOT>/dim')
sys.path.insert(0, '<ROOT>/dim/uni')
import numpy as np
from exact import ExactLocal
from polytables import PolyLocalExact
CUTS = [(), (3,), (0,), (2,), (0, 1), (0, 2), (2, 3)]
for n in [int(x) for x in sys.argv[1:]]:
    t0 = time.time(); ok = True
    for cut in CUTS:
        A = np.array(ExactLocal(n, 4, cut).FT, dtype=object)
        B = PolyLocalExact(cut, n).FT
        same = (A.shape == B.shape) and not (A != B).any()
        ok &= same
        if not same:
            print('  n=%d cut %s MISMATCH shapes %s %s' % (n, cut, A.shape, B.shape), flush=True)
    # three-replica (cut ()) data used by PolyEqualities at n=6
    s3n = np.array(ExactLocal(n, 3, ()).FT, dtype=object); s36 = np.array(ExactLocal(6, 3, ()).FT, dtype=object)
    same3 = s3n.shape == s36.shape and not (s3n != s36).any()
    print('n=%d: ExactLocal(n,4,cut) == FT_poly(n) all cuts: %s; ExactLocal(n,3,()) == ExactLocal(6,3,()): %s (%.0fs)'
          % (n, ok, same3, time.time() - t0), flush=True)
