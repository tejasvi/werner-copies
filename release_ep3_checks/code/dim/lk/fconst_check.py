"""Exact dimension of F_const = {orbit-constant x : (I^{x3} (x) Ga) x = 0} (ancilla kernel; Ga = Gram of S_4 words
on (C^2)^{x4}), and FT_a ker(Ga) = 0 for every cut (so all columns, equality rows and the objective annihilate it)."""
import sys
sys.path.insert(0, '<ROOT>/dim')
sys.path.insert(0, '<ROOT>/dim/lk')
import numpy as np
import flint
from local import compose, inverse, ncycles
from relax import P4, FAMILIES
from tcoords import reps, orb
from exact import ExactLocal
Ga = np.array([[2 ** ncycles(compose(inverse(v), w)) for w in P4] for v in P4], dtype=np.int64)
tot_rank, tot = 0, 0
for f in FAMILIES:
    oid, no = orb[f]
    M = np.zeros((no, no), dtype=np.int64)
    for i, w in enumerate(reps[f]):
        row = np.zeros((24, 24, 24, 24), dtype=np.int64)
        row[w[0], w[1], w[2], :] = Ga[w[3]]
        M[i] = np.bincount(oid.ravel(), weights=row.ravel(), minlength=no).astype(np.int64)
    p = 2 ** 61 - 1
    r = flint.nmod_mat(no, no, [int(x) % p for x in M.ravel()], p).rank()
    rq = flint.fmpz_mat(no, no, [int(x) for x in M.ravel()]).rank()
    print('family %s: orbits %d, rank mod p %d, rank over Q %d -> kernel %d' % (f, no, r, rq, no - rq), flush=True)
    tot_rank += rq; tot += no
print('F_const dimension = %d' % (tot - tot_rank))
kerGa = flint.fmpz_mat(24, 24, [int(x) for x in Ga.ravel()]).nullspace()[0]
K = np.array([[int(kerGa[i, j]) for j in range(24)] for i in range(24)], dtype=object)
ok = True
for cut in [(), (3,), (0,), (2,), (0, 1), (0, 2), (2, 3)]:
    FTa = np.array(ExactLocal(2, 4, cut).FT, dtype=object)
    if (FTa.dot(K) != 0).any():
        ok = False
print('ancilla Gram rank %d; FT_a annihilates ker(Ga) for all cuts: %s' % (24 - sum(1 for j in range(24) if any(K[:, j] != 0)), ok))
# equality rows: every part's ancilla factor A (rows x 24) must annihilate ker(Ga) too; objective za likewise
sys.path.insert(0, '<ROOT>/dim/uni')
from polytables import PolyEqualities

EQ = PolyEqualities(3, 7)
okE = True
for g in EQ.groups:
    for (f, S, A, sign) in g['parts']:
        if (np.array(A, dtype=object).dot(K) != 0).any():
            okE = False
print('equality ancilla factors annihilate ker(Ga): %s' % okE)
from exact import SWAP03
za = np.array([2 ** ncycles(compose(SWAP03, p)) for p in P4], dtype=object)
print('objective ancilla factor annihilates ker(Ga): %s' % (not (za.dot(K) != 0).any()))
