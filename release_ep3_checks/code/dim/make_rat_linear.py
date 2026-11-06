"""rat-like pickle with K = linear (structural) kernel of every exact block type (float rows), R empty.
Usage: make_rat_linear.py k,d types.pkl sdp.pkl out.pkl"""
import sys, pickle, time
sys.path.insert(0, '<ROOT>/dim')
import numpy as np
from relax import Relaxation
from typed_blocks import TypedEvaluator
k, d = map(int, sys.argv[1].split(','))
types = pickle.load(open(sys.argv[2], 'rb')); sdp = pickle.load(open(sys.argv[3], 'rb'))
t0 = time.time()
R = Relaxation(k, d, verbose=False)
TE = TypedEvaluator(R, types)
maps = TE.block_maps()
E = sdp['E']
U_, s_, Vt_ = np.linalg.svd(E, full_matrices=True)
Zn = Vt_[int((s_ > s_.max() * 1e-10).sum()):].T
out = []
tot = 0
for t, (idx, F) in zip(types, maps):
    Mz = np.tensordot(Zn[idx].T, F, axes=(1, 0))
    S = np.einsum('kij,kjl->il', Mz, Mz)
    w, V = np.linalg.eigh((S + S.T) / 2)
    K = V[:, w < 1e-9 * max(np.abs(w).max(), 1e-300)]
    out.append(dict(R=[], K=[list(map(float, K[:, j])) for j in range(K.shape[1])]))
    tot += K.shape[1]
print('types', len(types), 'total linear kernel dim', tot, '%.0fs' % (time.time() - t0), flush=True)
pickle.dump(out, open(sys.argv[4], 'wb'))
