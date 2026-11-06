"""Audit (iii)(c): every certificate used in the consistency argument must use the SAME face N (red2_k3_d6) and the same kept types."""
import sys, pickle
D0 = '<ROOT>/dim'
ref = pickle.load(open(D0 + '/runs/red2_k3_d6.pkl', 'rb'))
Nref, kref = ref['N'], list(ref['type_index'])
def same(A, B):
    import numpy as np
    if A is None or B is None:
        return A is None and B is None
    A = np.array(A, dtype=object); B = np.array(B, dtype=object)
    return A.shape == B.shape and not (A != B).any()
for p in sys.argv[1:]:
    c = pickle.load(open(p, 'rb'))
    keys = sorted(c.keys())
    N = c.get('N'); types = c.get('types'); ti = c.get('type_index')
    msg = []
    if N is not None:
        if len(N) == len(Nref):
            okN = all(same(a, b) for a, b in zip(N, Nref))
        else:   # N stored only for kept types
            okN = all(same(a, Nref[t]) for a, t in zip(N, kref)) if len(N) == len(kref) else False
        msg.append('N==Nref: %s (len %d vs %d/%d)' % (okN, len(N), len(Nref), len(kref)))
    if ti is not None:
        msg.append('type_index==kept: %s' % (list(ti) == kref))
    print(p.split('/')[-1], 'd=%s' % c.get('d'), '; '.join(msg) if msg else 'keys=%s' % keys[:12], flush=True)
