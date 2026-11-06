"""Audit (iii)(c): the zero modes behind the tau generators must be EXACT zeros of q_3(1/2, .) (complementary slackness).
Dense specs: C = A B^dagger with A = a.reshape(-1,2), B = b.reshape(-1,2) (Gaussian integers; float64 exact here)."""
import pickle, itertools, numpy as np
d = pickle.load(open('<ROOT>/dim/lk/tau_exact2.pkl', 'rb'))
def q3(C, ds):
    T = C.reshape([ds] * 6)            # rows (i1,i2,i3), cols (j1,j2,j3)
    tot = 0.0
    for J in itertools.product([0, 1], repeat=3):
        X = T
        # trace copies m with J[m]=1 (row axis m, col axis 3+m); do from last to first to keep axis indices valid
        for m in reversed(range(3)):
            if J[m]:
                X = np.trace(X, axis1=m, axis2=X.ndim // 2 + m)
        tot += (-0.5) ** sum(J) * float(np.sum(X.real ** 2 + X.imag ** 2))
    return tot
seen, worst = set(), 0.0
for s in d['specs']:
    if s['kind'] != 'dense':
        continue
    key = (str(s['a'])[:200], str(s['b'])[:200])
    if key in seen:
        continue
    seen.add(key)
    a = np.array(s['a']); b = np.array(s['b'])
    A = a.reshape(-1, 2); B = b.reshape(-1, 2)
    C = A @ B.conj().T
    ds = round(C.shape[0] ** (1 / 3))
    assert ds ** 3 == C.shape[0]
    assert np.abs(A.real - np.round(A.real)).max() == 0 and np.abs(B.imag - np.round(B.imag)).max() == 0
    qv = q3(C, ds)
    worst = max(worst, abs(qv) / max(float(np.sum(C.real ** 2 + C.imag ** 2)), 1))
    print('J=%s ds=%d  q3/||C||^2 = %.3e  (||C||^2 = %.0f)' % (s['J'], ds, qv / float(np.sum(C.real ** 2 + C.imag ** 2)), float(np.sum(C.real ** 2 + C.imag ** 2))))
print('distinct dense zero modes: %d, max |q3|/||C||^2 = %.3e (exact zero expected; float64 exact for these integers)' % (len(seen), worst))
