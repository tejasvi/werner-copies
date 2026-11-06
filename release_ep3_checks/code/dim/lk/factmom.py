"""Moments of 4-replica product vectors psi_r = phiA_r (x) phiB_r with factor A = (site0, anc) and factor B =
(site1, site2) (the |J|=1 zero-mode structure), with separate bra and ket vectors:
    t[w0,w1,w2,wa] = tA[w0,wa] * tB[w1,w2],  tX[w,v] = <(x)_r braX_r| P_w (x) P_v |(x)_r ketX_r>.
Index conventions as fastmom.moments (validated there against physical.moment_tensor_par)."""
import numpy as np
from relax import P4
from fastmom import _replica_perm_index


def two_factor(bras, kets):
    """bras/kets: lists of 4 matrices (n0, n1).  Returns tX (24, 24)."""
    n0, n1 = kets[0].shape
    def dense(ms):
        T = np.einsum('ae,bf,cg,dh->abcdefgh', *ms, optimize=True)
        return T.reshape(n0 ** 4, n1 ** 4)
    Pb, Pk = dense(bras), dense(kets)
    PbH = Pb.conj().T
    i1 = np.array([_replica_perm_index(n1, P4[v]) for v in range(24)])      # (24, n1^4)
    J = np.arange(n1 ** 4)
    t = np.zeros((24, 24), dtype=complex)
    for w in range(24):
        idx = _replica_perm_index(n0, P4[w])
        K = PbH @ Pk[idx]
        t[w] = K[J[None, :], i1].sum(-1)
    return t


def prod_moments(braA, braB, ketA, ketB):
    tA = two_factor(braA, ketA)          # (w0, wa)
    tB = two_factor(braB, ketB)          # (w1, w2)
    return np.einsum('ad,bc->abcd', tA, tB)


def prod_moments_with_derivative(A, B, dA, dB):
    """A, B: lists of 4 replica factor matrices; direction for replica r: dA[r] (x) B[r] + A[r] (x) dB[r]
    (dA[r] or dB[r] may be None).  Returns (t, dt) with dt the exact first derivative."""
    t = prod_moments(A, B, A, B)
    dt = np.zeros_like(t)
    for r in range(4):
        for which in ('A', 'B'):
            d = dA[r] if which == 'A' else dB[r]
            if d is None:
                continue
            kA = [d if (s == r and which == 'A') else A[s] for s in range(4)]
            kB = [d if (s == r and which == 'B') else B[s] for s in range(4)]
            dt += prod_moments(A, B, kA, kB) + prod_moments(kA, kB, A, B)
    return t, dt


def prod_moments_dirs(A, B, terms):
    """t and exact derivative along a direction given per replica r as a list of product terms (fa, fb):
    d psi_r = sum (fa (x) fb).  terms: list of 4 lists."""
    t = prod_moments(A, B, A, B)
    dt = np.zeros_like(t)
    for r in range(4):
        for fa, fb in terms[r]:
            kA = [fa if s == r else A[s] for s in range(4)]
            kB = [fb if s == r else B[s] for s in range(4)]
            dt += prod_moments(A, B, kA, kB) + prod_moments(kA, kB, A, B)
    return t, dt
