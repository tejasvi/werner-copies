"""Endpoint partial-trace form for k copies of the d x d Werner state.

q_k(t, C) = sum_{J subset [k]} (-t)^{|J|} ||Tr_J C||_F^2,  C in L((C^d)^{(x)k}).
rho(d, alpha) is k-copy distillable iff q_k(-alpha, C) < 0 for some rank<=2 C (Costa Rico).
G = (id - t T)^{(x)k}, T(X) = Tr(X) I, so q(C) = <C, G(C)>_HS.
"""
import numpy as np


def apply_G(C, d, k, t):
    """Return (id - t T)^{(x)k} (C) for C given as (d^k, d^k) array."""
    N = d ** k
    X = C.reshape((d,) * (2 * k)).copy()
    for m in range(k):
        # trace over row index m and column index k+m
        tr = np.trace(X, axis1=m, axis2=k + m)  # removes both axes
        # broadcast back: tr has axes (rows without m, cols without m)
        tr = np.expand_dims(tr, axis=m)          # restore row axis m (size 1)
        tr = np.expand_dims(tr, axis=k + m)      # restore col axis k+m (size 1)
        eye_shape = [1] * (2 * k)
        eye_shape[m] = d
        eye_shape[k + m] = d
        X = X - t * tr * np.eye(d).reshape(eye_shape)
    return X.reshape(N, N)


def qval(C, d, k, t):
    return np.vdot(C, apply_G(C, d, k, t)).real


def q_bruteforce(C, d, k, t):
    """Direct sum over subsets (for testing)."""
    from itertools import combinations
    X = C.reshape((d,) * (2 * k))
    total = 0.0
    for r in range(k + 1):
        for J in combinations(range(k), r):
            Y = X
            # trace out J (largest first to keep axis numbering valid)
            rem = k
            Jl = sorted(J, reverse=True)
            for m in Jl:
                Y = np.trace(Y, axis1=m, axis2=rem + m)
                rem -= 1
            total += (-t) ** r * np.sum(np.abs(Y) ** 2)
    return total
