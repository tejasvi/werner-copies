"""Fast all-word 4-replica moments t[w0,w1,w2,wa] = <Psi| P_w |Psi> for Psi = psi_0 x psi_1 x psi_2 x psi_3,
psi_r in (C^ds)^{x3} x C^2, via K_{w0,w1} = Psi^dag (P_{w0} x P_{w1}) Psi on the (site0,site1) | (site2,anc) split.
Also the directional derivative (multilinear, exact)."""
import numpy as np
from relax import P4

_perm_cache = {}


def _replica_perm_index(dim, p):
    """index map for P_p acting on (C^dim)^{x4} (4 replicas): (P_p v)[J] = v[idx[J]]."""
    key = (dim, p)
    if key not in _perm_cache:
        idx = np.arange(dim ** 4).reshape([dim] * 4)
        # target(s)[p[i]] = s[i]: output axis p[i] takes input axis i
        axes = [None] * 4
        for i in range(4):
            axes[p[i]] = i
        _perm_cache[key] = np.transpose(idx, axes).ravel()
    return _perm_cache[key]


def _dense(vs, dims):
    """Psi with axes grouped by factor: (site0 r0..r3, site1 r0..r3 | site2 r0..r3, anc r0..r3)."""
    T = np.einsum('abcd,efgh,ijkl,mnop->aeimbfjncgkodhlp', *[np.asarray(v).reshape(dims) for v in vs], optimize=True)
    ds, da = dims[0], dims[3]
    return T.reshape(ds ** 8, ds ** 4 * da ** 4)


def moments(vs, dims, dvs=None):
    """all-word moment tensor (24,24,24,24) complex; if dvs (4 direction vectors) given also the derivative."""
    ds, da = dims[0], dims[3]
    Psi = _dense(vs, dims)
    if dvs is not None:
        DPsi = sum(_dense([dvs[r] if s == r else vs[s] for s in range(4)], dims) for r in range(4))
    i01 = {}
    for a in range(24):
        ia = _replica_perm_index(ds, P4[a])
        for b in range(24):
            ib = _replica_perm_index(ds, P4[b])
            i01[a, b] = (ia[:, None] * ds ** 4 + ib[None, :]).ravel()
    i2a = np.array([[(_replica_perm_index(ds, P4[c])[:, None] * da ** 4 + _replica_perm_index(da, P4[e])[None, :]).ravel()
                     for e in range(24)] for c in range(24)])          # (24, 24, ncol)
    ncol = Psi.shape[1]
    J = np.arange(ncol)
    t = np.zeros((24,) * 4, dtype=complex)
    dt = np.zeros((24,) * 4, dtype=complex) if dvs is not None else None
    PsiH = Psi.conj().T
    if dvs is not None:
        DPsiH = DPsi.conj().T
    for (a, b), idx in i01.items():
        PP = Psi[idx]                          # (P01 Psi)[I, :] = Psi[idx[I], :]
        K = PsiH @ PP                          # K[J', J] = sum_I conj Psi[I,J'] Psi[idx I, J]
        # t = sum_J K[J, i2a[J]]  (column permutation by P_2a)
        t[a, b] = K[J[None, None, :], i2a].sum(-1)
        if dvs is not None:
            K2 = DPsiH @ PP + PsiH @ DPsi[idx]
            dt[a, b] = K2[J[None, None, :], i2a].sum(-1)
    return t, dt
