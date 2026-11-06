"""Assemble the relaxation SDP data and save to npz (sparse-friendly)."""
import sys
import time
import pickle

import numpy as np

sys.path.insert(0, '<ROOT>/dim')
from relax import Relaxation, FAMILIES, FAMILY_CUTS


def build(k, d, gram=True, out=None, verbose=True):
    t0 = time.time()
    R = Relaxation(k, d, verbose=verbose)
    data = dict(k=k, d=d, N=R.N, nvar=R.nvar, foff=R.foff)
    data['c'] = R.objective()
    data['tr'] = {f: R.trace_row(f) for f in FAMILIES}
    E = R.equality_rows()
    data['E_raw_shape'] = E.shape
    # orthonormal basis of the row space
    U, s, Vt = np.linalg.svd(E, full_matrices=False)
    tol = s.max() * 1e-10
    r = int((s > tol).sum())
    data['E'] = Vt[:r]
    data['E_sv'] = s
    if verbose:
        print('equalities raw', E.shape, 'rank', r, 'smallest kept sv %.3e next %.3e' % (s[r - 1], s[r] if r < len(s) else 0), '%.1fs' % (time.time() - t0), flush=True)
    blocks = []
    for f in FAMILIES:
        for cut in FAMILY_CUTS[f]:
            obs, Fs = R.family_blocks(f, cut)
            for ob, Fm in zip(obs, Fs):
                for qi, Q in enumerate(ob['Qs']):
                    Fq = np.einsum('ia,kij,jb->kab', Q, Fm, Q, optimize=True)
                    if np.abs(Fq).max() < 1e-12:
                        continue
                    blocks.append(dict(kind='src', f=f, cut=cut, st=ob['st'], ai=ob['ai'], q=qi,
                                       m=Q.shape[1], F={f: Fq}))
            if verbose:
                print('family', f, 'cut', cut, 'blocks', len(obs), 'max m', max(Q.shape[1] for ob in obs for Q in ob['Qs']),
                      '%.1fs' % (time.time() - t0), flush=True)
    if gram:
        obs, res = R.gram_blocks()
        for j, ob in enumerate(obs):
            for qi, Q in enumerate(ob['Qs']):
                m = Q.shape[1]
                Fq = {f: np.einsum('ia,kij,jb->kab', Q, res[f][j], Q, optimize=True) for f in res}
                blocks.append(dict(kind='gram', st=ob['st'], ai=ob['ai'], q=qi, m=2 * m, F=Fq))
        if verbose:
            print('gram blocks', len(obs), 'max 2m', max(2 * Q.shape[1] for ob in obs for Q in ob['Qs']), '%.1fs' % (time.time() - t0), flush=True)
    data['blocks'] = blocks
    if out:
        with open(out, 'wb') as fh:
            pickle.dump(data, fh, protocol=4)
    return data


def gram_full(blk, N, foff, nvar):
    """Return F (N, 2m, 2m) for a gram block."""
    m = blk['m'] // 2
    F = np.zeros((N, 2 * m, 2 * m))
    a = foff['31']
    F[a:a + nvar['31'], :m, :m] = blk['F']['31']
    a = foff['22']
    F[a:a + nvar['22'], :m, m:] = blk['F']['22']
    F[a:a + nvar['22'], m:, :m] = np.transpose(blk['F']['22'], (0, 2, 1))
    a = foff['13']
    F[a:a + nvar['13'], m:, m:] = blk['F']['13']
    return F


if __name__ == '__main__':
    k, d = int(sys.argv[1]), int(sys.argv[2])
    out = sys.argv[3]
    data = build(k, d, out=out)
    tot = sum(b['m'] * (b['m'] + 1) // 2 for b in data['blocks'])
    print('N', data['N'], 'blocks', len(data['blocks']), 'svec total', tot)
