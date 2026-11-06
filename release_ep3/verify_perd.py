#!/usr/bin/env python3
"""verify_perd.py -- standalone verifier of the per-dimension EP_3 certificates (d = 3, ..., 8).

Each file ep3_perd_d<D>.pkl.xz holds a LOW-HEIGHT approximate certificate (dyadic Gram multipliers Z_t and equality
multipliers lambda, ~120 significant bits) for the relaxation at local dimension D, plus a square set S of raw
multiplier coordinates and a row set R.  The verifier COMPLETES it to an exact certificate and checks it:
  1. r = c - (verifier map)(Z, lambda) exactly (diagram compressions J(D) = D(D) C, exact at this D);
  2. the S columns at D exactly (residues modulo primes beyond an a-priori height bound, Chinese remaindering);
  3. u = A_RS^{-1} r_R exactly (rational), Z <- Z + u, lambda <- lambda + u;
  4. the identity c = (verifier map)(Z, lambda) holds EXACTLY on every word orbit (independent recomputation), and every
     Z_t is positive semidefinite (exact characteristic polynomial).
Step 4 alone is the proof (a valid exact certificate at D); steps 1-3 only construct it.
Usage: python3 verify_perd.py ep3_perd_d5.pkl.xz [more files] [--workers N]
"""
import argparse
import lzma
import math
import multiprocessing as mp
import os
import pickle
import sys
import time
from fractions import Fraction

import numpy as np
import flint

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import ep3core as E

sys.set_int_max_str_digits(0)


def crt_exact(res_list, primes):
    """Exact integers (balanced) from residues: list of int64 arrays -> numpy object array."""
    P = len(primes)
    t = []
    for i in range(P):
        x = res_list[i].astype(np.int64) % primes[i]
        for j in range(i):
            x = ((x - t[j]) % primes[i]) * pow(primes[j], -1, primes[i]) % primes[i]
        x = np.where(x > primes[i] // 2, x - primes[i], x)
        t.append(x)
    N = t[P - 1].astype(object)
    for i in range(P - 2, -1, -1):
        N = t[i].astype(object) + primes[i] * N
    return N


def verify_file(path, workers):
    t0 = time.time()
    log = lambda s: print('[d=%s %7.1fs] %s' % (D, time.time() - t0, s), flush=True)
    pkg = pickle.loads(lzma.decompress(open(path, 'rb').read()))
    assert pkg['format'] == 'ep3-perd-v1'
    k, D, nrow = pkg['k'], pkg['d'], pkg['nrow']
    orb = {f: E.word_orbits(k, f) for f in E.FAMILIES}
    assert sum(orb[f][1] for f in E.FAMILIES) == nrow
    blocks = [dict(kind=t['kind'], family=t['family'], rows=t['rows'], modules=t['modules'], W=t['W'])
              for t in pkg['types']]
    rx = E.Relaxation(k, blocks, pkg['diagrams'], pkg['aux'], pkg['eq_groups'], orb)
    E.check_definition(pkg)
    ce = E.ColumnEngine(rx)
    Zs = [[[Fraction(t['Znum'][i * t['r'] + j], 2 ** t['Zexp']) for j in range(t['r'])] for i in range(t['r'])]
          for t in pkg['types']]
    lam = {}
    for g, items in pkg['lam'].items():
        lam[g] = {tuple(o): Fraction(num, 2 ** ex) for o, num, ex in items}
    log('%d types, %d equality multipliers, |S| = |R| = %d' % (len(Zs), sum(len(v) for v in lam.values()), len(pkg['S'])))
    acc = rx.residual(D, Zs, lam)
    r = [x for f in E.FAMILIES for x in acc[f]]
    log('1. residual of the approximate certificate: max |r| = %.3e' % max(abs(float(x)) for x in r))
    # 2. exact raw S columns at D
    S, R = pkg['S'], pkg['R']
    maxorb = max(int(np.bincount(orb[f][0].ravel()).max()) for f in E.FAMILIES)
    H = 0
    bytype, eqs = {}, []
    for c, key in enumerate(S):
        if key[0] == 'blk':
            bytype.setdefault(key[1], []).append((c, key[2], key[3]))
        else:
            eqs.append((c, key[1], tuple(key[2])))
    for ti, lst in bytype.items():
        t = pkg['types'][ti]
        Wm = np.array(t['W'], dtype=object)
        dims = [rx.dims(m, 'a' if l == k else 's') for l, m in enumerate(t['modules'])]
        nn = int(np.prod(dims))
        for (g, rr, ss) in ce.block_pairs[ti]:
            f, kpos, lpos, cut = g
            amax = 1
            for l, m in enumerate(t['modules']):
                A = rx.local_rows(m, 'a' if l == k else 's', D, kpos, lpos, False)
                amax *= max(abs(int(v)) for v in A.ravel())
            ur = [sum(abs(int(x)) for x in Wm[rr * nn:(rr + 1) * nn, a]) for a in range(Wm.shape[1])]
            us = [sum(abs(int(x)) for x in Wm[ss * nn:(ss + 1) * nn, a]) for a in range(Wm.shape[1])]
            for (c, a, b) in lst:
                l1 = ur[a] * us[b] + (ur[b] * us[a] if a != b else 0)
                H = max(H, maxorb * l1 * amax * len(ce.block_pairs[ti]))
    for (c, g, o) in eqs:
        tot = 0
        for part in pkg['eq_groups'][g]['parts']:
            pr = maxorb
            for l in range(k + 1):
                Es = rx.eq_local(D, part['local'][l], False)
                pr *= max(abs(int(v)) for v in Es[o[l]])
            tot += pr
        H = max(H, tot)
    primes, pp, prod = [], 2 ** 26, 1
    while prod <= 2 * H + 1:
        pp -= 1
        if flint.fmpz(pp).is_prime():
            primes.append(pp)
            prod *= pp
    res = []
    for p in primes:
        out = np.zeros((len(R), len(S)), dtype=np.int64)
        for ti, lst in bytype.items():
            rt = pkg['types'][ti]['r']
            Zl = []
            for (c, a, b) in lst:
                Z = [[0] * rt for _ in range(rt)]
                Z[a][b] += 1
                if a != b:
                    Z[b][a] += 1
                Zl.append(Z)
            cols = ce.type_columns(D, False, ti, Zl, p)
            full = np.concatenate([cols[f] if f in cols else np.zeros((len(next(iter(cols.values()))), orb[f][1]), dtype=np.int64) for f in E.FAMILIES], axis=1)       # len(lst) x nrow
            for jj, (c, a, b) in enumerate(lst):
                out[:, c] = full[jj, R]
        if eqs:
            cols = ce.eq_columns(D, False, [(g, o) for _, g, o in eqs], p)
            full = np.concatenate([cols[f] if f in cols else np.zeros((len(next(iter(cols.values()))), orb[f][1]), dtype=np.int64) for f in E.FAMILIES], axis=1)
            for jj, (c, g, o) in enumerate(eqs):
                out[:, c] = full[jj, R]
        res.append(out)
    A_RS = crt_exact(res, primes)
    log('2. exact S columns at d = %d (%d primes, height bound 2^%d)' % (D, len(primes), H.bit_length()))
    # 3. exact correction
    Dr = 1
    for i in R:
        Dr = Dr * r[i].denominator // math.gcd(Dr, r[i].denominator)
    Am = flint.fmpz_mat(len(R), len(S), [int(x) for x in A_RS.ravel()])
    bv = flint.fmpz_mat(len(R), 1, [int(r[i] * Dr) for i in R])
    u = flint.fmpq_mat(Am).solve(flint.fmpq_mat(bv))
    uu = [Fraction(int(u[j, 0].p), int(u[j, 0].q)) / Dr for j in range(len(S))]
    log('3. exact correction: max |u| = %.3e, max denominator %d bits' % (
        max(abs(float(x)) for x in uu), max(x.denominator.bit_length() for x in uu)))
    for ti, lst in bytype.items():
        for (c, a, b) in lst:
            Zs[ti][a][b] += uu[c]
            if a != b:
                Zs[ti][b][a] += uu[c]
    for (c, g, o) in eqs:
        d_ = lam.setdefault(g, {})
        d_[o] = d_.get(o, Fraction(0)) + uu[c]
    # 4. the proof: exact identity on every orbit and exact PSD
    acc = rx.residual(D, Zs, lam)
    nz = sum(1 for f in E.FAMILIES for x in acc[f] if x != 0)
    log('4. identity c = (verifier map)(Z, lambda): nonzero orbit sums %d of %d' % (nz, nrow))
    with mp.get_context('fork').Pool(workers) as pool:
        psd = pool.map(E.psd_charpoly, Zs, chunksize=8)
    nbad = sum(1 for x in psd if not x)
    log('4. PSD (exact characteristic polynomial): %d of %d multipliers fail' % (nbad, len(Zs)))
    ok = nz == 0 and nbad == 0
    log('EXACT CERTIFICATE AT d = %d: %s' % (D, 'PASS' if ok else 'FAIL'))
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('files', nargs='+')
    ap.add_argument('--workers', type=int, default=os.cpu_count())
    args = ap.parse_args()
    ok = all([verify_file(f, args.workers) for f in args.files])
    print('ALL PER-d CERTIFICATES: %s' % ('PASS' if ok else 'FAIL'), flush=True)
    return ok


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
