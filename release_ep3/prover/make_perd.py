"""Prover side: compact per-d certificate (ep3-perd-v1) from an exact v4 certificate.
The exact multipliers are rounded to ~BITS significant bits (dyadic), and a square set S of raw coordinates
(equality items first, then raw Gram entries, pivoted QR on normalised float columns at d) with rows R is chosen;
the verifier re-solves the exact correction on S and checks the completed certificate.
Usage: make_perd.py cert_v4.pkl diagram_C.pkl bits out.pkl.xz [nprimes]"""
import itertools
import lzma
import math
import os
import pickle
import sys
import time
from fractions import Fraction

import numpy as np
import scipy.linalg as sla
import flint

sys.set_int_max_str_digits(0)
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # package root
import ep3core as E
from verify_alld import crt_float

src, diagp, bits, outp = sys.argv[1:5]
bits = int(bits)
nprimes = int(sys.argv[5]) if len(sys.argv) > 5 else 6
t0 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
c = pickle.load(open(src, 'rb'))
k, D = c['k'], c['d']
Dg = pickle.load(open(diagp, 'rb'))


def rename(key):
    n, cut, lab = key.split('|')
    return ('A' if n == '2' else 'S') + '|' + cut + '|' + lab


diagrams = {(int(m), tuple(cut)): {tuple(lab): (keys, [[int(x) for x in row] for row in C]) for lab, (keys, C) in labs.items()}
            for (m, cut), labs in Dg.items()}
aux = {rename(kk): [[int(x) for x in row] for row in v] for kk, v in c['modules'].items() if kk.startswith('2|')}
aux.update({kk.replace('|2|', '|A|'): [[int(x) for x in row] for row in v] for kk, v in c['eq_modules'].items() if '|2|' in kk})
eqg = {}
for g, v in c['eq_groups'].items():
    parts = []
    for part in v['parts']:
        loc = []
        for (n0, slot, order, kind, mkeys) in part['local']:
            site = n0 != 2
            loc.append(('S' if site else 'A', int(slot), tuple(int(x) for x in order), kind,
                        [mk.replace('|%d|' % n0, '|S|' if site else '|A|') for mk in mkeys]))
        parts.append(dict(family=part['family'], sign=int(part['sign']), local=loc))
    eqg[g] = dict(parts=parts)
types = []
for b in c['blocks']:
    Z = [[Fraction(x) for x in row] for row in b['Z']]
    r = len(Z)
    mx = max(abs(x) for row in Z for x in row)
    e = bits - int(math.floor(math.log2(mx))) if mx else 0
    num = [int(round(Z[i][j] * 2 ** e)) for i in range(r) for j in range(r)]
    types.append(dict(kind=b['kind'], family=b['family'], rows=list(b['rows']), modules=[rename(m) for m in b['modules']],
                      W=[[int(x) for x in row] for row in b['W']], r=r, Znum=num, Zexp=e))
lam = {}
for g, v in c['eq_groups'].items():
    items = []
    for o, val in v['lambda']:
        x = Fraction(val)
        if x:
            e = bits - int(math.floor(math.log2(abs(x))))
            items.append((tuple(int(y) for y in o), int(round(x * 2 ** e)), e))
    lam[g] = items
log('d = %d: %d types, %d equality multipliers rounded to %d bits' % (D, len(types), sum(len(v) for v in lam.values()), bits))
orb = {f: E.word_orbits(k, f) for f in E.FAMILIES}
nrow = sum(orb[f][1] for f in E.FAMILIES)
blocks = [dict(kind=t['kind'], family=t['family'], rows=t['rows'], modules=t['modules'], W=t['W']) for t in types]
rx = E.Relaxation(k, blocks, diagrams, aux, eqg, orb)
ce = E.ColumnEngine(rx)
# candidate columns: all raw Gram entries and all equality items
cand = []
for ti, t in enumerate(types):
    for a in range(t['r']):
        for b_ in range(a, t['r']):
            cand.append(('blk', ti, a, b_))
eqitems = []
for g, ginfo in eqg.items():
    shp = [rx.eq_local(D, ginfo['parts'][0]['local'][l], False).shape[0] for l in range(k + 1)]
    for o in itertools.product(*[range(x) for x in shp]):
        eqitems.append((g, tuple(o)))
cand += [('eq', g, o) for g, o in eqitems]
primes, pp = [], 2 ** 26
while len(primes) < nprimes:
    pp -= 1
    if flint.fmpz(pp).is_prime():
        primes.append(pp)
G = {}


def prime_task(p):
    out = np.zeros((nrow, len(cand)), dtype=np.int64)
    pos = 0
    for ti, t in enumerate(types):
        Zl = []
        for a in range(t['r']):
            for b_ in range(a, t['r']):
                Z = [[0] * t['r'] for _ in range(t['r'])]
                Z[a][b_] += 1
                if a != b_:
                    Z[b_][a] += 1
                Zl.append(Z)
        cols = ce.type_columns(D, False, ti, Zl, p)
        full = np.concatenate([cols[f] if f in cols else np.zeros((len(Zl), orb[f][1]), dtype=np.int64) for f in E.FAMILIES], axis=1)
        out[:, pos:pos + len(Zl)] = full.T
        pos += len(Zl)
    cols = ce.eq_columns(D, False, eqitems, p)
    out[:, pos:] = np.concatenate([cols[f] for f in E.FAMILIES], axis=1).T
    fn = outp + '.res_%d.npy' % p
    np.save(fn, out)
    return fn


import multiprocessing as mp
with mp.get_context('fork').Pool(len(primes)) as pool:
    fns = pool.map(prime_task, primes)
res = [np.load(fn) for fn in fns]
for fn in fns:
    os.remove(fn)
log('  columns modulo %d primes done (%d candidates)' % (len(primes), len(cand)))
Af = crt_float(res, primes)[0]
cn = np.linalg.norm(Af, axis=0)
cn[cn == 0] = 1
An = Af / cn
eqc = [i for i, x in enumerate(cand) if x[0] == 'eq']
bc = [i for i, x in enumerate(cand) if x[0] == 'blk']
QE, RE, pE = sla.qr(An[:, eqc], mode='economic', pivoting=True)
dE = np.abs(np.diag(RE))
rE = int((dE > 1e-10 * dE[0]).sum())
QEb = QE[:, :rE]
Bp = An[:, bc] - QEb @ (QEb.T @ An[:, bc])
QB, RB, pB = sla.qr(Bp, mode='economic', pivoting=True)
dB = np.abs(np.diag(RB))
cut = [i for i in range(len(dB) - 1) if dB[i + 1] < 1e-9 * dB[0] and dB[i] > 1e-13 * dB[0]]
rB = (max(cut, key=lambda i: dB[i] / max(dB[i + 1], 1e-300)) + 1) if cut else int((dB > 1e-10 * dB[0]).sum())
Ssel = [eqc[i] for i in pE[:rE]] + [bc[i] for i in pB[:rB]]
_, _, pR = sla.qr(An[:, Ssel].T, mode='economic', pivoting=True)
R = sorted(int(x) for x in pR[:len(Ssel)])
log('selection: %d equality + %d raw Gram columns (block R-diag ratios at the cut %s)' % (
    rE, rB, ['%.1e' % (x / dB[0]) for x in dB[max(0, rB - 2):rB + 2]]))
pkg = dict(format='ep3-perd-v1', k=k, d=D, nrow=nrow, diagrams=diagrams, aux=aux, eq_groups=eqg, types=types,
           lam=lam, S=[cand[i] for i in Ssel], R=R)
raw = pickle.dumps(pkg, protocol=4)
open(outp, 'wb').write(lzma.compress(raw, preset=9 | lzma.PRESET_EXTREME))
log('written %s (%.2f MB pickled, %.2f MB xz)' % (outp, len(raw) / 1e6, os.path.getsize(outp) / 1e6))
