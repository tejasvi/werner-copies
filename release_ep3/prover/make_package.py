"""Prover side: build the COMPACT all-d certificate (d >= 9) for release_ep3 from the route-A data.

Contents (pure Python objects: ints, strings, lists, tuples, dicts; pickled and xz-compressed):
  k, d0; diagrams {(m, cut): {label: (keys, C)}}; aux modules (local dimension 2); equality groups (structure);
  types: kind, family, rows, modules (site keys 'S|cut|label', aux keys 'A|cut|label'), W (integers),
         T (integers, T_r = T / 2^40), delta (s-exponent), Bernstein coefficients of Z_t / s^delta (raw coordinates,
         numerators with one power-of-two denominator 2^cexp per type);
  equality items with Bernstein coefficients mu (degree 9, lambda_e = s^k sum_m mu_m B_m(9s));
  stage1: degree-20 Bernstein coefficients of the polynomial correction (conditioned coordinates D_t with
          Z_t = s^delta T_r D_t T_r^T; equality items lambda = s^k mu), integer mantissas with one exponent per column;
  stage2: square column subset S (block entries / equality items) and row set R;
  W: constant sparse left-kernel vectors (V^perp) and moving polynomial left-kernel vectors (degree <= 5),
     restricted to a subset that is independent at s = 1/9;
  margin m.
Usage: make_package.py <routeA dir> <stage1.npz> <S.npy> <diagram_C.pkl> <bits> <out.pkl.xz>"""
import lzma
import math
import os
import pickle
import sys
import time
from fractions import Fraction

import numpy as np
import flint

sys.set_int_max_str_digits(0)
RA, s1p, Sp, diagp, bits, outp = sys.argv[1:7]
bits = int(bits)
t0 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
cert = pickle.load(open(os.path.join(RA, 'perdL', 'certfile4_k3_d9.pkl'), 'rb'))
RS = pickle.load(open(os.path.join(RA, 'res_k3b.pkl'), 'rb'))
meta = pickle.load(open(os.path.join(RA, 'k3', 'meta.pkl'), 'rb'))
NM = pickle.load(open(os.path.join(RA, 'neumannR_k3.pkl'), 'rb'))
MG = pickle.load(open(os.path.join(RA, 'margins_k3.pkl'), 'rb'))
NB = pickle.load(open(os.path.join(RA, 'null_k3.pkl'), 'rb'))
S1 = np.load(s1p)
S = np.load(Sp)
D = pickle.load(open(diagp, 'rb'))
k = 3
gnames = list(cert['eq_groups'].keys())


def rename(key):
    n, cut, lab = key.split('|')
    return ('A' if n == '2' else 'S') + '|' + cut + '|' + lab


def dyadic(fr_list):
    """list of Fractions with power-of-two denominators -> (integer numerators, exponent e) with x = num / 2^e."""
    e = 0
    for x in fr_list:
        dd = x.denominator
        assert dd & (dd - 1) == 0, 'non-dyadic coefficient'
        e = max(e, dd.bit_length() - 1)
    return [int(x * 2 ** e) for x in fr_list], e


types = []
for ti, b in enumerate(cert['blocks']):
    r = len(RS['C'][ti][0])
    Cs = [[Fraction(x) for row in Cj for x in row] for Cj in RS['C'][ti]]
    flat = [x for Cj in Cs for x in Cj]
    num, e = dyadic(flat)
    Cnum = [num[j * r * r:(j + 1) * r * r] for j in range(len(Cs))]
    Tint = [[int(round(x * 2 ** 40)) for x in row] for row in RS['T'][ti]]
    types.append(dict(kind=b['kind'], family=b['family'], rows=list(b['rows']), modules=[rename(m) for m in b['modules']],
                      W=[[int(x) for x in row] for row in b['W']], T=Tint, delta=int(RS['deltas'][ti]),
                      p=len(Cs) - 1, Cnum=Cnum, Cexp=e, r=r))
log('types: %d' % len(types))
# equality items and base multipliers (Bernstein degree nm-1 = 9 on 9s in [0,1], times s^k)
nm = RS['nm']
mu = [Fraction(x) for x in RS['mu']]
eq_items = []
for e_, item in enumerate(RS['esel']):
    g, o = item if isinstance(item, tuple) else tuple(item)
    num, ex = dyadic(mu[e_ * nm:(e_ + 1) * nm])
    eq_items.append(dict(group=gnames[g], o=tuple(int(x) for x in o), mu=num, muexp=ex))
log('base equality items: %d (Bernstein degree %d)' % (len(eq_items), nm - 1))
# stage 1: rounded Bernstein coefficients of the correction, one exponent per column
beta = S1['beta']
q = int(S1['q'])
colkey = []
for c, x in enumerate(meta['cmeta']):
    colkey.append(('blk', int(x[1]), int(x[2]), int(x[3])) if x[0] == 'blk' else ('eq', gnames[x[1][0]], tuple(int(y) for y in x[1][1])))
s1 = []
maxrel = 0.0
for c in range(len(colkey)):
    v = beta[:, c]
    mx = np.abs(v).max()
    if mx == 0:
        continue
    e = int(math.floor(math.log2(mx))) - bits
    mant = [int(round(x / 2.0 ** e)) for x in v]
    maxrel = max(maxrel, np.abs(np.array(mant) * 2.0 ** e - v).max() / mx)
    s1.append(dict(col=colkey[c], mant=mant, exp=-e))          # value = mant / 2^exp
log('stage 1: %d nonzero columns, degree %d, %d-bit mantissas (max relative rounding %.2e)' % (len(s1), q, bits + 1, maxrel))
stage2 = dict(S=[colkey[c] for c in S], R=[int(x) for x in NM['rows']])
# left kernel: constant sparse part and an independent subset of the moving vectors
vperp = []
for v in NB['vperp']:
    fr = [Fraction(x) for x in v]
    den = 1
    for x in fr:
        den = den * x.denominator // math.gcd(den, x.denominator)
    vperp.append(dict(den=den, ent={i: int(x * den) for i, x in enumerate(fr) if x}))
P = 1000003
s19 = pow(9, -1, P)                                             # s = 1/9 mod P
rows = []
for v in vperp:
    row = [0] * meta['nrow']
    for i, x in v['ent'].items():
        row[i] = x % P
    rows.append(row)
base = flint.nmod_mat(rows, P)
rk = base.rank()
log('V^perp: %d vectors, rank %d mod %d' % (len(vperp), rk, P))
moving_sel = []
cur = [list(r) for r in rows]
for j, m in enumerate(NB['moving']):
    vals = [0] * meta['nrow']
    for d_, coef in enumerate(m):
        for i, x in enumerate(coef):
            fx = Fraction(x)
            if fx:
                vals[i] = (vals[i] + (fx.numerator % P) * pow(fx.denominator, -1, P) * pow(s19, d_, P)) % P
    trial = flint.nmod_mat(cur + [vals], P)
    r2 = trial.rank()
    if r2 > rk:
        cur.append(vals)
        rk = r2
        moving_sel.append(j)
    if rk == meta['nrow'] - len(NM['rows']):
        break
log('moving vectors selected: %d (rank at s = 1/9 now %d = nrow - rho = %d)' % (len(moving_sel), rk, meta['nrow'] - len(NM['rows'])))
moving = []
for j in moving_sel:
    m = NB['moving'][j]
    fr = [[Fraction(x) for x in coef] for coef in m]
    den = 1
    for coef in fr:
        for x in coef:
            den = den * x.denominator // math.gcd(den, x.denominator)
    moving.append(dict(den=den, coef=[{i: int(x * den) for i, x in enumerate(coef) if x} for coef in fr]))
aux = {rename(kk): [[int(x) for x in row] for row in v] for kk, v in cert['modules'].items() if kk.startswith('2|')}
aux.update({kk.replace('|2|', '|A|'): [[int(x) for x in row] for row in v] for kk, v in cert['eq_modules'].items() if '|2|' in kk})
eqg = {}
for g, v in cert['eq_groups'].items():
    parts = []
    for part in v['parts']:
        loc = []
        for (n0, slot, order, kind, mkeys) in part['local']:
            site = n0 != 2
            loc.append(('S' if site else 'A', int(slot), tuple(int(x) for x in order), kind,
                        [mk.replace('|%d|' % n0, '|S|' if site else '|A|') for mk in mkeys]))
        parts.append(dict(family=part['family'], sign=int(part['sign']), local=loc))
    eqg[g] = dict(parts=parts)
diagrams = {(int(m), tuple(cut)): {tuple(lab): (keys, [[int(x) for x in row] for row in C]) for lab, (keys, C) in labs.items()}
            for (m, cut), labs in D.items()}
pkg = dict(format='ep3-alld-v1', k=k, d0=9, nrow=meta['nrow'], diagrams=diagrams, aux=aux, eq_groups=eqg, types=types,
           eq_items=eq_items, stage1=dict(q=q, cols=s1), stage2=stage2,
           W=dict(vperp=vperp, moving=moving, deg=int(NB['Dw'])), margin=str(Fraction(MG['mmin'])))
raw = pickle.dumps(pkg, protocol=4)
open(outp, 'wb').write(lzma.compress(raw, preset=9 | lzma.PRESET_EXTREME))
log('package written: %s (%.1f MB pickled, %.1f MB xz)' % (outp, len(raw) / 1e6, len(open(outp, 'rb').read()) / 1e6))
