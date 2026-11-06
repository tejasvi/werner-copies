"""CRT-combine the per-prime orbit-sum residues into exact rationals R0(o), R1(o) (denominator Dden = 2^261 * 5^4),
then the exact S0 = sum_o |R0(o)|, S1 = sum_o |R1(o)|, and the uniform margin with the exact LK and an S2 upper bound.
Usage: combine.py s2_bound.pkl out.pkl res_p*_c*.pkl"""
import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))   # python -I does not add the script dir
import common
import sys, pickle, glob, os
from fractions import Fraction
import numpy as np

s2file, outp = common.W(sys.argv[1]), common.W(sys.argv[2])
files = []
for f in sys.argv[3:]:                      # relative paths and glob patterns are taken inside work/
    f = f if os.path.isabs(f) else common.W(f)
    files += sorted(glob.glob(f)) if any(ch in f for ch in '*?[') else [f]
assert files, 'no residue files found'
DDEN = 2 ** 261 * 5 ** 4
by_p = {}
for fn in files:
    d = pickle.load(open(fn, 'rb'))
    by_p.setdefault(d['p'], []).append(d)
primes = sorted(by_p)
fams = ['31', '22', '13']
resid = {}
for p in primes:
    parts = by_p[p]
    nch = parts[0]['nchunk']
    assert sorted(x['chunk'] for x in parts) == list(range(nch)), ('missing chunks for p', p)
    r = {}
    for nm in ('R0o', 'R1o'):
        for f in fams:
            s = sum(x[nm][f] for x in parts) % p
            r[nm, f] = (s * (DDEN % p)) % p           # residue of the integer numerator N = DDEN * R
    resid[p] = r
check_p = primes[-1]
use = primes[:-1]
P = 1
for p in use:
    P *= p
print('primes used for CRT: %d (%d bits); check prime %d' % (len(use), P.bit_length(), check_p))


def crt_vec(vals):   # vals: dict p -> int64 array
    n = len(next(iter(vals.values())))
    x = [0] * n
    M = 1
    for p in use:
        v = vals[p]
        inv = pow(M % p, p - 2, p)
        for i in range(n):
            t = ((int(v[i]) - x[i]) * inv) % p
            x[i] += M * t
        M *= p
    return [xi - M if xi > M // 2 else xi for xi in x]


out = {}
S = {}
for nm in ('R0o', 'R1o'):
    tot = Fraction(0)
    for f in fams:
        N = crt_vec({p: resid[p][nm, f] for p in use})
        chk = resid[check_p][nm, f]
        bad = sum(1 for i, ni in enumerate(N) if ni % check_p != int(chk[i]))
        mx = max(abs(ni) for ni in N)
        assert bad == 0, ('CRT check failed', nm, f, bad)
        assert mx.bit_length() < P.bit_length() - 2
        sab = sum(Fraction(abs(ni), DDEN) for ni in N)
        out[nm, f] = dict(norb=len(N), sum_abs=sab, max_abs=Fraction(mx, DDEN), bits=mx.bit_length())
        print('%s family %s: %d orbits, sum |R| = %.6e, max |R| = %.3e, max numerator bits %d (CRT check OK)' % (
            nm, f, len(N), float(sab), mx / DDEN, mx.bit_length()))
        tot += sab
    S[nm] = tot
S2b = pickle.load(open(s2file, 'rb'))['S2_upper']
s0 = Fraction(1, 1250000000)
eps = 6 * s0 + 11 * s0 ** 2 + 6 * s0 ** 3
LK = 16 * Fraction(31, 180) / (1 - eps) ** 4
gamma = Fraction(1, 10000)
tot = S['R0o'] + s0 * S['R1o'] + s0 ** 2 * Fraction(S2b)
margin = gamma - LK * tot
print('EXACT S0 = %.6e, EXACT S1 = %.6e, S2 upper = %.4e' % (float(S['R0o']), float(S['R1o']), float(S2b)))
print('LK(1.25e9) = %.7f; total = %.6e; margin gamma - LK*total = %.6e  => %s' % (
    float(LK), float(tot), float(margin), 'POSITIVE' if margin > 0 else 'NOT POSITIVE'))
pickle.dump(dict(per=out, S0=S['R0o'], S1=S['R1o'], S2_upper=S2b, LK=LK, gamma=gamma, s0=s0, margin=margin,
                 primes=primes), open(outp, 'wb'), protocol=4)
