"""CRT combination of the exact_words.py residues and the final margin (own implementation).

For every family and orbit, the numerators N0(o) = Den R0(o), N1(o) = Den R1(o) are integers with
|N| <= Den * B (B the uniform shadow bound of shadow_words.py).  With the CRT primes P (all but the last) and
prod(P) > 2 Den B + 2, the symmetric CRT lift is the exact N; the LAST prime is a check prime: the lift must reduce to
its residue for every orbit.  Then S0 = sum |N0| / Den, S1 = sum |N1| / Den exactly, and
    margin = nu - LK(s0) (S0 + s0 S1 + s0^2 S2),   LK(s0) = 16 ||G_a^+||_inf / (1 - 6 s0 - 11 s0^2 - 6 s0^3)^5.
Usage: combine_words.py shadow.pkl lk.pkl 'res/*.npz' out.pkl
"""
import os, sys, glob, pickle, math, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction
import numpy as np
import k5defs as KD

t0 = time.time()
log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
SH = pickle.load(open(sys.argv[1], 'rb'))
LKD = pickle.load(open(sys.argv[2], 'rb'))
files = sorted(glob.glob(sys.argv[3]))
outp = sys.argv[4]
res = {}
meta = None
for fn in files:
    z = np.load(fn)
    p, f, ch, nch = int(z['p']), str(z['f']), int(z['chunk']), int(z['nchunk'])
    m = (int(z['E']), int(z['Elam']), str(z['Den']))
    assert meta is None or meta == m, ('inconsistent E/Elam/Den', fn)
    meta = m
    d = res.setdefault((p, f), {})
    assert ch not in d, ('duplicate chunk', fn)
    d[ch] = (nch, z['R0o'].astype(object), z['R1o'].astype(object))
E, Elam, Den = meta[0], meta[1], int(meta[2])
assert E == SH['E'] and Elam == SH['Elam']
primes = sorted(set(p for p, f in res))
for p in primes:
    for f in KD.FAMS:
        d = res[(p, f)]
        nch = {v[0] for v in d.values()}
        assert len(nch) == 1 and set(d) == set(range(nch.pop())), ('missing chunks', p, f, sorted(d))
log('%d result files; primes %s; E=%d Elam=%d Den bits %d' % (len(files), primes, E, Elam, Den.bit_length()))
crt_p, check_p = primes[:-1], primes[-1]
Mprod = math.prod(crt_p)
bound = max(max(SH['B0'].values()), max(SH['B1'].values()))
need = 2 * Den * bound + 2
assert Mprod > need, ('need more primes: prod 2^%.1f vs need 2^%.1f' % (math.log2(Mprod), math.log2(need)))
log('CRT over %d primes (2^%.1f) > 2 Den max(B0,B1) = 2^%.1f; check prime %d' % (len(crt_p), math.log2(Mprod), math.log2(need), check_p))
coef = [(Mprod // q) * pow(Mprod // q, -1, q) for q in crt_p]


def total(p, f, i):
    d = res[(p, f)]
    s = None
    for ch in sorted(d):
        v = d[ch][1 + i]
        s = v if s is None else (s + v)
    return np.array([int(x) % p for x in s], dtype=object)


S = {0: Fraction(0), 1: Fraction(0)}
rep = {}
for f in KD.FAMS:
    for i in (0, 1):
        R = [total(p, f, i) for p in crt_p]
        Rc = total(check_p, f, i)
        norb = len(Rc)
        N = [0] * norb
        acc = np.zeros(norb, dtype=object)
        for q, cf, r in zip(crt_p, coef, R):
            acc = acc + r * cf
        acc = np.array([int(x) % Mprod for x in acc], dtype=object)
        N = [x - Mprod if x > Mprod // 2 else x for x in acc]
        bad = sum(1 for o in range(norb) if N[o] % check_p != int(Rc[o]))
        assert bad == 0, ('check prime FAILED', f, i, bad)
        assert max(abs(x) for x in N) <= Den * bound * (1 + 1e-6) + 1
        s = Fraction(sum(abs(x) for x in N), Den)
        rep[(f, i)] = dict(norb=norb, S=s, maxabs=Fraction(max(abs(x) for x in N), Den), N=N if i == 0 else None)
        S[i] += s
        log('family %s R%d: %d orbits, check prime OK, EXACT sum |R%d(o)| = %.9e (max orbit %.3e)' % (
            f, i, norb, i, s, float(rep[(f, i)]['maxabs']), ))
s0 = LKD['s0']
LK = LKD['LK']
S2 = Fraction(math.ceil(SH['S2']))
tot = S[0] + s0 * S[1] + s0 ** 2 * S2
margin = KD.NU_Q - LK * tot
log('EXACT S0 = %s = %.9e' % (S[0], float(S[0])) if S[0].denominator < 10 ** 60 else 'EXACT S0 = %.9e' % float(S[0]))
log('EXACT S1 = %.9e;  S2 <= %s;  s0 = %s;  LK(s0) = %.9f' % (float(S[1]), S2, s0, float(LK)))
log('S0 + s0 S1 + s0^2 S2 = %.6e;  margin nu - LK (...) = %.9e  => %s' % (float(tot), float(margin),
    'POSITIVE (q_5(9/20, C) > 0 for every rank-2 C at every n >= 1/s0)' if margin > 0 else 'NOT POSITIVE'))
pickle.dump(dict(S0=S[0], S1=S[1], S2=S2, s0=s0, LK=LK, margin=margin, E=E, Elam=Elam, Den=Den, primes=primes,
                 rep={k: {kk: vv for kk, vv in v.items() if kk != 'N'} for k, v in rep.items()},
                 R0num={f: rep[(f, 0)]['N'] for f in KD.FAMS}), open(outp, 'wb'), protocol=4)
