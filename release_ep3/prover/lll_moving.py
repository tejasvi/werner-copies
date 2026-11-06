"""Size reduction of the moving left-kernel witness: LLL (python-flint) on a random integer projection of the 293
integer-scaled RREF moving vectors (degree <= 5), the unimodular transform applied to the full vectors, then 107
short vectors independent at s = 1/9 (together with V^perp) are selected.  Output: pickle with the new moving list."""
import lzma, math, pickle, random, sys, time
from fractions import Fraction
import numpy as np
import flint
sys.set_int_max_str_digits(0)
t0 = time.time(); log = lambda s: print('[%.0fs] %s' % (time.time() - t0, s), flush=True)
NB = pickle.load(open(sys.argv[1], 'rb'))
pkg = pickle.loads(lzma.decompress(open(sys.argv[2], 'rb').read()))
outp = sys.argv[3]
proj = int(sys.argv[4]) if len(sys.argv) > 4 else 600
nrow = pkg['nrow']; dw = NB['Dw']
L = len(NB['moving'])
dimv = (dw + 1) * nrow
rows = []
for m in NB['moving']:
    fr = [Fraction(x) for coef in m for x in coef]
    den = 1
    for x in fr:
        den = den * x.denominator // math.gcd(den, x.denominator)
    rows.append([int(x * den) for x in fr])
hb = max(abs(x).bit_length() for r in rows for x in r)
log('%d moving vectors of length %d, max entry %d bits' % (L, dimv, hb))
random.seed(12345)
nz = [(random.randrange(dimv), random.choice((-1, 1))) for _ in range(proj * 40)]
P = [[0] * proj for _ in range(dimv)]
for i, (pos, sg) in enumerate(nz):
    P[pos][i % proj] += sg
V = flint.fmpz_mat(rows)
Pm = flint.fmpz_mat(P)
M = V * Pm
log('projection %d x %d computed' % (L, proj))
red, U = M.lll(transform=True)
log('LLL done')
W2 = U * V
ents = [[int(W2[i, j]) for j in range(dimv)] for i in range(L)]
hts = [max(abs(x).bit_length() for x in r) for r in ents]
nnz = [sum(1 for x in r if x) for r in ents]
order = sorted(range(L), key=lambda i: (hts[i], nnz[i]))
log('reduced vectors: entry bits min %d median %d max %d (before: %d)' % (min(hts), sorted(hts)[L // 2], max(hts), hb))
P0 = 1000003
s0 = pow(9, -1, P0)
base = []
for v in pkg['W']['vperp']:
    row = [0] * nrow
    for i, val in v['ent'].items():
        row[i] = val % P0
    base.append(row)
rk = flint.nmod_mat(base, P0).rank()
sel = []
for i in order:
    r = ents[i]
    val = [sum(r[e * nrow + j] * pow(s0, e, P0) for e in range(dw + 1)) % P0 for j in range(nrow)]
    trial = flint.nmod_mat(base + [val], P0).rank()
    if trial > rk:
        base.append(val); rk = trial; sel.append(i)
    if rk == nrow - len(pkg['stage2']['R']):
        break
log('selected %d reduced vectors (rank %d); their max entry %d bits' % (len(sel), rk, max(hts[i] for i in sel)))
moving = []
for i in sel:
    r = ents[i]
    g = 0
    for x in r:
        g = math.gcd(g, x)
    moving.append(dict(den=1, coef=[{j: r[e * nrow + j] // g for j in range(nrow) if r[e * nrow + j]} for e in range(dw + 1)]))
raw = pickle.dumps(moving, protocol=4)
log('new moving witness: %.2f MB pickled, %.2f MB xz' % (len(raw) / 1e6, len(lzma.compress(raw, preset=6)) / 1e6))
pickle.dump(moving, open(outp, 'wb'), protocol=4)
