#!/usr/bin/env python
"""Exact parametric certificates for the all-d profile LP with inputs (I2)-(I6) (profile_lp_k5.rows_exact with k5=True):
the thresholds gamma_6 = 0.368683... and gamma_7 = 0.318076... of Section 9 of the paper.
usage: cert_k5.py all:k:gref ...   (gref = a reference value just below the threshold, where the LP is solved)
Each run checks the polynomial identity q_k(g; a) = LB(g) + sum_i y_i(g) row_i(a) + ... exactly and certifies the sign of every
multiplier on a rational isolating interval of the threshold root (param_cert_ext2.certify).  verify_k5_certs.py re-checks the
printed certificate from the row labels alone."""
import os, sys
from fractions import Fraction as Fr
import sympy as sp
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # python -I does not add the script dir
from param_cert_ext2 import certify
from profile_lp_k5 import rows_exact as _rows_exact
rows_exact = lambda k, d=None, **kw: _rows_exact(k, d, k5=True, **kw)
for arg in sys.argv[1:]:
    ps = arg.split(':'); mode, k, gr = ps[:3]; k = int(k); gr = Fr(gr); d = None if mode == 'all' else int(mode)
    kw = dict((kv.split('=')[0], Fr(kv.split('=')[1])) for kv in ps[3:])      # optional t4=, t5=, tk4= thresholds
    R = rows_exact(k, d, **kw)
    C = certify(k, gr, R)
    print('k = %d d = %s: gamma* = %s  (root of %s) | rows %d | identity %s | CERTIFIED %s' % (
        k, mode, C['gs'], sp.factor(C['LB']), len(R), C['ident'], C['ok']), flush=True)
    for nm, expr, val, gd in C['mult']:
        print('    %-52s %s   (at g*: %.4e, > 0: %s)' % (str(nm), expr, val, gd), flush=True)
