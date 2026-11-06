"""rel31b.pkl = rel31.pkl (selection: sel_eq, sel_gram, F, Fmax, kept) with the relative metric replaced by the exact
dyadic rounding Lnum/Lden (Lden = 2^E, E = 96 - floor(log2 max|L|)) of the accurate analytic-centre metric rel2_31.pkl.
Usage: make_rel31b.py rel2_31.pkl rel31.pkl out.pkl"""
import sys, pickle, math
import numpy as np
r2 = pickle.load(open(sys.argv[1], 'rb')); r1 = pickle.load(open(sys.argv[2], 'rb'))
mx = max(np.abs(L).max() for L in r2['L'].values())
E = max(0, 96 - int(math.floor(math.log2(mx))))
Lden = 2 ** E
out = dict(r1)
out['Lnum'] = {ti: [[int(round(x * Lden)) for x in row] for row in r2['L'][ti]] for ti in r2['kept']}
out['Lden'] = Lden
pickle.dump(out, open(sys.argv[3], 'wb'), protocol=4)
print('written %s, Lden 2^%d' % (sys.argv[3], E))
