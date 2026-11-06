"""Convert a v1-v3 exported certificate (blocks with kind src/gram + family) to the v4 format read by
verify_cert4.py (every block a Gram block with explicit row patterns)."""
import pickle
import sys

LETTERS = {'31': 'aaab', '22': 'aabb', '13': 'bbba'}


def pattern(f, cut):
    return ' '.join(LETTERS[f][i] + ('*' if i in cut else '') for i in range(4))


def main():
    cert = pickle.load(open(sys.argv[1], 'rb'))
    out = dict(cert)
    blocks = []
    for b in cert['blocks']:
        b2 = dict(b)
        if b['kind'] == 'src':
            cut = tuple(int(x) for x in b['modules'][0].split('|')[1].split(',') if x != '')
            b2['rows'] = [pattern(b['family'], cut)]
        elif b['kind'] == 'gram':
            b2['rows'] = ['a a b a*', 'b b a b*']
        elif b['kind'] == 'gram2':
            b2['rows'] = ['a a a* b*', 'a b b* b*']
        else:
            raise ValueError(b['kind'])
        blocks.append(b2)
    out['blocks'] = blocks
    if len(sys.argv) > 3 and sys.argv[3] == 'perturb':
        from fractions import Fraction
        Z = out['blocks'][0]['Z']
        Z[0][0] = str(Fraction(Z[0][0]) + Fraction(1, 10 ** 30))
    pickle.dump(out, open(sys.argv[2], 'wb'))
    print('converted %d blocks -> %s' % (len(blocks), sys.argv[2]))


if __name__ == '__main__':
    main()
