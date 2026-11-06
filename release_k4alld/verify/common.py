"""Package paths: modules in zm/, inputs in certs/ and data/, regenerated intermediates in work/ (or $K4_WORK)."""
import os, sys, pickle
PKG = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(PKG, 'zm'))
WORK = os.environ.get('K4_WORK', os.path.join(PKG, 'work'))
os.makedirs(WORK, exist_ok=True)


def P(*a):
    return os.path.join(PKG, *a)


def W(*a):
    return os.path.join(WORK, *a)


def load_ftp():
    """exact polynomial-in-n per-site data (integer coefficients), data/ftpoly.pkl"""
    return pickle.load(open(P('data', 'ftpoly.pkl'), 'rb'))
