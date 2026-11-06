# k-copy Werner undistillability for α ≥ −11/(5k) in every dimension: exact verification package

**Theorem (Theorem 9.2 of the accompanying paper).** Let d ≥ 2 and let C be a complex matrix of rank at most two on (C^d)^{⊗k}.
Then

    q_k(11/(5k), C) ≥ 0  for every k ≥ 6,     and     q_k(56/(25k), C) ≥ 0  for every k ≥ 9,

where q_k(t, C) = Σ_{J ⊆ {1,…,k}} (−t)^{|J|} ‖Tr_J C‖²_F.

With Corollary 2.4 of the paper, the Werner state ρ(d, α) is therefore k-copy undistillable for every α ≥ −11/(5k) (k ≥ 6)
and every α ≥ −56/(25k) (k ≥ 9), in every dimension (Theorem 1.5).

The package also checks two further results of Section 9 and the computations of Section 10.6:
- the exact all-dimension thresholds γ_6 = 0.368683… and γ_7 = 0.318076… of the linear program;
- the numerical parts of Proposition 9.3(a): the constant of the method tends to 9/4;
- the five identities marked (†) in the proof of Theorem 10.7, symbolically, and the other steps of that proof,
  numerically for k = 2, …, 5.

Everything that the proofs use is checked in exact rational arithmetic, or by explicit bounds evaluated in exact or interval
arithmetic. Floating-point linear programs only propose candidates.

## Quick start

    python3 -m venv .venv && .venv/bin/pip install -r requirements.txt     # numpy >= 2, scipy, sympy, mpmath
    PYTHON=.venv/bin/python ./run_all.sh

The run ends with `ALL-K CHECKS PASSED`. Logs go to `logs/`, and reference outputs are in `expected/`.
`REGEN=1 ./run_all.sh` also re-derives the two all-k certificates with the linear program (into `work/`) and checks the new
files. They may differ from the shipped ones, for example under another LP solver version, but they must pass the same
exact check.

## Method (paper, Section 9)

For C ≠ 0 of rank at most two the profile is a_j = average over |J| = j of ‖Tr_J C‖²_F / ‖C‖²_F, so a_0 = 1 and
q_k(t, C) = ‖C‖²_F Σ_j C(k, j)(−t)^j a_j.

The inputs (I1)–(I6) are inequalities for operators of rank at most two:
- (I1) the trace bound |Tr X|² ≤ 2‖X‖²_F, which with Lemma 9.1(a) gives 0 ≤ a_j ≤ 2;
- (I2) the two-copy inequality q_2(1/2, ·) ≥ 0;
- (I3) the inequality of Costa Rico;
- (I4) q_3(1/2, ·) ≥ 0;
- (I5) q_4(79/160, ·) ≥ 0 and (I6) q_5(9/20, ·) ≥ 0, the four- and five-copy theorems.

Lemma 9.1 applies each input to disjoint groups of copies, with frozen copies and compressed sets. Averaging over the
positions turns it into a row: a polynomial row(S) = base(S) · Π_l (1 + S^{s_l}), read as Σ_j row_j a_j ≥ 0.

A certificate for q_k(X/k) is a list of rows with rational weights y ≥ 0. With b_j = C(k, j)(−X/k)^j and
r = b − Σ_i y_i row_i,

    Σ_j b_j a_j ≥ r_0 + 2 Σ_{j≥1} min(0, r_j)      (the slack),

because every row is nonnegative on profiles, a_0 = 1 and 0 ≤ a_j ≤ 2. A positive slack proves q_k(X/k, ·) ≥ 0.
Lemma 2.3(b) then gives every smaller t.

**All k at once.** Each certificate file `certs/allk_k5_X*.json` covers every k ≥ k_0:
- (A) for k_0 ≤ k < J there is a certificate for each k;
- (B) for J ≤ k ≤ K a single limit certificate is used, with rows of size at most J (valid for every k ≥ J by Lemma 9.1).
  Its slack is evaluated exactly at each k, and a per-k certificate replaces it where it is negative. The degrees above J,
  which no row reaches, are bounded by TAIL ≥ Σ_{j>J} X^j/j!, using C(k, j)(X/k)^j ≤ X^j/j!;
- (C) for k > K, |C(k, j)(X/k)^j − X^j/j!| ≤ (X^j/j!)·j(j−1)/(2k), and the difference has the favourable sign for odd j.
  The slack is therefore at least δ_∞ − E_2/(K+1) − 2·TAIL, where δ_∞ is the slack of the limit certificate against
  (−X)^j/j! and E_2 = Σ_{2≤j≤J, j even} X^j/(j−2)!.

| file | X | k_0 | J | K | per-k certificates in (B) | smallest slack (A) / (B) / (C) |
|---|---|---|---|---|---|---|
| certs/allk_k5_X2.2.json | 11/5 | 6 | 12 | 1010 | 829 | 7.709e-3 / 1.800e-5 / 2.219e-5 |
| certs/allk_k5_X2.24.json | 56/25 | 9 | 14 | 5450 | 4286 | 1.875e-3 / 9.202e-7 / 8.762e-7 |

The certificates use only rows built from FHPV = (I2), CR = (I3), EP3 = (I4), K4 = (I5) and K5 = (I6), with compressed sets.

## What each step checks (run_all.sh)

| step | script | content |
|---|---|---|
| 0 | `sha256sum -c SHA256SUMS` | integrity of every shipped file |
| 1 | `code/allk_check.py` | exact check of (A), (B), (C) for both certificate files. It rebuilds every row polynomial from its label alone, shares no code with the row generators, solves no LP, and re-derives TAIL and E_2. Any label other than the inputs above makes it fail |
| 1b | `code/allk_check.py --no-k5` | negative control: with (I6) refused, the first file is rejected |
| 2 | `code/cert_k5.py`, `code/verify_k5_certs.py` | exact parametric certificates for γ_6 and γ_7 (multipliers are rational functions of t; polynomial identity; the threshold is the smallest positive root of an explicit polynomial; every multiplier is positive on a rational isolating interval). They are then re-checked from the printed labels by an independent verifier |
| 3 | `code/expo_k5.py` | Proposition 9.3(a), see below |
| 4 | `code/limit_lp_k5.py` | floating-point limit LP: c*_J = 2.2028, 2.2440, 2.2490, 2.24983, 2.249986 for J = 8, 10, 12, 14, 16 (illustration only) |
| 5 | `independent/` | an independent construction of both statements of Theorem 9.2 and of the numbers of Proposition 9.3(a), see below |
| 6 | `sec10/check_sec10.py` | the identities of Theorem 10.7 and numerical checks of its proof (Section 10.6), see below |

**Proposition 9.3(a) (step 3).**
- **Poisson mixture.** With τ = 9/20, x = 5τ(1 − ε) and E_k defined by (1 − xS/k)^k = ε + (1 − ε)(1 − τS)^5 E_k(S),
  write log E_k = Σ_r β_r S^r. The script checks β_r ≥ 0 for 2 ≤ r ≤ k, for all k ≥ 40 and ε ≤ 1/200 (Claim 1):
  - exactly for r ≤ 300 (minimum of r·F(r) is 3.6476, at r = 40);
  - beyond r = 300 by an explicit bound, 5 − 0.241 > 0 at s = 5.28. This bound uses −log(1 − y) ≤ y/(1 − y).
- **Truncation constant (Claim 2).** It is 21176.26 < 21177 at z = 8/5.
- **Sanity checks.** The formula for β_r agrees with a 50-digit series expansion, and the assembled certificate is
  checked at k = 30 and k = 40.

**Independent construction (step 5).** These scripts were written from the definitions of Section 9 only and share no code
with `code/`. `independent/a_cert_v2.py` builds its own rows and certificates and covers k ≥ J by finitely many intervals of
k. On each interval it bounds b(k) below coordinatewise, using that C(k, j)/k^j increases with k; the last interval is
unbounded:
- X = 11/5: k = 6..11 per k, then intervals up to [1155, ∞);
- X = 56/25: k = 9..13 per k, then intervals up to [2361, ∞).

The script asserts that the intervals are contiguous. `independent/a_cert_v3.py` repeats both runs without compressed
trace-bound rows. `independent/a_controls.py` checks three things:
- every row of size ≤ 14 is nonnegative at the point (1, 4/9, 0, …) of Proposition 9.3(b);
- the LP fails, as it must, without K5 at X = 11/5 and with K5 at X = 113/50 > 9/4;
- on 30 random rank-two matrices on 7 qubits, the profile reproduces q_7 and the rows used are nonnegative.

`independent/b_check_v2.py` re-checks every number of Proposition 9.3(a). It uses its own exact and interval code, and
its bound beyond r = 300 uses the logarithm itself, giving 5 − 0.0179. Its check P5 also covers a level-by-level interval
argument that the paper does not need, because it uses Lemma 2.3(b).

**Section 10.6 (step 6).** `sec10/check_sec10.py` verifies with sympy the five identities marked (†) in Steps 3 and 4 of
the proof of Theorem 10.7, typed as displayed in the paper, and the eigenvalues of the quadratic part in Step 4. It then
checks Steps 1–4 numerically for k = 2, …, 5, with random positive coefficients from a fixed seed: the operator identity
for q_k and (10.5), the formula for A_10, the block structure of A_00, Lemma 10.8 on one to six copies, the bound
Ã_00 ≥ A̲_00, the scalar form of Step 3 and the chain down to G ≥ 0. It takes a few seconds.

## Validity

The computation proves the slack inequalities for these certificates. The paper proves the rest:
- the inputs (I1)–(I6): the two-copy theorem, the inequality of Costa Rico, Theorem 1.2, and Sections 6 and 7. The
  four- and five-copy theorems have their own verification packages;
- the rows (Lemma 9.1) and the slack bound (Section 9);
- t-monotonicity (Lemma 2.3(b)) and the passage to undistillability (Corollary 2.4);
- the steps of the proof of Theorem 10.7 that step 6 checks only numerically.

## Compute requirements (measured reference run)

`./run_all.sh` took about 1 min of wall time on one core of a recent x86-64 server (`expected/run_all_reference.log`). The
largest step, the exact check of `certs/allk_k5_X2.24.json`, takes about 25 s. The peak resident memory was 0.2 GB.
`REGEN=1` added 35 s; its logs are `expected/regen_*.log`. A fresh run reproduces the files in `expected/` except for the
printed timings.

## Contents

- `certs/allk_k5_X2.2.json` (sha256 5fb7333b…fb5c6bbc) and `certs/allk_k5_X2.24.json` (sha256 62924578…7dddf0ef): the all-k
  certificates. They hold the per-k certificates of (A), the limit certificate, the per-k certificates of (B), and K, J,
  TAIL and E_2. The weights are exact rationals stored as strings.
- `code/`:
  - `allk_check.py`: exact checker for the certificate files;
  - `allk_dump.py`: writes them from the LP;
  - `profile_lp_k5.py`: row generator; it uses `param_cert_ext.py` (base inequalities), `profile_lp_ext2.py`,
    `profile_lp_ext.py` and `profile_lp.py` (helpers);
  - `cert_k5.py` with `param_cert_ext2.py`: parametric certificates;
  - `verify_k5_certs.py`: their independent check;
  - `expo_k5.py`: Proposition 9.3(a);
  - `limit_lp_k5.py`: limit LP.
- `independent/`: `a_cert.py` (imported by `a_controls.py`), `a_cert_v2.py`, `a_cert_v3.py`, `a_controls.py`,
  `b_check_v2.py`.
- `sec10/check_sec10.py`: the checks of Section 10.6.
- `expected/`: reference outputs of `run_all.sh`.
- `LICENSE`: CC-BY-4.0.
- `SHA256SUMS`: every shipped file.

## Notes

- The original computation also generated rows of a further inequality (labelled FOI, Σ_i a_{k_i} ≤ m + 1 on m groups). It
  is not among the inputs of the paper, and none of its rows carries weight in the shipped certificates or in γ_6 and γ_7.
  The row generator of this package therefore leaves those rows out, and both verifiers reject them.
- The row generator still contains options for fixed dimension (the qutrit inputs of Section 8). This package does not
  use them.
