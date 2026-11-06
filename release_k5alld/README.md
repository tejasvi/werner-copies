# Five-copy Werner undistillability for α ≥ −9/20 in every dimension: exact verification package

**Theorem.** For every local dimension d ≥ 2 and every α ≥ −9/20 = −0.45, the Werner state ρ(d, α) = (I + αF)/(d² + αd) is 5-copy undistillable.

Equivalently, for every complex matrix C on (C^d)^{⊗5} of rank at most two and every t ∈ [0, 9/20],

    q₅(t, C) = Σ_{J ⊆ {1,…,5}} (−t)^{|J|} ‖Tr_J C‖²_F ≥ 0.

By Costa Rico's criterion (Lett. Math. Phys. 115:47, 2025), the two statements are equivalent. For α > 0 every term of q₅(−α, ·) is nonnegative.

This directory reproduces the computer-assisted part of the proof in exact rational arithmetic, end to end, from the certificate. The proof has the structure of the four-copy theorem (Theorem 1.3 and Section 6 of the accompanying paper) with k = 5.

## Quick start

    python3 -m venv .venv && .venv/bin/pip install -r requirements.txt     # numpy >= 2, scipy, sympy (python-flint only for RUN_CROSS)
    PYTHON=.venv/bin/python ./run_all.sh 32                                 # 32 = parallel exact-worker jobs

The run ends with `K5 EXACT CHECK PASSED`. Logs go to `logs/` and regenerated intermediates to `work/`. Reference outputs are in `expected/`.

Optional switches:
- `RUN_E2E=1` runs the physical-point checks (step 7).
- `RUN_CROSS=1` runs the class-sum verifier that accompanied the certificate (step 8).

## Proof structure

1. **Dimension monotonicity (paper, Lemma 2.3(a)).** If q₅(t, ·) ≥ 0 on rank-≤2 matrices in dimension D, the same holds in every d ≤ D, because zero padding by an isometry preserves rank and every ‖Tr_J C‖. It therefore suffices to prove q₅(9/20, ·) ≥ 0 for every d ≥ d₀ = 10¹⁰.
2. **t monotonicity (paper, Lemma 2.3(b)).** If q_j(t, ·) ≥ 0 for all j ≤ 5, then q₅(t′, ·) ≥ 0 for all 0 ≤ t′ ≤ t. Moreover, q₅(t, ·) ≥ 0 implies q_j(t, ·) ≥ 0 for j < 5.
3. **Slack form (paper, Lemma 3.6), applied at each fixed n ≥ 4.** Fix PSD multipliers Q_b = M_b M_b^T on the raw spaces of the blocks, equality multipliers λ, and ν = 1/1000. Then for every rank-2 C, with X its symmetrized four-replica moment tuple,

       c(X) ≥ (ν − LK(n) Σ_o |R(o; 1/n)|) τ(X),   LK(n) = 16 (n⁴‖G_site(n)^{-1}‖_∞)⁵ ‖G_aux⁺‖_∞,

   where R(o; s) is the orbit sum of the word-level residual. The inequality uses that every raw block is PSD on physical tuples and every equality row vanishes there; this is paper Theorem 3.5, whose proof does not depend on k.
4. **Residual bound.** Every word residual is a polynomial in s = 1/n:

       ρ(w; s) = R0(w) + s R1(w) + (terms of degree ≥ 2),

   and for 0 ≤ s ≤ s₀,

       Σ_o |R(o; s)| ≤ S0 + s S1 + s² S2.

   For n ≥ 10¹⁰:

   | quantity | value |
   |---|---|
   | S0 = Σ_o \|R0(o)\| | 2.225624e-10 (exact) |
   | S1 = Σ_o \|R1(o)\| | 77278.70 (exact) |
   | S2 | ≤ 1.15399e12 (absolute shadow) |
   | LK | ≤ 2.7555556 |
   | margin ν − LK(S0 + s₀S1 + s₀²S2) | **9.786730e-4 > 0** |

   Steps 1–4 together prove the theorem.

## What each script checks (run_all.sh)

| step | script | content |
|---|---|---|
| 0 | `sha256sum -c SHA256SUMS` | integrity of every shipped file |
| 1 | `verify/lk5.py` | exact ‖G_aux⁺‖_∞ = 31/180 (rank 14), the Neumann bound for G_site(n), and LK(10¹⁰) ≤ 2.755555563822 |
| 2 | `verify/ft_spot.py` | the per-site polynomial data `data/ftpoly.pkl` agree with the exact local Fourier data J^T V_p^Γ J at n = 4, 5, 6 (all 7 cuts, all labels, all permutations) |
| 3 | `verify/orbits_words.py` | orbit labels of all 24⁶ words under the symmetry group; every generator preserves them, their number equals the Burnside count, and every orbit size divides the group order. Counts 36195 / 79245 / 36195 |
| 4 | `verify/shadow_words.py` | uniform magnitude bounds for the Chinese remainder step, and the rigorous upper bound on S2 (full absolute shadow, all orders) |
| 5 | `verify/exact_words.py` | exact residues mod p of the orbit sums of R0 and R1. Every term is expanded over all 24⁶ words (no class reduction). Runs 10 primes p < 2²¹ × 3 families × 8 key chunks |
| 6 | `verify/combine_words.py` | CRT over 9 primes (189 bits), checked against the 10th; exact S0 and S1 as rationals with denominator 2^132·5⁵; the margin |
| 7 (optional) | `verify/e2e5.py` | physical rank-2 points entangled across all five sites (sums of two product operators), at n = 4, 50, 1000, 10¹⁰. Checks: the objective reproduces q₅; the trace reproduces Tr X; the coefficient bound of step 3 holds (n = 4, 10¹⁰); every literal equality row vanishes; every raw block of the certificate is PSD (keys with at most 1100 rows) and ⟨Q, M⟩ ≥ 0 for all keys |
| 8 (optional) | `crosscheck/verify_alld_k.py` | the exact verifier that accompanied the certificate. It uses class sums over site-letter multisets and per-orbit magnitude bounds. It agrees with step 6 on S1, S2 and the margin to 7 digits; its own rounding of the equality multipliers changes S0 in the 5th digit |

Notes:
- **Rounding.** The exact check uses M rounded to 2^-66 (so Q = M M^T is exactly PSD) and equality multipliers rounded to 2^-69. The trace multiplier is exactly ν = 1/1000.
- **Equality rows.** The site part of an equality functional acts on S₃ words, which are linearly independent operators for n ≥ 3, so any functional is admissible. The ancilla part (n = 2) is expressed on literal trace rows G·A of the contrast, which vanish whenever the contrast operator vanishes.
- **Arithmetic in step 5.** Residues are held in float64. Every product and partial sum stays below 2⁵³, so the BLAS contractions are exact.

## Validity

The computation proves the margin inequality for this certificate. Validity of each ingredient is proved in the accompanying paper, and none of the proofs depends on k:
- every raw block is a compression (⊗J)^T (tw X_f)^{Γ_cut} (⊗J) of a twirled partial transpose of the rank-one moment X_f = |ψ⟩⟨ψ|, which is PSD because ψ is a product over replicas, so the block is PSD on physical tuples; every equality row vanishes there (Theorem 3.5);
- zero padding and t-monotonicity (Lemma 2.3);
- the slack form (Lemma 3.6).

The certificate uses only single-family blocks: X31 and X13 on the cuts (), (3), (0), (0,1), and X22 on (), (0), (2), (0,1), (0,2), 11409 blocks in 5627 keys.

Index convention: the X13 replica pattern is (b, b, b, a), with a in slot 3.

## Compute requirements (measured reference run)

These figures come from a clean replay of `RUN_CROSS=1 ./run_all.sh 32` on an x86-64 server with 64 hardware threads that was shared with other jobs:
- **Whole run:** 2 h 23 min wall time and 62.6 CPU-hours (user 58.6 h + sys 4.0 h). Reference logs are in `expected/run_all_reference.log` and `expected/worker_times.txt`.
- **Exact step (step 5):** 240 jobs. Each took 9–19 min (mean 14.5 min) with 32 running concurrently. The sum of per-job wall times was 57.8 h, and each job used about 4.5 GB of memory.
- **Orbit labels (step 3):** 1.5 min and about 12 GB per family.
- **Other steps:** steps 1, 2, 4 and 6 take a few minutes in total.
- **With N parallel jobs** the exact step takes about 240/N × 10–15 min. Use N ≤ (memory in GB)/5.
- **Optional steps:**
  - `RUN_CROSS=1` took 25 min with 12 processes. It reports S0 = 2.2255e-10 (the equality multipliers are rounded independently, so S0 differs from step 6 in the 5th digit), the same S1 and S2, and margin 9.786730e-4;
  - `RUN_E2E=1` takes 12–26 min per value of n on one core (four values). Its reference outputs are `expected/e2e5_1_n*.log`.

## Contents

- `certs/k5_cert_t9_20.pkl`: the certificate. It is the producer's file (sha256 a2c0bdf7…12b7) with one bookkeeping field (`source`, a path) shortened; all data fields are identical.
- `data/ftpoly.pkl`: per-site polynomial data (sha256 559789929b…50c2), the same file as in the four-copy package.
- `zm/`: `local.py` (exact local module data, used for the ancilla), together with `relax.py` and `exact.py` for the cross-check. These are copied unchanged from the code that produced the certificate.
- `verify/`: the exact verifier.
- `crosscheck/verify_alld_k.py`: the class-sum verifier that accompanied the certificate. Only its module path and its loader of `data/ftpoly.pkl` differ from the original, whose sha256 is fc7ebedbb47c607470c452066bb1eb8696f9880e788392c7daaff5533433bc5c.
- `expected/`: reference outputs of `run_all.sh` (one log per step; `run_all_reference.log` is the full output of the replay above) and of the optional checks.
- `LICENSE`: CC-BY-4.0.
- `SHA256SUMS`: every shipped file.

## Caveats

- The relaxation data (typed spaces, local Fourier data) come from the computation that produced the certificate. Their validity is the content of paper Theorem 3.5. Step 2 checks the per-site data against the exact local Fourier data at n = 4, 5, 6, and step 7 checks block positivity on physical points numerically.
- The physical points of step 7 are sums of two product operators. The exact residual computation of step 5 covers every word.
