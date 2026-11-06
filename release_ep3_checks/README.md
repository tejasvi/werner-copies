# EP_3 for every local dimension d ≥ 3 — additional cross-checks: code, data and reference logs

The theorems of the accompanying paper rest on the separate verification package `release_ep3` (compact certificates
and a standalone verifier). This package holds the **additional, independent checks** listed in the supplement's table
of cross-checks (rows R1–R13). They confirm the three-copy theorem by other routes:
- exact fixed-d certificates for d ≤ 16, under two independent verifiers;
- a second construction for d ≥ 17;
- tests of the verifiers themselves.

None of these checks is needed for the proof. The package contains the scripts that ran them (copies in which only the
machine paths are replaced, see "Paths"), the certificates and input data they read, and their original logs. One
script is new: `code/lebesgue_rigorous.py` (row R13b) certifies the two Lebesgue constants that R12 uses.

## Quick start

    python3 -m venv .venv
    .venv/bin/pip install -r requirements.txt
    PYTHON=.venv/bin/python ./run_all.sh

`run_all.sh`:
- checks `SHA256SUMS`;
- runs the rows that take minutes on one core: R3, R6, R7, R9, R10, R13 and R13b, about 16 min in all;
- ends with `ALL SELECTED CHECKS PASSED (R3 R6 R7 R9 R10 R13 R13b)`.

The heavy rows (R1, R2, R4/R5, R8, R11, R12, and the rebuild R10b) take from 15 min to several hours. They run only
when named, e.g. `./run_all.sh R2`; `./run_all.sh list` prints their commands without running them. Outputs and logs
go to `$OUT`, by default `release_ep3_checks_out` next to the package directory (`OUT` must lie outside the package);
the reference logs are in `expected/`.

## Requirements

- Python 3.14 (the reruns used 3.14.4), with the versions pinned in `requirements.txt`: numpy 2.5.4, scipy 1.18.1,
  sympy 1.14.0, mpmath 1.3.0, python-flint 0.9.0.
- Memory: under 2 GB for the rows of the default run; 1–4 GB in the reruns of heavy rows measured here (R2 at d = 5,
  R4 at d = 3, the exports of R8, R11, one column file of R12; larger d were not measured). The uniform verification of
  R12 holds about 14–18 GB (estimated from its arrays).
- Disk: 3.5 GB for the package. R12 also needs its interpolation columns, 24 GB, which are regenerated into `$OUT`
  (see R12 below).
- All runs use one core: `run_all.sh` sets `OMP_NUM_THREADS=OPENBLAS_NUM_THREADS=MKL_NUM_THREADS=1`.

## The checks

Row labels: the row of the supplement's table, with its v3 label in parentheses.

| row | what the check establishes |
|---|---|
| R1 (V3) | Construction I, 5 ≤ d ≤ 16: the 12 certificates (1342 PSD multipliers, 272 equality multipliers) pass Verifier I: identity (3.2) on all orbit sums, every multiplier PSD. Their exact solves of S1 have 272 + 2362 unknowns, rank 2634. |
| R2 (V4) | Construction II, d ∈ {5, …, 10, 12, 16}: the 8 certificates (1347 PSD multipliers) pass Verifier II. |
| R3 (V5) | Audit of the 22 certificate files of R1, R2, R4, R5: every equality functional is a Stiefel contrast or a marginal, and every partial-transpose block transposes whole replicas. |
| R4, R5 (V1, V2) | The certificates at d = 3 (715 multipliers) and d = 4 (1237) pass Verifier I. |
| R6 (V6) | Both verifiers' semantics agree with dense implementations for d = 3, …, 8 (15 row-pattern sets, 16 cuts, coupled Gram, gram2, partial traces, Stiefel contrasts, objective, swap identity); perturbed certificates fail. |
| R7 (V8) | FT_poly(d) equals the verifier's literal local data at d ∈ {6, 9, …, 26, 30, 31, 50}. |
| R8 (V20) | Certificates built from the polynomial data at d = 17 and d = 23 pass Verifier I. |
| R9 (V9) | The columns of A(s) and c(s) have degree ≤ 12: their differences of order 13 vanish. |
| R10 (V10) | The 1934 vanishing combinations annihilate all columns and the objective; the 107 trace vectors have rank 107; q_3 = 0 at the 31 zero modes. |
| R11 (V11) | Exact certificates on the d = 6 face, strictly positive definite, at 30 dimensions. |
| R12 (V12) | Second construction on [0, 1/17]: θ ≤ 1.25×10⁻⁴, residual ≤ 2.85×10⁻⁸, correction ≤ 8.1×10⁻³ (≤ 7.45×10⁻² with every rounding term ×10), below the PSD margin 0.5495. Its two Lebesgue constants are certified by R13b. |
| R13 (V18) | Lebesgue constants of the interpolation points of R12: the bounds 3.4895 (28 points) and 3.0645 (16 points) used there, against 40-digit evaluations on a fine grid, 3.084 and 2.728. |
| R13b (new) | Certified by interval arithmetic at the exact nodes of R12: the Lebesgue constants are ≤ 3.083926 (28 points) and ≤ 2.727778 (16 points), below the constants 3.4895 and 3.0645 that R12 uses. |

Verifier I is `code/dim/verify_cert.py` (R1, R8) or `code/cert/verify_cert.py` (R4, R5); Verifier II is
`code/cert/verify_cert4.py`. Both build the permutation operators, partial transposes, partial traces and Gram index
rules literally and import nothing from the construction code.

### Times and memory

Reference times are those printed in the original logs. Those runs were made on a shared many-core x86-64 server, often
with several jobs at once. The rerun column gives wall time and peak memory of the shipped scripts, run from this
package on one core (nice 10) of the same kind of server.

| row | reference time (logs) | rerun: time, peak memory |
|---|---|---|
| R1 | 1758–2977 s per d; 8.0 h for the 12 | first two minutes only (start-up lines as in the logs) |
| R2 | 229–1525 s per d; 68 min for the 8 | d = 5: 172 s, 2.0 GB |
| R3, R6 (A–E) | not printed | 6 s, 0.7 GB |
| R4, R5 | 814 s (d = 3), 1668 s (d = 4) | d = 3: 525 s, 1.1 GB |
| R6 (negative test) | not printed | 3 min, 1.3 GB |
| R7 | ft_newn: 16–905 s per value (n = 50: 905 s); ft_check_d: not printed | 9 min for all 22 values, 1.8 GB |
| R8 | export not printed; verification 3877 s (d = 17), 6392 s (d = 23) | export: 6 s and 18 s, 1.5 GB |
| R9 | not printed | 70 s, 0.4 GB |
| R10 | not printed | 20 s, 0.3 GB |
| R10b (rebuild) | not printed | more than 10 min |
| R11 | check_relcert_modp: not printed | pd_check 75 s per file; pd_rel2 110 s per file; check_relcert_modp 140 s per file; about 70 min, 0.9 GB |
| R12 | columns 462–835 s per node, 3.0 h for 16; uniform_verify 2139 s; audit 251 s | columns for one node: 218 s, 4.0 GB |
| R13 | not printed | 144 s, 12 MB |
| R13b | new script | 0.6 s, 34 MB |

## Running the checks by hand

The commands below are those of `run_all.sh`. Set once, in the package directory:

    export PKG_OUT=$PWD/../release_ep3_checks_out    # pkgrun.py's default; any directory outside the package works
    mkdir -p $PKG_OUT; P=$PWD                        # P = the package directory
    PY="python3 -I -B"                               # or .venv/bin/python -I -B

`code/pkgrun.py SCRIPT ARGS` runs `code/SCRIPT` with its `<ROOT>` file paths mapped onto this package (see "Paths"
below). Scripts without such paths run directly. `R` = reference log in `expected/`.

**R1** (in `data/dim`; d = 5, …, 16):

    $PY ../../code/dim/verify_cert.py runs/certfile2_k3_d5.pkl     # last line: [...s] EXACT_CERTIFICATE_PASS

R: `expected/R1/verify2_k3_d*.log`.

**R2** (in `data/cert`; d = 5, 6, 7, 8, 9, 10, 12, 16):

    $PY ../../code/cert/verify_cert4.py runs/vm_certs/certfile4_k3_d5.pkl    # last line: [...s] EXACT_CERTIFICATE_PASS

R: `expected/R2/verify4_local_k3_d*.log`.

**R3 and R6, parts A–E** (package root):

    $PY code/pkgrun.py validity/check_validity.py      # last line: ALL CHECKS PASS; part E lists the 22 files, each ": ok"

R: `expected/R3_R6/check_validity.log`. Parts A–D are R6, part E is R3.

**R4, R5** (in `data/cert`; d = 3, 4):

    $PY ../../code/cert/verify_cert.py runs/certfile_k3_d3.pkl     # last line: [...s] EXACT_CERTIFICATE_PASS

R: `expected/R4_R5/verify_k3_d3.log`, `verify_k3_d4.log`.

**R6, negative test** (in `$PKG_OUT`). `convert_cert_v4.py` converts a Verifier I
certificate to the format of Verifier II; with the argument `perturb` it adds 10⁻³⁰ to one entry of one multiplier:

    $PY $P/code/cert/convert_cert_v4.py $P/data/cert/runs/certfile_k3_d3.pkl c3.pkl
    $PY $P/code/cert/convert_cert_v4.py $P/data/cert/runs/certfile_k3_d3.pkl c3p.pkl perturb
    $PY $P/code/cert/verify_cert4.py c3.pkl      # last line: [...s] EXACT_CERTIFICATE_PASS
    $PY $P/code/cert/verify_cert4.py c3p.pkl     # last line: [...s] FAIL   (exit status 0: read the verdict)

No reference log exists for this test (see "Notes").

**R7** (package root):

    $PY code/pkgrun.py dim/uni/ft_check_d.py 6 9 10 11 12 13 14 15 16
        # one line per d: d=6: ExactLocal == FT_poly for all cuts: True
    $PY code/pkgrun.py dimaudit/ft_newn.py 17 18 19 20 21 22 23 24 25 26 30 31 50
        # one line per n: n=17: ExactLocal(n,4,cut) == FT_poly(n) all cuts: True; ExactLocal(n,3,()) == ExactLocal(6,3,()): True (...s)

R: `expected/R7/ft_check_d.log`, `ft_newn.log`, `ft_newn_cert.log`.

**R8** (in `$PKG_OUT/R8`; n = 17, 23):

    $PY $P/code/pkgrun.py dim/export_cert.py $P/data/dim/runs/certnode_n17.pkl certfile_node_n17.pkl
        # exported 1342 blocks, 58 modules -> certfile_node_n17.pkl; the file equals data/dimaudit/runs/certfile_node_n17.pkl
    $PY $P/code/dim/verify_cert.py certfile_node_n17.pkl     # last line: [...s] EXACT_CERTIFICATE_PASS

R: `expected/R8/export_n17.log` (with the sha256 of the exported file), `verify_node_n17.log`, and the same for n = 23.

**R9** (package root):

    $PY code/pkgrun.py dim/lk/degree_checks.py    # (1) ... True; (2) label blocks with degree > 2f: 0; (3) ... = 24
    $PY code/pkgrun.py dim/lk/eqdeg_check.py      # equality columns: 4th differences vanish: True True
                                                  # objective * n^12: 13th differences vanish: True True

R: `expected/R9/degree_checks.log`, `eqdeg.log`.

**R10** (package root):

    $PY code/pkgrun.py dim/lk/fconst_check.py     # F_const dimension = 1934; three lines "... annihilate(s) ker(Ga) ...: True"
    $PY code/pkgrun.py dimaudit/fconst_colmap.py  # FT_a[:, colmap] annihilates ker(Ga) for all cuts and colmaps [...]: True
    $PY code/pkgrun.py dimaudit/tau_rank.py       # tau generators: 107 x 4675, exact rank over Q = 107 (stored 107); ...
    $PY code/pkgrun.py dimaudit/zm_exact_q.py     # distinct dense zero modes: 31, max |q3|/||C||^2 = 0.000e+00 (...)

R: `expected/R10/fconst.log`, `tau_rank.log`. `tau_rank.py` recomputes the exact rank of the stored trace vectors
`data/dim/lk/tau_exact2.pkl`. **R10b** rebuilds those vectors from scratch (more than 10 min); it writes its output to
the file named as first argument, so do not point it at the shipped file:

    $PY code/pkgrun.py dim/lk/exact_tau2.py $PKG_OUT/tau_exact2.pkl 107    # last line: ... exact rank over Q: 107

**R11** (in `data/dim`):

    $PY ../../code/dim/uni/pd_check.py runs/cert2_k3_d{6,9,10,11,12,13,14,15,16}.pkl runs/certnode_n{17..28}.pkl
        # 21 lines "...: d=..., 1342 multipliers, consistent=True, strictly PD failures: 0"
    $PY ../../code/pkgrun.py dimaudit/face_check.py   (same 21 files)     # 21 lines "... N==Nref: True (len 1342 vs 2354/1342)"
    $PY ../../code/pkgrun.py dimaudit/pd_rel2.py runs/relcert2_n{31,38,48,64,93,150,288,790,7061}.pkl
        # 9 lines "...: n=... consistent=True kept==red2_d6: True; rigorous strict PD failures 0 of 1342 (...)"
    $PY ../../code/pkgrun.py dim/ac/check_relcert_modp.py runs/relcert2_n31.pkl    # n = 26, 31, ..., 7061
        # two lines "n=31 p=...: nonzero residual rows mod p: 0 -> OK"

R: `expected/R11/pd_check.log` (d = 6, 9…16), `pd_recheck.log` (d = 17), `pd_new.log` (d = 22, 24…28),
`face_all.log`, `pd_rel2.log`, `check_relcert_modp_n*.log`. The 30 dimensions are d = 6, 9, …, 28 (21 certificates)
and n = 31, 38, 48, 64, 93, 150, 288, 790, 7061 (9 relative certificates); n = 26 also has a relative certificate.

**R12** (package root). The interpolation columns `rcols_n*.npz` (16 files, 1.5 GB each) are not included. Regenerate
them into `$PKG_OUT/dim/ac`, where the uniform verification finds them through `pkgrun.py`:

    for n in 7061 790 288 150 93 64 48 38 31 26 23 21 20 19 18 17; do
        $PY code/pkgrun.py dim/ac/dumpcols_rel.py $n data/dim/ac/rel2_31.pkl data/dim/ac/rel31b.pkl $PKG_OUT/dim/ac/rcols_n$n.npz
    done        # (create $PKG_OUT/dim/ac first) last line per node: [...s] saved .../rcols_n$n.npz
    $PY code/pkgrun.py dim/ac/uniform_verify.py 7061,790,288,150,93,64,48,38,31,26,23,21,20,19,18,17 28
        # last line: [...s] PSD margin 0.5495 vs correction bound 8.075e-03 : UNIFORM CERTIFICATE VERIFIED
    $PY code/pkgrun.py dimaudit/uv_audit.py 7061,790,288,150,93,64,48,38,31,26,23,21,20,19,18,17 28
        # last line: [...s] PSD margin 0.5495 vs correction bound 7.449e-02 : AUDIT (INFL=10, Frobenius G) UNIFORM CERTIFICATE VERIFIED

R: `expected/R12/uniform_verify.log`, `uv_infl10.log`; the logs of the original column runs are in
`expected/R12/regenerate/` (times per node). Regenerated columns agree with the original ones up to the last bit of
some entries (floating-point summation order; for n = 26, 0.16 % of the entries of `R`, by at most 3.1×10⁻¹⁷, which is
below 0.003 of their error bounds `Rbound`), so the files' hashes differ from the original ones.

**R13** (package root):

    $PY code/dimaudit/lebesgue_check.py
        # 28 eval points     grid max 3.083926  rigorous upper bound 4.674031 (q=3.402e-01)
        # 16 M nodes         grid max 2.727778  rigorous upper bound 3.326558 (q=1.800e-01)
        # 16 integer nodes   grid max 37.244718  rigorous upper bound 45.420388 (q=1.800e-01)

No reference log exists; the lines above are from a rerun of the shipped script. Grid maxima are not bounds, and the
script's own Markov-type bounds on this grid (4.674, 3.327) are weaker than the constants 3.4895 and 3.0645 that
`uniform_verify.py` uses; R13b certifies those constants.

**R13b** (package root; `code/lebesgue_rigorous.py`, written for this package):

    $PY code/lebesgue_rigorous.py
        # 28 evaluation points (se): certified sup Lambda <= 3.083926 (lower bound 3.083925), ...; < 3.4895
        # 16 Chebyshev nodes (cm): certified sup Lambda <= 2.727778 (lower bound 2.727777), ...; < 3.0645
        # last line: [...s] LEBESGUE BOUNDS CERTIFIED: both constants used by uniform_verify.py hold

R: `expected/R13/lebesgue_rigorous.log` (from this package's run). The script rebuilds the nodes exactly as
`uniform_verify.py` does (and checks that they reproduce its values 3.4895 and 3.0645), then bounds sup Λ over [0, 1/17]
by interval arithmetic (`mpmath.iv`, outward rounding) on subintervals with exact rational end points, bisecting until
each enclosure is below a target; the bound is the largest upper end over subintervals that cover [0, 1/17]. The
supremum lies at the end points of the interval, where the enclosures are tight, so upper and lower bounds agree to 10⁻⁶.

## Paths

In the shipped scripts and logs, the absolute and home-relative paths of the machines that ran them are replaced by
`<ROOT>`; nothing else in them is changed.

The scripts were run in one directory tree, and several of them name files of that tree by absolute path (`sys.path`
entries, input data, outputs), now written `<ROOT>/...`. They are in `code/` with their original relative layout
(`cert/`, `dim/`, `dimaudit/`, `validity/`; `lib/qform.py` is a helper loaded by `check_validity.py`), and the data
files are in `data/` with the same layout. `code/pkgrun.py` runs a script with every `<ROOT>/...` path mapped:
- reads go to `$PKG_ROOT` (optional, a directory with the same layout), then `code/`, then `data/`, then `$PKG_OUT`;
- writes go to `$PKG_OUT`, never into the package.

It maps `open`, `sys.path`, `glob`, `os.path.exists/isfile/isdir` and `importlib.util.spec_from_file_location`, and it
stops the run if a script touches a `<ROOT>` path that was not mapped. Command-line arguments are used as given. In
the construction scripts kept for the record, `<ROOT>` also stands for the other home directories they used.

## Files

| path | content |
|---|---|
| `code/` | the scripts of R1–R13 (copies, paths written `<ROOT>`), `pkgrun.py`, and `lebesgue_rigorous.py` (R13b, new) |
| `code/dim/`, `code/dim/uni/`, `code/dim/lk/`, `code/dim/ac/` | Verifier I (`verify_cert.py`), local maps (`exact.py`, `exact_blocks.py`, `local.py`, ...), polynomial data and degree checks, consistency checks, relative certificates and the uniform verification; `chain_exact*.sh` and the other construction scripts are included for the record (they also call construction modules and data that are not included) |
| `code/cert/` | Verifier I for d = 3, 4 (`verify_cert.py`), Verifier II (`verify_cert4.py`), `convert_cert_v4.py`; `vm_scripts/exact_k3.sh` (construction of R2, for the record) |
| `code/dimaudit/` | the independent audit scripts (R7, R8, R10, R11, R12, R13) |
| `code/validity/` | `check_validity.py` (R3, R6) |
| `data/` | 79 files, 3.48 GB: certificates of R1 (365 MB), R2 (223 MB), R4/R5 (30 MB), R8 (exported, 156 MB), R11 (cert2 235 MB, certnode 356 MB, relcert2 2.06 GB), and the inputs of R7–R12 (polynomial data, face, kept types, trace vectors, anchor-relative metric, analytic centres) |
| `expected/` | the original logs, by row; `expected/R13/lebesgue_rigorous.log` is from this package's run of R13b |
| `run_all.sh` | runs the checks |
| `requirements.txt` | the Python packages |
| `LICENSE` | CC BY 4.0 |
| `SHA256SUMS` | sha256 of every file above |

## Notes

- The certificates and data are Python pickles. Load them only from this trusted package.
- `code/dim/exact_blocks.py` differs from the hash recorded for the original runs (it was edited on 2026-10-20); the shipped file reproduces the logs of every script that imports it.
- R7: `ft_newn.py` takes the values of n as arguments; without them it checks nothing, so the command must list them.
- R10b: `exact_tau2.py` writes the file named by its first argument; run it with an output path in `$OUT` (as `run_all.sh` does), never over `data/dim/lk/tau_exact2.pkl`.
- `verify_cert4.py` exits with status 0 even when it prints `FAIL`: read the printed verdict; `run_all.sh` checks the printed line.
- Some reference logs predate the last edits of the verifiers (the R2 logs, the R3/R6 log, the d = 3 log of R4, whose wording differs); the reruns give the same verdicts and lines.
- R6 negative tests: `convert_cert_v4.py IN OUT perturb` adds 10⁻³⁰ to one entry of one multiplier; `verify_cert4.py OUT` must then print `FAIL`, while the unperturbed conversion prints `EXACT_CERTIFICATE_PASS` (`run_all.sh R6`).
- The original logs of R7 lack d = 12 and d = 17 (the reruns cover them); no logs were kept of the R6 negative tests, of `exact_tau2.py`, `fconst_colmap.py`, `zm_exact_q.py`, or of R13.
- Times on other machines scale with single-core speed; the exact computations of R1, R2, R4, R5 and R8 dominate.
