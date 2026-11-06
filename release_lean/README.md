# Lean 4 formalization: three-copy endpoint property of Werner states (EP_3, d = 3..8)

This package is a Lean 4 / Mathlib formalization of the computer-assisted results of the published record
Zenodo 10.5281/zenodo.23604344. It proves the three-copy endpoint property at `t = 1/2` in local dimensions
d = 3, …, 8 (and, by zero padding, d = 2), the two-copy property at d = 3, and the three-copy Werner theorem at d = 3
given Costa Rico's criterion.

The numerical certificates of the record enter as Lean data modules. Every check on them is evaluated by Lean's
kernel (`decide +kernel`): there is no `native_decide` and no `sorry`.

## What is proved

`EP ι d t` (module `NPT.Basic`) states that `q t C ≥ 0` for every operator `C` of rank at most two on the copies `ι`
of `ℂ^d`, where `q t C = Σ_{J ⊆ ι} (−t)^{|J|} ‖Tr_J C‖²_F`.

| Theorem | Statement |
|---|---|
| `NPT.Cert.EP3_d3`, `NPT.Cert.EP3_d4`, …, `NPT.Cert.EP3_d8` | `EP (Fin 3) d (1/2)` for d = 3, …, 8 |
| `NPT.EP3_d2` | `EP (Fin 3) 2 (1/2)` (zero padding; every d′ ≤ d follows the same way, `NPT.EP_mono_dim`) |
| `NPT.EP2_d3` | `EP (Fin 2) 3 (1/2)` (restriction to two copies) |
| `NPT.werner_three_copy_d3'` | given Costa Rico's criterion `hCR : CostaRico D`: for `−1 ≤ α ≤ 1`, `D 3 3 α ↔ α < −1/2`, i.e. the Werner state `ρ(3, α)` is 3-copy distillable iff `α < −1/2` |
| `NPT.Cert.soundness`, `NPT.Cert.soundness_of_check` | soundness of the moment certificates: well-formed data, the identity fact and positive semidefinite multipliers imply `EP (Fin k) d (1/2)` |

The Werner theorem holds in the same form for d = 4, …, 8: `NPT.werner_three_copy hCR d (by norm_num) NPT.Cert.EP3_d<d>`.

**Not formalized.**
- Costa Rico's criterion (Lett. Math. Phys. 115:47 (2025), Theorem 1), which relates Werner-state distillability to
  `q`. It enters as the hypothesis `CostaRico D`; quantum states and LOCC are not formalized.
- EP_3 for d ≥ 9 (the record's all-d certificate), and the four- and five-copy results. `NPT.Main` states the four-
  and five-copy corollaries at d = 3 with the certificate theorem as a hypothesis.

## Axioms

Every theorem above depends only on `propext`, `Classical.choice` and `Quot.sound`. The final audit (`AUDIT.md`)
rebuilt every module of this package from scratch and ran `#print axioms` on every theorem of every module:
21,841 theorems, none with another axiom. To print the axioms of the main theorems yourself after a full build:

    lake env lean NPT/Axioms.lean

## How it is proved

The certificate for each d is a moment (sum-of-squares type) certificate. The proof has two parts.
1. **Soundness, once for all d** (`NPT/Cert/Soundness.lean` and its imports; no Haar measure, no Schur–Weyl duality).
   The Hilbert–Schmidt projection onto the walled-Brauer word algebras preserves positivity, commutes with the maps
   that define the certificate, and has orbit-constant coefficients after symmetrization. Hence the certificate's
   identity, with positive semidefinite multipliers, yields `q ≥ 0`.
2. **Per-d checks** (`NPT/Cert/EP3D<d>/`): well-formedness (`wf_cert`); positive semidefiniteness of every multiplier
   (`blocks_psd`, exact `L D Lᵀ`-type hints with diagonal dominance); and the identity fact (`idFact`: the class sums
   of the certificate functional vanish). The class sums are checked modulo pairwise-coprime 600- and 1200-bit moduli
   and lifted to exact equalities by the Chinese remainder theorem, with kernel-checked bounds (`README_kernel.md`).

The certificate data are untrusted: they enter only through propositions that the kernel checks. `README_lean.md`
describes the theorem chain module by module.

## Building

You need `elan` (or the toolchain itself, see below), `git` and `python3`. The toolchain `leanprover/lean4:v4.35.0`
is pinned in `lean-toolchain`, and Mathlib with its dependencies in `lake-manifest.json`. Without elan, put the `bin`
directory of the `leanprover/lean4:v4.35.0` toolchain first on your `PATH`; its `lake` is the one elan would select,
so this is equivalent. The scripts fetch the prebuilt Mathlib with `lake exe cache get`, which needs network access.
On machines with many cores, the parallel decompression of the cache can exceed the default limit of open files
("No file descriptors available"); raise it first, e.g. `ulimit -n 65536`.

**Memory.** Most modules build in seconds with a few GB. The 259 kernel checks of the identity facts
(`NPT/Cert/EP3D<d>/KChk*.lean`) are the exception: each takes 4–7 minutes and up to 79 GiB of memory (up to
90 GiB of address space). Plain `lake build` builds independent modules in parallel, so several checks can be
in memory at once and exhaust the RAM of an ordinary machine. Use the sequential script:

    ./build_sequential.sh              # everything, one module at a time, then the axioms of the main theorems
    ./build_sequential.sh NPT.Final    # only the d = 3 results and their imports

`build_sequential.sh` runs `lake build <module>` for one module at a time, in topological import order (imports
first), with `LEAN_NUM_THREADS=4`. It needs about 85 GB of free memory (a machine with 96 GB of RAM or more).

**Time.** On a 128-core x86-64 machine with 850 GB of RAM, the final audit built all 961 modules in 3.3 hours
with up to 8 modules at a time (25 CPU-hours in all). One module at a time takes about 25 hours.
`./build_sequential.sh NPT.Final` took 3.1 hours of build time for its 216 modules.

`lakefile.toml` sets `maxHeartbeats 400000` and `Elab.async false`, which helps under address-space limits. With an
address-space limit on a machine with many cores, keep `LEAN_NUM_THREADS` small (4, say); otherwise Lake and Lean can
fail to create threads.

## Contents

| Path | Content |
|---|---|
| `NPT.lean`, `NPT/` | Lean sources: the import closure of the main theorems |
| `NPT/Axioms.lean` | `#print axioms` for the main theorems |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lake setup |
| `build_sequential.sh`, `build_order.txt`, `scripts/topo_order.py` | sequential build; the modules in import order; the import-order tool |
| `README_lean.md` | the theorem chain, the trusted base and the modules |
| `README_kernel.md` | the kernel checks of the identity facts |
| `DESIGN_soundness.md` | design of the soundness proof |
| `AUDIT.md` | summary of the final audit |
| `LICENSE` | license |
| `SHA256SUMS` | SHA-256 of every file in the package |
