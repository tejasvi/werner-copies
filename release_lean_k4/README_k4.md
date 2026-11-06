# Lean 4 formalization: four-copy endpoint property of Werner states at d = 3 (EP_4, t = 4979/10000 and 497/1000)

This package is a Lean 4 / Mathlib formalization of the four-copy qutrit results in version 3 of the paper. It proves the
four-copy endpoint property in local dimension 3 at `t = 4979/10000` and, from a second certificate, at
`t = 497/1000`, and the four-copy Werner statement given Costa Rico's criterion: the Werner state `ρ(3, α)` is not
4-copy distillable for `−4979/10000 ≤ α ≤ 1`.

The numerical certificates enter as Lean data modules, and every check on them is a proposition that Lean verifies.
The checks of the certificates' identity facts are split into slices: 120 slice checks for `t = 4979/10000` and 72 for
`t = 497/1000`. These slice checks are evaluated with `native_decide`; every other check is evaluated by Lean's kernel
(`decide +kernel`). There is no `sorry`.

## What is proved

`EP ι d t` (module `NPT.Basic`) states that `q t C ≥ 0` for every operator `C` of rank at most two on the copies `ι`
of `ℂ^d`, where `q t C = Σ_{J ⊆ ι} (−t)^{|J|} ‖Tr_J C‖²_F`.

| Theorem | Statement |
|---|---|
| `NPT.K4.D3T4979.EP_K4_4979` | `EP (Fin 4) 3 (4979 / 10000)` |
| `NPT.K4.werner_four_copy_4979` | given Costa Rico's criterion `hCR : CostaRico D`: for `−4979/10000 ≤ α ≤ 1`, `¬ D 4 3 α`, i.e. `ρ(3, α)` is not 4-copy distillable |
| `NPT.K4.D3T497.EP_K4_497` | `EP (Fin 4) 3 (497 / 1000)` |
| `NPT.K4.soundness_slack`, `NPT.K4.soundness_slack5` | soundness of moment certificates with residuals, for three and for five word families: well-formed data, positive semidefinite multipliers and class sums equal to small residuals within the slack imply `EP (Fin 4) 3 (β/α)` |

The Werner statement comes from `NPT.werner_four_copy_d3` (module `NPT.Main`), which turns any certificate theorem
`EP (Fin 4) 3 g` with `0 < g < 1` into undistillability for `α ∈ [−g, 1]`.

**Not formalized.**
- Costa Rico's criterion (Lett. Math. Phys. 115:47 (2025), Theorem 1), which relates Werner-state distillability to
  `q`. It enters as the hypothesis `CostaRico D`; quantum states and LOCC are not formalized.
- The four-copy property at `t = 1/2` and in other dimensions, and the five-copy results.

## Axioms

| Theorem | Axioms |
|---|---|
| `NPT.K4.D3T4979.EP_K4_4979`, `NPT.K4.werner_four_copy_4979` | `propext`, `Classical.choice`, `Quot.sound` and the 120 axioms `NPT.K4.Route.T4979.sliceOK{f}_{j}._native.native_decide.ax_1` (f = 0, …, 4; j = 0, …, 23) |
| `NPT.K4.D3T497.EP_K4_497` | `propext`, `Classical.choice`, `Quot.sound` and the 72 axioms `NPT.K4.Route.T497.sliceOK{f}_{j}._native.native_decide.ax_1` (f = 0, 1, 2; j = 0, …, 23) |

`AXIOMS_4979.txt` and `AXIOMS_497.txt` hold the complete `#print axioms` output of the two certificate theorems. Each
`native_decide` axiom records that one slice check `sliceOK{f}_{j} : sliceCheck … = true` evaluated to `true` by
compiled code; for these checks the trusted base therefore also includes the Lean compiler, its runtime (including GMP
big-integer arithmetic) and every `@[implemented_by]`/`@[extern]` implementation that the evaluated code uses. The
final audit (`AUDIT.md`) rebuilt every module of this package from scratch and ran `#print axioms` on every theorem of
every module: 24,760 theorems, and none depends on an axiom other than the three standard ones and the
native-evaluation axioms of the slice checks it uses. To print the axioms of the main theorems yourself after a full
build:

    lake env lean NPT/K4/Axioms.lean

## How it is proved

The certificate for each `t` is a moment (sum-of-squares type) certificate on four copies. Its word families are the
letter patterns `aaab`, `aabb`, `bbba` and, for `t = 4979/10000`, also `aaaa` and `bbbb` (the complete degree-4
relaxation with five families, called FULL5 in the README of the record's K4 certificate package); a word assigns one of the
24 permutations to each leg (the four copies and one auxiliary leg), and its class is its orbit under the family's
symmetry group (all of S₄ for `aaaa` and `bbbb`).
1. **Soundness with residuals** (`NPT/K4/SoundS.lean`, `NPT/K4/SoundS5.lean` and their imports; they build on the
   soundness theory of the three-copy package). The certificate identity is required only up to residuals at the class
   representatives. The residuals, scaled by an explicit integer `D`, are exact integers stored with the data, and one
   integer inequality (checked by the kernel) shows that their total is covered by the slack `ν` of the certificate.
2. **Data checks** (kernel): well-formedness (`wf_cert`, `wf5_cert`), positive semidefiniteness of every multiplier
   block (`blocks_psd`: 3816 blocks of size up to 135 for `t = 497/1000`, 4893 blocks of size up to 201 for
   `t = 4979/10000`, with integer `L·D·Lᵀ` hints whose remainder `2^{2F}·Z − L·D·Lᵀ` is checked to be diagonally
   dominant), the data bounds (`types_ok`, `maxJ_ok`), the class structure
   (`NPT/K4/Classes/`: every word is mapped to its class representative by a checked group element) and the
   consistency of the rule groups with the certificate (`NPT.K4.DataK497`, `NPT.K4.DataK4979`).
3. **Identity fact** (`NPT/K4/Route/`). The class sums of the certificate functional are computed slice by slice: the
   words with a fixed letter on the auxiliary leg form one slice (24 per family). A slice check first checks an
   a-priori bound (`partsBound < 2^(b−1)`) that makes its packed integer arithmetic exact, then evaluates the
   certificate's parts on all words of the slice, sums them per class into an accumulator tree keyed by the class
   representatives, and checks that every class sum cancels against the slice's stored offset. These are the
   `native_decide` checks above. The kernel checks that the offsets of the 24 slices add up to the negated residuals
   (`hoffK<f>_all`) and that the trees' keys are the representatives (`NPT.K4.Keys497`, `NPT.K4.Keys4979`). The
   assembly theorems `ep497_of_slicesB` and `ep4979_of_slicesB` combine all checks.

The certificate data are untrusted: they enter only through propositions that Lean checks. `STATEMENTS.md` lists the
theorems of the chain with their exact hypotheses.

## Relation to the three-copy package

The three-copy package of the published record (Zenodo 10.5281/zenodo.23604344; `EP (Fin 3) d (1/2)` for
d = 3, …, 8) is kernel-only. This package
uses 77 of its modules unchanged: every file outside `NPT/K4/` is byte-identical to the file of the same
path in the three-copy package. The new material is under `NPT/K4/`.

## Building

You need `elan` (or the toolchain itself), `git` and `python3`. The toolchain `leanprover/lean4:v4.35.0` is pinned in
`lean-toolchain`, and Mathlib with its dependencies in `lake-manifest.json`. The script fetches the prebuilt Mathlib with
`lake exe cache get`, which needs network access; on machines with many cores, raise the limit of open files first
(e.g. `ulimit -n 65536`).

**Memory.** Most modules build in seconds with a few GB. The exceptions are the positive-semidefiniteness checks of the
largest multiplier blocks (`NPT/K4/D3T497/Psd*.lean`, `NPT/K4/D3T4979/Psd*.lean`: up to 41 GiB of memory and 50 GiB
of address space, up to 33 minutes each) and the 192 slice checks (`NPT/K4/Route/T497/Chk*.lean`,
`NPT/K4/Route/T4979/Chk*.lean`: up to 8 GiB of memory and 19 GiB of address space, 12–62 minutes each). The modules
that import all of the certificate data (`EP497`, `EP4979`, `Final497`, `Final4979`, `Werner4`, `Axioms` under
`NPT/K4/`) use about 5 GiB of memory but up to 43 GiB of address space for the mapped `.olean` files. Plain
`lake build` builds independent modules in parallel and can exhaust the memory of an ordinary machine. Use the
sequential script:

    ./build_sequential.sh                    # every module, one at a time, then the axioms of the main theorems
    ./build_sequential.sh NPT.K4.Final497    # only the given modules and their imports

`build_sequential.sh` runs `lake build <module>` for one module at a time, in topological import order (imports first),
with `LEAN_NUM_THREADS=4`. It needs about 45 GB of free memory (a machine with 64 GB of RAM or more).

**Time.** On a 64-core x86-64 machine with 512 GB of RAM, the final audit built all 943 modules in 6.5 hours with up
to 24 modules at a time (103 CPU-hours in all). One module at a time takes on the order of 100 hours.

`lakefile.toml` sets `maxHeartbeats 400000` and `Elab.async false`, which helps under address-space limits. With an
address-space limit on a machine with many cores, keep `LEAN_NUM_THREADS` small (4, say); otherwise Lake and Lean can
fail to create threads.

## Contents

| Path | Content |
|---|---|
| `NPT/` | Lean sources: the import closure of the main theorems (`NPT/K4/` new, the rest from the three-copy package) |
| `NPT/K4/Axioms.lean` | `#print axioms` for the main theorems |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Lake setup |
| `build_sequential.sh`, `build_order.txt`, `scripts/topo_order.py` | sequential build; the modules in import order; the import-order tool |
| `STATEMENTS.md` | the theorems of the chain with their hypotheses |
| `AXIOMS_4979.txt`, `AXIOMS_497.txt` | `#print axioms` of the two certificate theorems |
| `AUDIT.md` | summary of the final audit |
| `LICENSE` | license |
| `SHA256SUMS` | SHA-256 of every file in the package |
