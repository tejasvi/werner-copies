# Kernel-only identity facts (EP_3 certificates, d = 3..8)

Each certificate's identity fact `NPT.Cert.EP3D<d>.idFact : Sem.IdFact cert` (structure in `NPT/Cert/Sem.lean`) is proved without `native_decide`. Every finite check is a `decide +kernel` declaration evaluated by Lean's kernel. Some docstrings mention an earlier version with `native_decide` checks (`IdFactNative.lean`); it is not part of this package, and nothing here imports it.

For every d = 3, …, 8, `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `NPT.Cert.EP3D<d>.idFact` and for `NPT.Cert.EP3_d<d>` (`AUDIT.md`).

## 1. Method

- **Family checks.** The class sums of each word family must vanish. The kernel checks this modulo pairwise-coprime moduli of 600 or 1200 bits, one declaration per (modulus, family) or per split declaration.
- **From congruences to equalities.** The Chinese remainder theorem (`KR.eq_zero_of_modEq_list`) turns the congruences into equalities, using kernel-checked crude bounds on the word values with 24·13824·B < Π p.
- **Other checks.** Orbit witnesses (`WitK`), rule-group items (`IdKChecks`), row and equality tables (`KTabT*`, `KEqT*`) and class-list lengths (`KClsLen`) are kernel-checked separately.

## 2. Soundness chain (module → key theorems)

| Module | Key theorems / role |
|---|---|
| `Ident/KRLib`, `KRLibEq` | Recursor-only kernel stages, each proved equal to its checked counterpart (`addS_eq` … `colStageR_eq`, `rowStageR_eq`, `finalStageR_eq`, `extLR_eq`). |
| `Ident/ModP`, `KRRed` | `partsF_mod`: each part's word values are congruent mod p to those of the reduced data. `certModR_eq`: reduction of the blocks in the kernel. |
| `Ident/KRItem`, `KRItem2`, `KRGlue` | `itemRowsC_gv`, `leafRowsC_gv`, `leafRowsC2_hleaf`: leaf rows (sparse `W` rows at d ≥ 4) have the values of `itemTF`. `LRShape` lemmas. |
| `Ident/KRTree`, `KRFamily`, `KRCheck` | `evalTreeRR_eq`, `slicesKR_gv`, `checkKR_sound`: packed word values; a passing check ⇒ every class sum ≡ 0 mod p. |
| `Ident/EqBox`, `KRIdFactB` | `partsF_eqBox`: λ-tensor equality boxes equal the rank-one equality parts. `hsum_of_checksB`. |
| `Ident/KRRoute` | `routeR_spec`, `okMod_sound`: class routing with sums, counts and flags. |
| `Ident/KRBound`, `KRBoundMod`, `KRBoundSplit` | Crude word bounds (`partsF_le_crudeB*`, `partsF_le_crudeBMod`, `partsF_split_le`). |
| `Ident/KRIdFact` | `KR.eq_zero_of_modEq_list` (CRT), `classSum_abs_le`, `hsum_of_checks`. |
| `Ident/KRSplit`, `KRSplitAsm`, `KROffs` | Families split over several declarations whose class trees start at offsets cancelling mod p: `checkKRo_sound`, `classSums_modP_split`, `hsum_of_checks_split`, `hsplit_last`, `offsZero_sound`. |
| `EP3D<d>/KPrimes`, `KBound`, `KChk*`, `KOff*`, `KAssembly*`, `KHsum`, `KChks`, `IdFact` | Per-d moduli and bounds, the kernel checks, the split offsets, and the assembly into `idFact`. |

## 3. Check plan

| d | Moduli (count × bits), packing width | Declarations per modulus (families f0 / f1 / f2) |
|---|---|---|
| 3 | f2: 10 × 600, 760; f0, f1: 5 × 1200, 1360 | f0 1 / f1 2 (split) / f2 1 |
| 4 | 6 × 1200, 1373 | f0 1 / f1 2 / f2 1 |
| 5, 6 | 7 × 1200, 1407 / 1418 | f0 2 / f1 3 / f2 2 |
| 7, 8 | 8 × 1200, 1428 / 1436 | f0 2 / f1 3 / f2 2 |

- **Measured in the final audit** (up to 8 modules at a time on a 128-core x86-64 machine; time per check, peak RSS, sum over the checks of d):

| d | checks | time per check | peak RSS | total check time |
|---|---|---|---|---|
| 3 | 25 | 261–410 s | 78.0 GiB | 2.25 h |
| 4 | 24 | 267–413 s | 78.8 GiB | 2.29 h |
| 5 | 49 | 227–334 s | 67.5 GiB | 3.91 h |
| 6 | 49 | 227–340 s | 67.5 GiB | 3.93 h |
| 7 | 56 | 227–364 s | 67.6 GiB | 4.53 h |
| 8 | 56 | 227–370 s | 70.7 GiB | 4.60 h |
| all | 259 | 227–413 s | 78.8 GiB | 21.5 h |

- **Split offsets.** For declaration j, offs_j = (−S_j) mod p, where S_j is the declaration's unreduced class sum, computed natively once per layout.
  - The offset modules `KOff<i>_<f>` carry only these numbers. Their sum ≡ 0 mod p is checked by the kernel (`offsOK<i>_<f>`).
  - The checks themselves enforce correctness, so wrong offsets would make a check fail.

## 4. Reproduce

Every module builds with `lake build <module>`; see `README.md`. Run the kernel checks one at a time, each under an address-space limit of about 100 GiB, and use `Elab.async false` there, as `lakefile.toml` does. `build_sequential.sh` builds every module one at a time.

    lake build NPT.Cert.EP3D3.KChk0_2        # one check
    lake build NPT.Cert.EP3D3.IdFact         # the d = 3 assembly; builds any missing checks in parallel

## 5. Notes on kernel cost

- **Hash collisions.** Lean hashes natural-number literals by their low 64 bits. Data or packed numbers whose low 64 bits are zero collide in the kernel caches, so the reductions add a position code first (`entryR2`).
- **Lazy counters.** An unevaluated `Nat.succ` counter threaded through a long kernel loop stalls the kernel. The loops here zip with data instead.
- **Horner packing.** Packing by `x + (rest <<< B)` keeps every partial number alive, so memory grows quadratically. Packing is balanced or per row instead.
- **Retention.** The kernel keeps every intermediate result until a declaration is checked, at several KB per reduction step. Recursor-based loops are 3–15× cheaper than structural recursion.
