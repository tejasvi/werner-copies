# The theorem chain, the trusted base and the modules

Lean 4.35.0 with Mathlib (commit pinned in `lake-manifest.json`). Published record: Zenodo 10.5281/zenodo.23604344.
`README.md` lists the main theorems and the build instructions; `README_kernel.md` describes the kernel checks of the
identity facts; `AUDIT.md` summarizes the final audit.

## 1. Statements

`EP ι d t` (module `NPT.Basic`) says that `q t C ≥ 0` for every operator `C` of rank at most two on the copies `ι`
of `ℂ^d`. Here `q t C = Σ_{J ⊆ ι} (−t)^{|J|} ‖Tr_J C‖²_F` is Costa Rico's form.

| Theorem | Statement |
|---|---|
| `NPT.Cert.EP3_d3`, …, `NPT.Cert.EP3_d8` | `EP (Fin 3) d (1/2)` for d = 3, …, 8 |
| `NPT.EP2_d3` | `EP (Fin 2) 3 (1/2)` |
| `NPT.EP3_d2` | `EP (Fin 3) 2 (1/2)` |
| `NPT.werner_three_copy_d3' hCR` | given Costa Rico's criterion `hCR`, for `−1 ≤ α ≤ 1`: `ρ(3, α)` is 3-copy distillable iff `α < −1/2` |
| `NPT.Cert.EP3_d3_of_idFact`, `NPT.Cert.EP3D<d>.EP_of_idFact` (d = 4..8), `NPT.EP2_d3_of_idFact`, `NPT.EP3_d2_of_idFact`, `NPT.werner_three_copy_d3_of_idFact` | the same statements with the identity fact `hid : NPT.Cert.Sem.IdFact cert` as a hypothesis |
| `NPT.Cert.soundness`, `NPT.Cert.soundness_of_check` | the soundness theorem of the moment certificates and its checkable form |
| `NPT.Cert.EP3D<d>.wf_cert`, `NPT.Cert.EP3D<d>.blocks_psd`, `NPT.Cert.EP3D<d>.idFact` (d = 3..8) | well-formedness, positive semidefiniteness of the multipliers and the identity fact of each certificate |

Every theorem in this table depends only on `propext`, `Classical.choice` and `Quot.sound` (`AUDIT.md`).

`EP3_d<d>` is `EP_of_idFact` (or `EP3_d3_of_idFact`) applied to `idFact`. The other statements follow from `EP3_d3`
by elementary reductions:
- restriction to two copies (`EP_restrict`, `EP_equiv`, `EP2_of_EP3`);
- zero padding (`EP_mono_dim`, `EP3_of_le`);
- the Werner corollary (`werner_three_copy`), which holds for every d with `EP (Fin 3) d (1/2)`, so also for
  d = 4..8 with `EP3_d<d>`.

`NPT.Main` also states the four- and five-copy corollaries at d = 3. They take the certificate theorem
`EP (Fin k) 3 g` as a hypothesis `hcert`; these certificates are not formalized.

## 2. The theorem chain

1. **Definitions and elementary reductions.**
   - `Basic`: `ptrace`, `frobSq`, `q`, `RankLE2`, `EP`.
   - `Product`: product formula.
   - `Sharp`: sharpness, `q_3 = 2 − 4t` for an explicit rank-2 operator.
   - `Padding`: zero padding.
   - `Interp`, `Block`: monotonicity in `t` (Lemma M2).
   - `Restrict`, `Copies`: subsets and relabelling of the copies.
   - `Reductions`: the Werner corollary from the hypothesis `CostaRico`.
2. **Soundness of moment certificates** (`NPT.Cert.soundness`):
   `WF C → IdFact C → (∀ t ∈ C.types, Z_t ⪰ 0) → EP (Fin C.k) C.d (1/2)`.
   It uses neither Haar measure nor Schur–Weyl duality (`DESIGN_soundness.md`). Ingredients:
   - **Lemma P** (`CondExp`): the Hilbert–Schmidt conditional expectation onto a unital *-subalgebra of matrices
     preserves positive semidefiniteness.
   - **Walled-Brauer closure** (`Brauer`, `BrauerTab`, `BrauerData`, `Glob`): for every cut `S` used, the span of the
     partially transposed word operators `V_w^{Γ_S}` is a *-algebra `A_S`. Products are certified by finite data
     (`GCert`) that the kernel checks with `decide +kernel`.
   - **Hilbert–Schmidt projection and intertwining** (`Proj`): projections exist and are unique. A linear map whose
     adjoint preserves the target subspaces commutes with the projections (`IsProj.map`).
   - **Semantics** (`Sem`, `SemLink`): the certificate functional `Λ_f(w)`, following the conventions of the record's
     verifier `ep3core.py`, and the identity fact `IdFact`; per word, `Λ` is a linear functional of the moment
     operators.
   - **Physical side.**
     - `Phys`: moment operators `X_f = |w_f⟩⟨w_f|` of `C = A Bᴴ`.
     - `NormalForm`: normal form `Aᴴ A = c·1`, `‖B‖ = ‖A‖`.
     - `PhysObj`: objective identity `Tr(O X_31) = ‖a‖⁴ 2^k q(1/2, C)`.
     - `PhysEq`: marginal identities.
     - `PhysStiefel`: Stiefel identities.
     - `PhysSym`: symmetry invariances.
   - **Symmetrization** (`SymDefs`, `Sym`): the projections of the symmetrized moments have orbit-constant
     coefficients (`sym_coeffs`), so the identity fact applies.
   - **Blocks** (`Rules`, `RuleData`, `BlockPos`, `BlkSign`): rule maps are Hilbert–Schmidt unitaries onto `A_S`.
     Lemma P on block algebras makes the projected blocks PSD, and each multiplier type contributes `≥ 0`.
   - **Equalities** (`EqMaps`, `EqLocal`, `EqData`, `EqInt`, `EqLink`): partial traces and the Stiefel contrast
     intertwine the projections, so the equality functionals vanish at the projected moments.
   - **Assembly** (`SoundPrep`, `Assembly`, `Soundness`): objective = Σ blocks + Σ equalities, hence `q ≥ 0`.
3. **Checkable conditions.**
   - `wfCheck C = true → WF C` (`WFCheck.wfCheck_sound`), which gives `soundness_of_check`.
   - The PSD checker `PBlock.check` with its soundness `check → PosSemidef` (`PsdCheck`, `PsdSound`).
4. **The certificates** (`EP3D3/*`, …, `EP3D8/*`), for each d:
   - the multiplier blocks, each checked by `decide +kernel` (`Psd*`), collected in `PsdAll.blocks_psd`
     (715 blocks at d = 3);
   - the certificate in `Sem` form (`SemData.cert`);
   - well-formedness `wf_cert : wfCheck cert = true` by `decide +kernel` (`WFd3` at d = 3, `EP3D<d>.WF` for d ≥ 4);
   - `EP3_d3_of_idFact` (module `EP3_d3`) and `EP3D<d>.EP_of_idFact` (module `EP3D<d>.EP`).
5. **Identity facts** (`Ident/*`, `EP3D<d>/K*`, `IdKChecks`, `WitK*`, `IdFact`): `idFact : IdFact cert` for each d,
   from kernel checks of the class sums modulo large primes, lifted by the Chinese remainder theorem
   (`README_kernel.md`). `EP3D<d>.EP3` and `EP3_d3` combine it with step 4.

## 3. Trusted base

- **Lean 4 kernel**, toolchain v4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`).
- **Mathlib**, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (`lake-manifest.json`).
- **Axioms:** `propext`, `Classical.choice` and `Quot.sound` only. `#print axioms` was run on every theorem of every
  module of this package (`AUDIT.md`). No source uses `sorry`, `admit` or `native_decide`; every finite computation is
  a `decide +kernel` check, evaluated inside the kernel, which adds no axioms.
- **Hypotheses that are not formalized:** Costa Rico's criterion (structure `CostaRico`; Lett. Math. Phys. 115:47
  (2025), Theorem 1). Quantum states and LOCC are not formalized.
- **Untrusted inputs:** the certificate data (rationals, rules, module matrices, product tables, moduli, offsets).
  They were generated by scripts that are not part of this package, and they enter only through propositions that
  the kernel checks, so they need no trust.
- **The semantics `Sem.Λ` need not match the record's verifier.** Agreement is not a trust assumption: the soundness
  theorem holds for whatever functional `Sem.Λ` defines. Agreement only decides whether `IdFact` is provable, and
  `IdFact` is proved in Lean.

## 4. Modules

Definitions, reductions and final statements:

| Module | Content |
|---|---|
| `NPT.Basic` | operators on copies, `ptrace`, `frobSq`, `q`, `RankLE2`, `EP` |
| `NPT.Product` | product operators, partial traces of products, product formula `q_tprod` |
| `NPT.Sharp` | the rank-2 operator `1₂ ⊗ \|0⟩⟨1\| ⊗ \|0⟩⟨1\|` with `q_3 = 2 − 4t` (sharpness at `t = 1/2`) |
| `NPT.Padding` | zero padding: `EP ι d t → EP ι d' t` for `d' ≤ d` |
| `NPT.Interp` | interpolation identity `q t C = Σ_S (1−t/g)^{\|Sᶜ\|} (t/g)^{\|S\|} Qpart g S C` |
| `NPT.Block` | spectator blocks; Lemma M2 (`EP_of_EP_sub`) |
| `NPT.Restrict` | `EP_restrict` (EP passes to any subset of copies) and `EP_mono_t` |
| `NPT.Reductions` | Costa Rico's criterion as hypothesis `CostaRico`; `undistillable_of_EP`, `werner_three_copy` |
| `NPT.Main` | conditional Werner corollaries at `d = 3` (3, 4, 5 copies), `EP3_of_le` |
| `NPT.Copies` | relabelling copies (`EP_equiv`); `EP2_of_EP3` |
| `NPT.Final` | `EP2_d3`, `EP3_d2`, `werner_three_copy_d3'` and their `*_of_idFact` forms |
| `NPT.Check`, `NPT.Axioms` | `#print axioms` for the elementary theorems and for the main theorems |
| `NPT` | imports the whole development |

Soundness (`NPT/Cert/`):

| Module | Content |
|---|---|
| `Brauer`, `BrauerTab`, `BrauerData` | selection operators; products certified by `GCert`; the 24 permutations and partially transposed operators `VG S p`; product certificates for the cuts used (`decide +kernel`) |
| `Lit` | raw-literal elaborators for generated data (untrusted; the kernel checks every statement about the terms) |
| `CondExp` | Lemma P |
| `Glob`, `Proj` | Kronecker products, global word operators `VW`, the *-algebras `A_S`, block algebras; Hilbert–Schmidt projections and intertwining |
| `Rules`, `RuleData` | entry-rule maps and their Hilbert–Schmidt unitarity; the entry rules of the EP_3 certificate |
| `PsdCheck`, `PsdSound` | kernel-checkable PSD test for exact multipliers (fixed-point `L D Lᵀ` plus diagonal dominance) and its soundness |
| `Sem`, `SemLink` | the semantic target (certificate data, `Λ_f(w)`, the word action `act`, `IdFact`); `Λ` per word as operator functionals |
| `Phys`, `NormalForm`, `PhysObj`, `PhysEq`, `PhysStiefel`, `PhysSym` | the physical moments and their identities and invariances |
| `BlockPos`, `BlkSign` | positivity of the projected multiplier blocks; sign of each multiplier type's contribution |
| `EqMaps`, `EqLocal`, `EqData`, `EqInt`, `EqLink` | partial traces and the Stiefel contrast as product-kernel maps; intertwining; the equality functionals |
| `SymDefs`, `Sym` | symmetry actions; `sym_coeffs` |
| `Assembly`, `SoundPrep`, `Soundness`, `WFCheck` | assembly; `WF` and `soundness`; computable `wfCheck` and `soundness_of_check` |

Certificates and identity facts:

| Module | Content |
|---|---|
| `Cert/EP3D<d>/Common`, `Psd*`, `PsdAll`, `SemData` | the certificate of dimension d: constants, multiplier blocks with PSD checks, `blocks_psd`, `cert` |
| `Cert/WFd3`, `Cert/EP3D<d>/WF` | `wf_cert` |
| `Cert/EP3_d3`, `Cert/EP3D<d>/EP` | `EP3_d3_of_idFact`, `EP_of_idFact` |
| `Cert/Ident/*` | the identity-fact checkers and their correctness (`README_kernel.md`, §2) |
| `Cert/EP3D<d>/K*`, `IdDefs`, `GrpF`, `IdKChecks`, `WitK*`, `Class*` | per-d data and kernel checks of the identity fact (moduli, tables, bounds, class-sum checks, offsets, assembly) |
| `Cert/EP3D<d>/IdFact` | `idFact : IdFact cert` |
| `Cert/EP3_d3`, `Cert/EP3D<d>/EP3` | `EP3_d3`, `EP3_d<d>` |
