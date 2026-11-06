# Statements

The theorem chain of the four-copy package, top down, with the exact Lean statements. "Standard axioms" means
`propext`, `Classical.choice`, `Quot.sound`. `EP`, `q`, `CostaRico` and the certificate semantics (`CertD`, `WF`,
`blkZ`, `Zmat`, …) come from the three-copy package of the record; the files outside `NPT/K4/` are byte-identical to
it.

## 1. Main theorems

```lean
-- NPT/K4/Final4979.lean
theorem NPT.K4.D3T4979.EP_K4_4979 : NPT.EP (Fin 4) 3 (4979 / 10000)

-- NPT/K4/Werner4.lean
theorem NPT.K4.werner_four_copy_4979 {D : ℕ → ℕ → ℝ → Prop} (hCR : NPT.CostaRico D) {α : ℝ}
    (hα : -(4979 / 10000 : ℝ) ≤ α) (h1 : α ≤ 1) : ¬ D 4 3 α

-- NPT/K4/Final497.lean
theorem NPT.K4.D3T497.EP_K4_497 : NPT.EP (Fin 4) 3 (497 / 1000)
```

`NPT.EP ι d t` (module `NPT.Basic`): `∀ C : Op ι d, RankLE2 C → 0 ≤ q t C`, with
`q t C = ∑ J : Finset ι, (-t) ^ J.card * frobSq (ptrace J C)`.

Axioms: `EP_K4_4979` and `werner_four_copy_4979` depend on the standard axioms and the 120 axioms
`NPT.K4.Route.T4979.sliceOK{f}_{j}._native.native_decide.ax_1` (f = 0, …, 4; j = 0, …, 23); `EP_K4_497` on the standard
axioms and the 72 axioms `NPT.K4.Route.T497.sliceOK{f}_{j}._native.native_decide.ax_1` (f = 0, 1, 2; j = 0, …, 23).
Every theorem of sections 2–5 depends on the standard axioms only.

## 2. Soundness with residuals

The slack functional of a certificate `C` (family codes `f`; `w` a word, one letter per leg):

```lean
-- NPT/K4/SemS.lean
def NPT.K4.ΛS (C : CertD) (α β : ℕ) (nu : ℚ) (f : ℕ) (w : Fin (C.k + 1) → Fin 24) : ℚ :=
  (if f = 0 then objT C α β w - nu * trW C w / (2 * C.d ^ C.k) ^ 4 else 0)
  - (C.types.map fun t => ∑ r ∈ range t.nrows, ∑ s ∈ range t.nrows,
        if ((t.rules.getD r []).getD s default).fam = f then C.blk t r s w else 0).sum
  - (C.eqs.map fun g => (g.parts.map fun P =>
        if P.fam = f then (P.sign : ℚ) * C.eqVal g P w else 0).sum).sum
```

The identity fact with residuals (three families; `IdFactS5` in `NPT/K4/Sem5.lean` is the same with `f < 5` and the
symmetry test `inG5`):

```lean
-- NPT/K4/SemS.lean
structure NPT.K4.IdFactS (C : CertD) (α β : ℕ) (nu : ℚ) where
  cls : ℕ → (Fin (C.k + 1) → Fin 24) → ℕ
  rep : ℕ → ℕ → (Fin (C.k + 1) → Fin 24)
  wit : ℕ → (Fin (C.k + 1) → Fin 24) → Fin 24 × Fin 24 × (Fin C.k → Fin C.k) × Bool
  hG : ∀ f < 3, ∀ w, inG f (wit f w).1 = true ∧ inG f (wit f w).2.1 = true
  hσ : ∀ f < 3, ∀ w, Function.Bijective (wit f w).2.2.1
  hrep : ∀ f < 3, ∀ w, act (wit f w).1 (wit f w).2.1 (wit f w).2.2.1 (wit f w).2.2.2 w = rep f (cls f w)
  res : ℕ → ℕ → ℚ
  codes : ℕ → Finset ℕ
  hcodes : ∀ f < 3, ∀ w, cls f w ∈ codes f
  hsum : ∀ f < 3, ∀ w₀, ∑ w ∈ univ.filter (fun w => cls f w = cls f w₀), ΛS C α β nu f w = res f (cls f w₀)
```

```lean
-- NPT/K4/SoundS.lean
theorem NPT.K4.soundness_slack (C : CertD) [NeZero C.d] (hd3 : C.d = 3) (α β : ℕ) (hα : 0 < α) (nu : ℚ)
    (hwf : WF C) (hid : IdFactS C α β nu)
    (hpsd : ∀ t ∈ C.types, ((C.blkZ t).Zmat C.Lden).PosSemidef)
    (hslack : (2 * (C.d : ℚ) ^ C.k) ^ 4 * Kq C.k *
      ∑ f ∈ Finset.range 3, ∑ j ∈ hid.codes f, |hid.res f j| ≤ nu) :
    NPT.EP (Fin C.k) C.d ((β : ℝ) / α)

-- NPT/K4/SoundS5.lean
theorem NPT.K4.soundness_slack5 (C : CertD) [NeZero C.d] (hd3 : C.d = 3) (α β : ℕ) (hα : 0 < α) (nu : ℚ)
    (hwf : WF5 C) (hid : IdFactS5 C α β nu)
    (hpsd : ∀ t ∈ C.types, ((C.blkZ t).Zmat C.Lden).PosSemidef)
    (hslack : (2 * (C.d : ℚ) ^ C.k) ^ 4 * Kq C.k *
      ∑ f ∈ Finset.range 5, ∑ j ∈ hid.codes f, |hid.res f j| ≤ nu) :
    NPT.EP (Fin C.k) C.d ((β : ℝ) / α)

-- NPT/K4/CRT.lean: the slack hypothesis from one integer inequality, residuals res = Rint / D
theorem NPT.K4.hslack_of_int (k d D : ℕ) (hD : 0 < D) (nuNum : ℤ) (nuDen : ℕ) (hnuDen : 0 < nuDen)
    (codes : ℕ → Finset ℕ) (Rint : ℕ → ℕ → ℤ) (Ssum : ℕ)
    (hS : ∑ f ∈ Finset.range 3, ∑ j ∈ codes f, |Rint f j| ≤ Ssum)
    (hchk : (((2 * d ^ k) ^ 4 * 786 ^ k * 496 * Ssum * nuDen : ℕ) : ℤ) ≤ nuNum * ((D * (8640 ^ k * 2880) : ℕ) : ℤ)) :
    (2 * (d : ℚ) ^ k) ^ 4 * Kq k * ∑ f ∈ Finset.range 3, ∑ j ∈ codes f, |(Rint f j : ℚ) / D| ≤
      (nuNum : ℚ) / nuDen
```

`WF5` and `wfCheck5_sound` (`NPT/K4/WF5.lean`, `NPT/K4/WFCheck5.lean`) extend the three-copy well-formedness to the
five-family entry rules (`NPT/K4/Rule5.lean`, `NPT/K4/RuleData5.lean`).

## 3. Assembly from the slice checks

`NPT.K4.D3T497.ep497_of_slicesB` (`NPT/K4/EP497.lean`) proves `NPT.EP (Fin 4) 3 (497 / 1000)` and
`NPT.K4.D3T4979.ep4979_of_slicesB` (`NPT/K4/EP4979.lean`) proves `NPT.EP (Fin 4) 3 (4979 / 10000)` from the route data
and checks below (three families for 497/1000, five for 4979/10000; `D = 2^224·1000^4·162^4` resp.
`D5 = 2^254·10000^4·162^4`). The hypotheses of `ep4979_of_slicesB`:

```lean
theorem NPT.K4.D3T4979.ep4979_of_slicesB (gsF : ℕ → List GrpF) (t0F : ℕ → AT) (offsF : ℕ → ℕ → List (ℕ × ℤ))
    (b E0 : ℕ) (cG cO cT cE : ℤ)
    (hG : ∀ f < 5, ∀ G ∈ gsF f, Route.grpOK5 cert E0 G = true)
    (hperm : ∀ f < 5, ((gsF f).flatMap fun G => itemsOf G.tree).Perm (allItems cert f))
    (hcG : (cG : ℚ) * 2 ^ E0 = -(D5 : ℚ))
    (hcO : (cO : ℚ) = (D5 : ℚ) / ((10000 : ℚ) ^ 4 * (2 * 3 ^ 4) ^ 4))
    (hcT : (cT : ℚ) = -((D5 : ℚ) * (((nuNum : ℤ) : ℚ) / nuDen) / (2 * 3 ^ 4) ^ 4))
    (hcE : (cE : ℚ) = (D5 : ℚ) / ((2 * Lden : ℕ) : ℚ))
    (hkind : ∀ g ∈ eqs, ∀ P ∈ g.parts, ∀ l : Fin (4 + 1),
      (P.specs.getD l.val default).kind = 0 ∨ nf 4 3 l = 2)
    (hchk : ∀ f < 5, ∀ j : Fin 24, Route.sliceCheck b (Route.parts5B cert 10000 4979 cG cO cT cE f (gsF f) j)
      ((slicesL5 f).getD j.val []) (Route.tOff (t0F f) (offsF f j.val)) = true)
    (reps : ℕ → List ℕ) (resL : ℕ → List ℤ)
    (hkeys : ∀ f < 5, ∀ e ∈ (t0F f).leaves, e.1 ∈ reps f)
    (hoff : ∀ f < 5, ∀ c ∈ reps f,
      ∑ j : Fin 24, Route.offAt (Route.tOff (t0F f) (offsF f j.val)) c = -RintOf (reps f) (resL f) c)
    (Ssum : ℕ)
    (hSsum : ((resL 0).map Int.natAbs).sum + ((resL 1).map Int.natAbs).sum + ((resL 2).map Int.natAbs).sum +
      ((resL 3).map Int.natAbs).sum + ((resL 4).map Int.natAbs).sum ≤ Ssum)
    (hchk2 : (((2 * 3 ^ 4) ^ 4 * 786 ^ 4 * 496 * Ssum * nuDen : ℕ) : ℤ) ≤
      (nuNum : ℤ) * ((D5 * (8640 ^ 4 * 2880) : ℕ) : ℤ)) :
    NPT.EP (Fin 4) 3 (4979 / 10000)
```

`ep497_of_slicesB` has the same form with `f < 3`, `D`, `1000`, `497` and `slicesL`. Inside, the data facts of
section 4 discharge well-formedness, positive semidefiniteness and the class structure; the slice lists `slicesL`,
`slicesL5` are the class lists of the class data read slice by slice (`NPT.K4.ClsSlicesW`, `NPT.K4.ClsLen*`).

## 4. Route soundness

```lean
-- NPT/K4/Route/SliceSound.lean: one slice check, for a key c of its accumulator tree
theorem NPT.K4.Route.sliceCheck_sound_key (b : Nat) (ps : List Part) (cls : List Nat) (t0 : AT)
    (h : sliceCheck b ps cls t0 = true) (hS : ∀ P ∈ ps, ∀ m, (P.S.rows m).length = 24)
    (c : Nat) (hc : (t0.leaves.getD (t0.tgt c) dLeaf).1 = c) :
    ∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = c then
      partsF ps (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0) = - offAt t0 c

-- NPT/K4/Route/OffsK.lean: the offset sums from four kernel checks
theorem NPT.K4.Route.hoff_of_checks (t0 : AT) (reps : List Nat) (resL : List Int) (offsL : List (List (Nat × Int)))
    (h24 : offsL.length = 24) (hsort : sortedLt reps = true)
    (hkeys : (routeL (reps.map fun _ => SInt.zero) reps t0).leaves.all (fun e => e.2.2) = true)
    (hzero : t0.leaves.all (fun e => e.2.1.mag == 0) = true)
    (hK : hoffK reps resL offsL = true) :
    ∀ c ∈ reps, ∑ j : Fin 24, offAt (tOff t0 (offsL.getD j.val [])) c = -RintOfR reps resL c
```

`NPT.K4.Route.ΛS_partsF5B` (`NPT/K4/Route/HsumSB.lean`) identifies `D · ΛS` at a word with the integer value of the
slice parts `parts5B` (rule-group parts, rank-one objective and trace parts, equality parts as boxes), and
`NPT.K4.Route.hsum_of_slicesB` turns the 24 slice checks of a family with the offsets into its class sums.

## 5. Data facts (kernel-checked)

For each certificate (`NPT.K4.D3T497`, `NPT.K4.D3T4979`):
- `wf_cert : NPT.Cert.wfCheck cert = true` (497/1000), `wf5_cert : NPT.K4.wfCheck5 cert = true` (4979/10000);
- `blocks_psd : ∀ b ∈ blocks, (b.Zmat Lden).PosSemidef` (3816 resp. 4893 blocks);
- `types_ok : cert.types.all (NPT.K4.typeOK cert BW sZ NB DM) = true` and `maxJ_ok : NPT.Cert.Ident.maxJall cert ≤ BJ`;
- class structure: `NPT.K4.Classes.witCheck5_all`, `hG5`, `hσ5`, `hrep5`, `hcodes5` (three families) and `hG5'`, `hσ5'`,
  `hrep5'`, `hcodes5'` (five families): every word is mapped to its class representative by a checked symmetry
  (families 3, 4: one shared S₄ class list, checked by `witCheckS_f3`, `NPT/K4/Classes/WitK3.lean`, through
  `NPT.K4.WitnessS4`);
- rule groups: `grpOK5K_f<f> : rgs<f>.all (grpOK5 cert E0) = true`, `itemsPerm5K_f<f>` (the groups' items are a
  permutation of the family's multiplier entries) and `eqKinds5K` (`NPT/K4/DataK497.lean`, `NPT/K4/DataK4979.lean`,
  through `NPT.K4.Route.getDChunks_eq`, `grpOK5_L`, `allItems_eq_L`, `msortF_perm`, `items_perm_of_sort` of
  `NPT/K4/DataK.lean`);
- keys: `t0keys<f> : t0_<f>.leaves.map Prod.fst = reps<f>` (`NPT/K4/Keys497.lean`, `NPT/K4/Keys4979.lean`);
- offsets: `hoffK<f>_all` (`NPT/K4/Route/T497/HoffK<f>.lean`, `NPT/K4/Route/T4979/HoffK<f>.lean`, by
  `hoff_of_checks`);
- the integer slack inequality (hypothesis `hchk2`, discharged by `decide +kernel` in `NPT/K4/Final497.lean` and
  `NPT/K4/Final4979.lean`).

## 6. Facts evaluated by `native_decide`

The slice checks, one module each (`NPT/K4/Route/T497/Chk<f>_<j>.lean`, `NPT/K4/Route/T4979/Chk<f>_<j>.lean`):

```lean
theorem NPT.K4.Route.T497.sliceOK<f>_<j> : sliceCheck bP (parts5B cert 1000 497 cG cO cT cE <f> rgs<f> ⟨<j>, by decide⟩)
    cls<f>_<j> (tOff t0_<f> offs<f>_<j>) = true := by native_decide        -- f = 0, 1, 2; j = 0, …, 23

theorem NPT.K4.Route.T4979.sliceOK<f>_<j> : sliceCheck bP (parts5B cert 10000 4979 cG cO cT cE <f> rgs<f> ⟨<j>, by decide⟩)
    cls<g>_<j> (tOff t0_<f> offs<f>_<j>) = true := by native_decide        -- f = 0, …, 4; j = 0, …, 23
```

For 4979/10000 the class list of families 3 and 4 is the shared list `cls3_<j>` (`g = 3`); otherwise `g = f`. Each
check adds the axiom `sliceOK<f>_<j>._native.native_decide.ax_1`. These are the only `native_decide` uses in the import
closure of the main theorems (audit axiom scan).
