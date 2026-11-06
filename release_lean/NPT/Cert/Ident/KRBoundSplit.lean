/-
NPT.Cert.Ident.KRBoundSplit — two more crude word-value bounds (for the kernel route at d ≥ 4).

* `partsF_le_crudeBS`: the bound of `KRBound` in sum form, `|partsF (famParts C zmul f gs zs za eqT) w| ≤ crudeBS …`,
  a sum over the three kinds of parts of `term count × largest coefficient × largest value`:
  rule groups `NG · (den3 · max|Zq|) · (max|W|² · max|J|^8)` (`NG` as in `crudeN`), objective (family 0)
  `1 · 2 Lden · (max|zs|³ · max|za|)`, equality parts `eqCount · max|sign · den3 · λ| · (eqB(d)³ · eqB(2))`.
  It is about 25 bits below `crudeB` at d = 4..8.
* `partsF_split_le`: a declaration of a split mod-`p` check (`KRSplit`) holds the rule groups `gs` (any sub-list of a
  family's groups), with or without `otherPartsModB` (objective and λ-box equality parts); its word values are bounded
  by `crudeBMod C f gs zs za P` (`KRBoundMod`) for `0 < p ≤ P`.
-/
import NPT.Cert.Ident.KRBoundMod
import NPT.Cert.Ident.KRSplit

open BigOperators Finset NPT.Cert.Sem NPT.Brauer NPT.Cert.KR

namespace NPT.Cert.Ident

noncomputable section

/-! ### The sum form of the crude bound -/

/-- **Crude bound, sum form**: rule groups + objective + equality parts, each
`term count × largest coefficient × largest value`. -/
def crudeBS (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ) : ℕ :=
  (gs.map fun G => (itemsOf G.tree).length).sum *
      (nbMax C * nbMax C * (dimMax C * dimMax C * (nMax C ^ 4 * nMax C ^ 4)) ^ 4) * (den3 C.d * zqBmax C zmul) *
      (maxWall C ^ 2 * maxJall C ^ 8) +
    (if f = 0 then 1 else 0) * (2 * C.Lden * (tabMax zs ^ 3 * tabMax za)) +
    eqCount C f * (eqCoefMax C f * (eqB C C.d ^ 3 * eqB C 2))

/-- **Crude a-priori bound on the word values, sum form**, for every `eqT` bounded by `eqB` (e.g. `eqLocF C`). -/
theorem partsF_le_crudeBS (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (heqT : ∀ sp n p o, |eqT sp n p o| ≤ (eqB C n : ℤ))
    (w0 w1 w2 w3 : ℕ) (hw0 : w0 < 24) (hw1 : w1 < 24) (hw2 : w2 < 24) (hw3 : w3 < 24) :
    |partsF (famParts C zmul f gs zs za eqT) w0 w1 w2 w3| ≤ (crudeBS C zmul f gs zs za : ℤ) := by
  refine le_trans (partsF_abs _ (famParts_rows C zmul f gs zs za eqT) w0 w1 w2 w3 hw0 hw1 hw2 hw3) ?_
  have hgr := groups_bound_le C zmul gs
  have hobj : boundTree (rank1Spec (objE zs za) (2 * C.Lden)) rank1Tree ≤
      2 * C.Lden * (tabMax zs ^ 3 * tabMax za) := by
    have hz : ∀ l < 3, ∀ p, (objE zs za l p).natAbs ≤ tabMax zs := by
      intro l hl p; simp only [objE, ite_eq_left hl]; exact le_tabMax zs p
    have ha : ∀ p, (objE zs za 3 p).natAbs ≤ tabMax za := by
      intro p; simp only [objE]; exact le_tabMax za p
    refine le_trans (boundTree_rank1_le _ _ _ _ _ _ (hz 0 (by norm_num)) (hz 1 (by norm_num)) (hz 2 (by norm_num)) ha) ?_
    have hc : ((2 * C.Lden : ℕ) : ℤ).natAbs = 2 * C.Lden := Int.natAbs_natCast _
    push_cast at hc
    rw [show ((2 : ℤ) * (C.Lden : ℤ)).natAbs = 2 * C.Lden by simpa using hc]
    calc 2 * C.Lden * (tabMax zs * tabMax zs * tabMax zs * tabMax za) = 2 * C.Lden * (tabMax zs ^ 3 * tabMax za) := by ring
      _ ≤ 2 * C.Lden * (tabMax zs ^ 3 * tabMax za) := le_rfl
  have heq := eq_bound_le C f eqT heqT
  have hnat : partsBound (famParts C zmul f gs zs za eqT) ≤ crudeBS C zmul f gs zs za := by
    unfold partsBound famParts
    simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def]
    have hsum : (if f = 0 then [rank1Part (objE zs za) (2 * C.Lden)] else []).map (fun P => boundTree P.S P.tree) =
        if f = 0 then [boundTree (rank1Spec (objE zs za) (2 * C.Lden)) rank1Tree] else [] := by
      split_ifs <;> rfl
    rw [hsum]
    have hobj' : (if f = 0 then [boundTree (rank1Spec (objE zs za) (2 * C.Lden)) rank1Tree] else []).sum ≤
        (if f = 0 then 1 else 0) * (2 * C.Lden * (tabMax zs ^ 3 * tabMax za)) := by
      split_ifs <;> simp [hobj]
    unfold crudeBS
    exact add_le_add (add_le_add hgr hobj') heq
  exact_mod_cast hnat

/-- The sum-form bound for the certificate's own equality maps (`eqT = eqLocF C`). -/
theorem partsF_le_crudeBS_eqLocF (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (w0 w1 w2 w3 : ℕ) (hw0 : w0 < 24) (hw1 : w1 < 24) (hw2 : w2 < 24) (hw3 : w3 < 24) :
    |partsF (famParts C zmul f gs zs za (eqLocF C)) w0 w1 w2 w3| ≤ (crudeBS C zmul f gs zs za : ℤ) :=
  partsF_le_crudeBS C zmul f gs zs za (eqLocF C) (eqLocF_le C) w0 w1 w2 w3 hw0 hw1 hw2 hw3

/-! ### Split declarations -/

lemma gpartsMod_rows (p zmul : ℕ) (C : CertD) (gs : List GrpF) :
    ∀ P ∈ gpartsMod p zmul C gs, ∀ m, (P.S.rows m).length = 24 := by
  intro P hP m
  simp only [gpartsMod, List.mem_map] at hP
  obtain ⟨G, _, rfl⟩ := hP
  exact localRowsF_length _ _ _

/-- The rule-group parts mod `p` alone: the first summand of `crudeBMod`. -/
lemma partsBound_gpartsMod_le (p zmul : ℕ) (C : CertD) (gs : List GrpF) (P : ℕ) (hp : 0 < p) (hpP : p ≤ P) :
    partsBound (gpartsMod p zmul C gs) ≤ (gs.map fun G => (itemsOf G.tree).length).sum *
      (nbMax C * nbMax C * (dimMax C * dimMax C * (nMax C ^ 4 * nMax C ^ 4)) ^ 4) * (den3 C.d * P) *
      (maxWall C ^ 2 * maxJall C ^ 8) := by
  unfold partsBound gpartsMod
  rw [List.map_map]
  refine le_trans (groups_bound_le (certMod p zmul C) 1 gs) ?_
  rw [nbMax_certMod]
  exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (zqBmax_certMod_le C p zmul P hp hpP))) le_rfl

/-- The groups plus `otherPartsModB` have the word values of `famPartsMod` (λ-box = rank-one equality parts). -/
lemma partsF_gpartsMod_others (p zmul : ℕ) (C : CertD) (f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (w0 w1 w2 w3 : ℕ) (h0 : w0 < 24) (h1 : w1 < 24) (h2 : w2 < 24)
    (h3 : w3 < 24) :
    partsF (gpartsMod p zmul C gs ++ otherPartsModB p zmul C f zs za eqT) w0 w1 w2 w3 =
      partsF (famPartsMod p zmul C f gs zs za eqT) w0 w1 w2 w3 := by
  have he : partsF (eqBoxPartsF (certModR p zmul C) f eqT) w0 w1 w2 w3 =
      partsF (eqPartsF (certMod p zmul C) f eqT) w0 w1 w2 w3 := by
    rw [certModR_eq]; exact partsF_eqBox (certMod p zmul C) f eqT ⟨w0, h0⟩ ⟨w1, h1⟩ ⟨w2, h2⟩ ⟨w3, h3⟩
  unfold famPartsMod otherPartsModB gpartsMod
  simp only [partsF_append]
  rw [he]
  ring

/-- **Word bound of one split declaration**: the rule groups `gs` (any sub-list of a family's groups), with or without
`otherPartsModB`, have word values bounded by `crudeBMod C f gs zs za P` for `0 < p ≤ P`. -/
theorem partsF_split_le (p zmul : ℕ) (C : CertD) (f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (heqT : ∀ sp n p o, |eqT sp n p o| ≤ (eqB C n : ℤ)) (P : ℕ)
    (hp : 0 < p) (hpP : p ≤ P) (others : List Part)
    (hothers : others = [] ∨ others = otherPartsModB p zmul C f zs za eqT)
    (w0 w1 w2 w3 : ℕ) (hw0 : w0 < 24) (hw1 : w1 < 24) (hw2 : w2 < 24) (hw3 : w3 < 24) :
    |partsF (gpartsMod p zmul C gs ++ others) w0 w1 w2 w3| ≤ (crudeBMod C f gs zs za P : ℤ) := by
  rcases hothers with rfl | rfl
  · rw [List.append_nil]
    refine le_trans (partsF_abs _ (gpartsMod_rows p zmul C gs) w0 w1 w2 w3 hw0 hw1 hw2 hw3) ?_
    have h := partsBound_gpartsMod_le p zmul C gs P hp hpP
    have h' : partsBound (gpartsMod p zmul C gs) ≤ crudeBMod C f gs zs za P := by
      unfold crudeBMod; omega
    exact_mod_cast h'
  · rw [partsF_gpartsMod_others p zmul C f gs zs za eqT w0 w1 w2 w3 hw0 hw1 hw2 hw3]
    exact partsF_le_crudeBMod p zmul C f gs zs za eqT heqT P hp hpP w0 w1 w2 w3 hw0 hw1 hw2 hw3

/-- `partsF_split_le` for the certificate's own equality maps (`eqT = eqLocF C`). -/
theorem partsF_split_le_eqLocF (p zmul : ℕ) (C : CertD) (f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ) (P : ℕ)
    (hp : 0 < p) (hpP : p ≤ P) (others : List Part)
    (hothers : others = [] ∨ others = otherPartsModB p zmul C f zs za (eqLocF C))
    (w0 w1 w2 w3 : ℕ) (hw0 : w0 < 24) (hw1 : w1 < 24) (hw2 : w2 < 24) (hw3 : w3 < 24) :
    |partsF (gpartsMod p zmul C gs ++ others) w0 w1 w2 w3| ≤ (crudeBMod C f gs zs za P : ℤ) :=
  partsF_split_le p zmul C f gs zs za (eqLocF C) (eqLocF_le C) P hp hpP others hothers w0 w1 w2 w3 hw0 hw1 hw2 hw3

end

end NPT.Cert.Ident
