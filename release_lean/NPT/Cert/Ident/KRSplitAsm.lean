/-
NPT.Cert.Ident.KRSplitAsm — the hypothesis `hsplit` of `KRSplit.hsum_of_checks_split` for one modulus, from the data of
a split layout: declarations `pre` with no other parts, then a last declaration `(gL, otherPartsModB …, oL)`,
whose rule groups concatenate to the family's groups. Besides the checks and the offsets, only the table facts of the
whole family and ONE bound `crudeBMod C f gs zs za P < 2^(b−1)` for the whole family are needed (`hsplit_last`):
every declaration's word values are bounded through `partsF_split_le` and the monotonicity of `crudeBMod`.
-/
import NPT.Cert.Ident.KRBoundSplit

open BigOperators Finset NPT.Cert.Sem NPT.Brauer NPT.Cert.KR

namespace NPT.Cert.Ident

noncomputable section

/-- The number of items of a list of rule groups. -/
lemma itemsSum_append (A B : List GrpF) : ((A ++ B).map fun G => (itemsOf G.tree).length).sum =
    (A.map fun G => (itemsOf G.tree).length).sum + (B.map fun G => (itemsOf G.tree).length).sum := by
  rw [List.map_append, List.sum_append]

lemma crudeBMod_mono (C : CertD) (f : ℕ) (gs gs' : List GrpF) (zs za : Fin 24 → ℤ) (P : ℕ)
    (h : (gs'.map fun G => (itemsOf G.tree).length).sum ≤ (gs.map fun G => (itemsOf G.tree).length).sum) :
    crudeBMod C f gs' zs za P ≤ crudeBMod C f gs zs za P := by
  unfold crudeBMod
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ h))) _) _

lemma itemsSum_le_flatten {X : Type} (pre : List (List (GrpF × X) × List Part × List ℕ))
    (s : List (GrpF × X) × List Part × List ℕ) (hs : s ∈ pre) :
    ((s.1.map Prod.fst).map fun G => (itemsOf G.tree).length).sum ≤
      ((((pre.map Prod.fst).flatten).map Prod.fst).map fun G => (itemsOf G.tree).length).sum := by
  induction pre with
  | nil => simp at hs
  | cons t pre ih =>
    rw [List.map_cons, List.flatten_cons, List.map_append, itemsSum_append]
    rcases List.mem_cons.1 hs with rfl | hs
    · exact Nat.le_add_right _ _
    · exact le_trans (ih hs) (Nat.le_add_left _ _)

lemma partsF_famPartsMod_append (p zmul : ℕ) (C : CertD) (f : ℕ) (A B : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (w0 w1 w2 w3 : ℕ) :
    partsF (famPartsMod p zmul C f (A ++ B) zs za eqT) w0 w1 w2 w3 =
      partsF (gpartsMod p zmul C A) w0 w1 w2 w3 + partsF (famPartsMod p zmul C f B zs za eqT) w0 w1 w2 w3 := by
  unfold famPartsMod gpartsMod
  simp only [List.map_append, partsF_append]
  ring

/-- The declarations of the layout add up to `famPartsMod` of the concatenated groups. -/
theorem hall_last (p zmul : ℕ) (C : CertD) (f : ℕ) (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ)
    (gL : List (GrpF × List (List (List SInt)))) (oL : List ℕ) (w0 w1 w2 w3 : ℕ) (h0 : w0 < 24) (h1 : w1 < 24)
    (h2 : w2 < 24) (h3 : w3 < 24) :
    ∀ (pre : List (List (GrpF × List (List (List SInt))) × List Part × List ℕ)), (∀ s ∈ pre, s.2.1 = []) →
    ((pre ++ [(gL, otherPartsModB p zmul C f zs za eqT, oL)]).map fun s =>
        partsF (gpartsMod p zmul C (s.1.map Prod.fst) ++ s.2.1) w0 w1 w2 w3).sum =
      partsF (famPartsMod p zmul C f (((pre.map Prod.fst).flatten ++ gL).map Prod.fst) zs za eqT) w0 w1 w2 w3
  | [], _ => by
    simp only [List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.flatten_nil]
    exact partsF_gpartsMod_others p zmul C f _ zs za eqT w0 w1 w2 w3 h0 h1 h2 h3
  | s :: pre, hpre => by
    have hs : s.2.1 = [] := hpre s (by simp)
    have ih := hall_last p zmul C f zs za eqT gL oL w0 w1 w2 w3 h0 h1 h2 h3 pre
      (fun s' hs' => hpre s' (by simp [hs']))
    have hR : (((s :: pre).map Prod.fst).flatten ++ gL).map Prod.fst =
        s.1.map Prod.fst ++ (((pre.map Prod.fst).flatten ++ gL).map Prod.fst) := by
      rw [List.map_cons, List.flatten_cons, List.append_assoc, List.map_append]
    rw [hR, partsF_famPartsMod_append, ← ih, List.cons_append, List.map_cons, List.sum_cons, hs, List.append_nil]

lemma hO_last (p zmul : ℕ) (C : CertD) (f : ℕ) (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ)
    (pre : List (List (GrpF × List (List (List SInt))) × List Part × List ℕ)) (hpre : ∀ s ∈ pre, s.2.1 = [])
    (gL : List (GrpF × List (List (List SInt)))) (oL : List ℕ) :
    ∀ s ∈ pre ++ [(gL, otherPartsModB p zmul C f zs za eqT, oL)], ∀ P ∈ s.2.1, ∀ m, (P.S.rows m).length = 24 := by
  intro s hs P hP m
  rcases List.mem_append.1 hs with hs | hs
  · rw [hpre s hs] at hP; simp at hP
  · rw [List.mem_singleton] at hs; subst hs
    exact otherPartsModB_rows p zmul C f zs za eqT P hP m

lemma htab_last {Q : GrpF × List (List (List SInt)) → Prop}
    (pre : List (List (GrpF × List (List (List SInt))) × List Part × List ℕ))
    (gL : List (GrpF × List (List (List SInt)))) (others : List Part) (oL : List ℕ)
    (h : ∀ Gt ∈ (pre.map Prod.fst).flatten ++ gL, Q Gt) :
    ∀ s ∈ pre ++ [(gL, others, oL)], ∀ Gt ∈ s.1, Q Gt := by
  intro s hs Gt hGt
  rcases List.mem_append.1 hs with hs | hs
  · exact h Gt (List.mem_append_left _ (List.mem_flatten.2 ⟨s.1, List.mem_map.2 ⟨s, hs, rfl⟩, hGt⟩))
  · rw [List.mem_singleton] at hs; subst hs
    exact h Gt (List.mem_append_right _ hGt)

/-- Every declaration's word values are below `2^(b−1)`, from one bound for the whole family. -/
lemma hF_last (p zmul : ℕ) (C : CertD) (f : ℕ) (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ)
    (heqT : ∀ sp n p o, |eqT sp n p o| ≤ (eqB C n : ℤ)) (P b : ℕ) (hp : 0 < p) (hpP : p ≤ P)
    (pre : List (List (GrpF × List (List (List SInt))) × List Part × List ℕ)) (hpre : ∀ s ∈ pre, s.2.1 = [])
    (gL : List (GrpF × List (List (List SInt)))) (oL : List ℕ)
    (hbnd : crudeBMod C f (((pre.map Prod.fst).flatten ++ gL).map Prod.fst) zs za P < 2 ^ (b - 1)) :
    ∀ s ∈ pre ++ [(gL, otherPartsModB p zmul C f zs za eqT, oL)], ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 →
      w3 < 24 → |partsF (gpartsMod p zmul C (s.1.map Prod.fst) ++ s.2.1) w0 w1 w2 w3| < 2 ^ (b - 1) := by
  intro s hs w0 w1 w2 w3 h0 h1 h2 h3
  have hoth : s.2.1 = [] ∨ s.2.1 = otherPartsModB p zmul C f zs za eqT := by
    rcases List.mem_append.1 hs with hs | hs
    · exact Or.inl (hpre s hs)
    · rw [List.mem_singleton] at hs; subst hs; exact Or.inr rfl
  have hle : crudeBMod C f (s.1.map Prod.fst) zs za P ≤
      crudeBMod C f (((pre.map Prod.fst).flatten ++ gL).map Prod.fst) zs za P := by
    apply crudeBMod_mono
    rw [List.map_append, itemsSum_append]
    rcases List.mem_append.1 hs with hs | hs
    · exact le_trans (itemsSum_le_flatten pre s hs) (Nat.le_add_right _ _)
    · rw [List.mem_singleton] at hs; subst hs; exact Nat.le_add_left _ _
  have hb := partsF_split_le p zmul C f (s.1.map Prod.fst) zs za eqT heqT P hp hpP s.2.1 hoth w0 w1 w2 w3 h0 h1 h2 h3
  calc |partsF (gpartsMod p zmul C (s.1.map Prod.fst) ++ s.2.1) w0 w1 w2 w3|
      ≤ (crudeBMod C f (s.1.map Prod.fst) zs za P : ℤ) := hb
    _ ≤ (crudeBMod C f (((pre.map Prod.fst).flatten ++ gL).map Prod.fst) zs za P : ℤ) := by exact_mod_cast hle
    _ < 2 ^ (b - 1) := by exact_mod_cast hbnd

/-- The offsets hypothesis of `hsplit_last` from a pointwise statement over the declarations' offset lists (the form of
`offsOK`, `KROffs.offsZero_sound`). -/
lemma hoff_of_offs (p n : ℕ) (sp : List (List (GrpF × List (List (List SInt))) × List Part × List ℕ))
    (h : ∀ j, ((sp.map fun s => s.2.2).map fun o => o.getD j 0).sum % p = 0) :
    ∀ i < n, (sp.map fun s => s.2.2.getD i 0).sum % p = 0 := by
  intro i _
  have hi := h i
  rw [List.map_map] at hi
  exact hi

/-- **`hsplit` of `hsum_of_checks_split` for one modulus**, for the layout `pre ++ [(gL, otherPartsModB …, oL)]`
(no other parts in `pre`; the groups concatenate to `gs`): from the family's table facts, one word bound
`crudeBMod C f gs zs za P < 2^(b−1)` (`0 < p ≤ P`), the declarations' checks and the offsets. -/
theorem hsplit_last (p zmul : ℕ) (C : CertD) (f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (heqT : ∀ sp n p o, |eqT sp n p o| ≤ (eqB C n : ℤ)) (b P : ℕ)
    (hp : 0 < p) (hpP : p ≤ P) (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (cls : List ℕ) (t0 : AT)
    (pre : List (List (GrpF × List (List (List SInt))) × List Part × List ℕ)) (hpre : ∀ s ∈ pre, s.2.1 = [])
    (gL : List (GrpF × List (List (List SInt)))) (oL : List ℕ)
    (hcat : ((pre.map Prod.fst).flatten ++ gL).map Prod.fst = gs)
    (htab : ∀ Gt ∈ (pre.map Prod.fst).flatten ++ gL,
      Gt.2 = mkTab C Gt.1.kpos Gt.1.lpos (supps 2 Gt.1.kpos Gt.1.lpos) (supps 3 Gt.1.kpos Gt.1.lpos))
    (hbnd : crudeBMod C f gs zs za P < 2 ^ (b - 1))
    (hchk : ∀ s ∈ pre ++ [(gL, otherPartsModB p zmul C f zs za eqT, oL)],
      checkKRo p b (slicesG p zmul C s.1 lr b s.2.1) cls t0 s.2.2 = true)
    (hoff : ∀ i < t0.leaves.length,
      ((pre ++ [(gL, otherPartsModB p zmul C f zs za eqT, oL)]).map fun s => s.2.2.getD i 0).sum % p = 0) :
    ∃ sp : List (List (GrpF × List (List (List SInt))) × List Part × List ℕ),
      (∀ s ∈ sp, ∀ Gt ∈ s.1,
        Gt.2 = mkTab C Gt.1.kpos Gt.1.lpos (supps 2 Gt.1.kpos Gt.1.lpos) (supps 3 Gt.1.kpos Gt.1.lpos)) ∧
      (∀ s ∈ sp, ∀ P ∈ s.2.1, ∀ m, (P.S.rows m).length = 24) ∧
      (∀ s ∈ sp, ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
        |partsF (gpartsMod p zmul C (s.1.map Prod.fst) ++ s.2.1) w0 w1 w2 w3| < 2 ^ (b - 1)) ∧
      (∀ s ∈ sp, checkKRo p b (slicesG p zmul C s.1 lr b s.2.1) cls t0 s.2.2 = true) ∧
      (∀ i < t0.leaves.length, (sp.map fun s => s.2.2.getD i 0).sum % p = 0) ∧
      (∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
        (sp.map fun s => partsF (gpartsMod p zmul C (s.1.map Prod.fst) ++ s.2.1) w0 w1 w2 w3).sum =
          partsF (famPartsMod p zmul C f gs zs za eqT) w0 w1 w2 w3) := by
  subst hcat
  exact ⟨pre ++ [(gL, otherPartsModB p zmul C f zs za eqT, oL)], htab_last pre gL _ oL htab,
    hO_last p zmul C f zs za eqT pre hpre gL oL, hF_last p zmul C f zs za eqT heqT P b hp hpP pre hpre gL oL hbnd,
    hchk, hoff, fun w0 w1 w2 w3 h0 h1 h2 h3 => hall_last p zmul C f zs za eqT gL oL w0 w1 w2 w3 h0 h1 h2 h3 pre hpre⟩

end

end NPT.Cert.Ident
