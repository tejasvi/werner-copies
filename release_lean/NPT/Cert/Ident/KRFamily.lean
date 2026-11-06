/-
NPT.Cert.Ident.KRFamily — one family's mod-`p` slices by recursor stages: `slicesKR` packs the word
values of `famPartsMod` (`slicesKR_gv`).
-/
import NPT.Cert.Ident.KRCheck
import NPT.Cert.Ident.KRTree
import NPT.Cert.Ident.ModP

open BigOperators Finset NPT.Cert.Sem NPT.Cert.Ident

namespace NPT.Cert.KR

/-- The objective and equality parts of family `f` with reduced data (as in `famPartsMod`). -/
noncomputable def otherPartsMod (p zmul : ℕ) (C : CertD) (f : ℕ) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : List Part :=
  (if f = 0 then [rank1Part (objE zs za) ((2 * C.Lden : ℤ) % (p : ℤ))] else []) ++ eqPartsF (certModR p zmul C) f eqT

/-- **The 24 slices of family `f`, data mod `p`**: rule groups `gts` (group, local-row table) by recursor stages with
row-form leaves `lr`, the other parts by `evalTree`. -/
noncomputable def slicesKR (p zmul : ℕ) (C : CertD) (f : ℕ) (gts : List (GrpF × List (List (List SInt))))
    (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (b : ℕ) : List SInt :=
  addLR (foldrR (fun Gt acc => addLR (evalTreeRR (certModR p zmul C) Gt.1.kpos Gt.1.lpos Gt.2 lr b Gt.1.tree) acc) [] gts)
    (foldrR (fun P acc => addLR (evalTree P.S b P.tree) acc) [] (otherPartsMod p zmul C f zs za eqT))

lemma pack_add (b : ℕ) (F G : ℕ → ℕ → ℕ → ℤ) :
    (∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24, F w0 w1 w2 * 2 ^ (b * w0)) * 2 ^ (24 * b * w1)) *
      2 ^ (576 * b * w2)) +
    (∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24, G w0 w1 w2 * 2 ^ (b * w0)) * 2 ^ (24 * b * w1)) *
      2 ^ (576 * b * w2)) =
    ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24, (F w0 w1 w2 + G w0 w1 w2) * 2 ^ (b * w0)) *
      2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w2 _ => ?_
  rw [← add_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w1 _ => ?_
  rw [← add_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w0 _ => ?_
  ring

/-- Group parts with table specs and row-form leaves. -/
noncomputable def grpPartsRows (C' : CertD) (gts : List (GrpF × List (List (List SInt))))
    (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) : List Part :=
  gts.map fun Gt => ⟨specRows C' Gt.1.kpos Gt.1.lpos Gt.2 lr, Gt.1.tree⟩

lemma slicesKR_eq (p zmul : ℕ) (C : CertD) (f : ℕ) (gts : List (GrpF × List (List (List SInt))))
    (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (hlr : LRShape lr) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (b : ℕ) :
    slicesKR p zmul C f gts lr zs za eqT b =
      addL (partsSlices b (grpPartsRows (certModR p zmul C) gts lr))
        (partsSlices b (otherPartsMod p zmul C f zs za eqT)) := by
  unfold slicesKR partsSlices grpPartsRows
  rw [addLR_eq, foldrR_eq, foldrR_eq, List.map_map, List.foldr_map, List.foldr_map]
  congr 1
  · refine congrArg (fun g => List.foldr g [] gts) (funext fun Gt => funext fun acc => ?_)
    rw [addLR_eq, evalTreeRR_eq _ _ _ _ lr b hlr]
    rfl
  · refine congrArg (fun g => List.foldr g [] _) (funext fun P => funext fun acc => ?_)
    rw [addLR_eq]

lemma specTree_eq_of_leaf (S S' : Spec) (hR : S'.rows = S.rows) (hD : S'.dimsq = S.dimsq)
    (hL : ∀ m1 m2 m3 lf k, gv (S.leaf m1 m2 m3 lf) k = gv (S'.leaf m1 m2 m3 lf) k) (tree : List Nd3)
    (w0 w1 w2 w3 : ℕ) : specTree S tree w0 w1 w2 w3 = specTree S' tree w0 w1 w2 w3 := by
  have h := specTree_mod 0 S S' hR hD (fun m1 m2 m3 lf k => by rw [hL]) tree w0 w1 w2 w3
  unfold Int.ModEq at h
  simpa using h

/-- **The packed word values of the mod-`p` parts.** -/
theorem slicesKR_gv (p zmul : ℕ) (C : CertD) (f : ℕ) (gts : List (GrpF × List (List (List SInt))))
    (htab : ∀ Gt ∈ gts, Gt.2 = mkTab C Gt.1.kpos Gt.1.lpos (supps 2 Gt.1.kpos Gt.1.lpos) (supps 3 Gt.1.kpos Gt.1.lpos))
    (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (b : ℕ)
    (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (hlr : LRShape lr)
    (hleaf : ∀ d0 d1 d2 d3 items k, gv (lr d0 d1 d2 d3 items).flatten k =
      gv ((items.map (itemTF (certMod p zmul C) 1 (-(den3 C.d : ℤ)) d0 d1 d2 d3)).foldr addL []) k)
    (w3 : ℕ) (hw : w3 < 24) :
    gv (slicesKR p zmul C f gts lr zs za eqT b) w3 =
      ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24,
        partsF (famPartsMod p zmul C f (gts.map Prod.fst) zs za eqT) w0 w1 w2 w3 * 2 ^ (b * w0)) *
          2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2) := by
  have hC : certModR p zmul C = certMod p zmul C := certModR_eq p zmul C
  have hmods : (certMod p zmul C).mods = C.mods := rfl
  have hrowsR : ∀ Gt ∈ gts, ∀ m, (specRows (certMod p zmul C) Gt.1.kpos Gt.1.lpos Gt.2 lr).rows m =
      localRowsF ((certMod p zmul C).mods.getD m default) Gt.1.kpos Gt.1.lpos := by
    intro Gt hGt m
    simp only [specRows]
    rw [htab Gt hGt, mkTab_eq, getD_map', hmods]
  rw [slicesKR_eq p zmul C f gts lr hlr zs za eqT b, gv_addL, hC]
  have hrowsA : ∀ P ∈ grpPartsRows (certMod p zmul C) gts lr, ∀ m, (P.S.rows m).length = 24 := by
    intro P hP m
    simp only [grpPartsRows, List.mem_map] at hP
    obtain ⟨Gt, hGt, rfl⟩ := hP
    rw [hrowsR Gt hGt m]
    exact localRowsF_length _ _ _
  have hrowsB : ∀ P ∈ otherPartsMod p zmul C f zs za eqT, ∀ m, (P.S.rows m).length = 24 := by
    intro P hP m
    unfold otherPartsMod eqPartsF at hP
    rw [List.mem_append] at hP
    rcases hP with hP | hP
    · by_cases hf : f = 0
      · rw [if_pos hf, List.mem_singleton] at hP; subst hP; exact rank1Spec_rows _ _ m
      · rw [if_neg hf] at hP; simp at hP
    · rw [List.mem_flatMap] at hP
      obtain ⟨g, _, hP⟩ := hP
      rw [List.mem_flatMap] at hP
      obtain ⟨P', _, hP'⟩ := hP
      by_cases hf : P'.fam = f
      · rw [if_pos hf, List.mem_map] at hP'; obtain ⟨ol, _, rfl⟩ := hP'; exact rank1Spec_rows _ _ m
      · rw [if_neg hf] at hP'; simp at hP'
  rw [partsSlices_gv b _ hrowsA w3 hw, partsSlices_gv b _ hrowsB w3 hw, pack_add]
  refine Finset.sum_congr rfl fun w2 _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun w1 _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun w0 _ => ?_
  congr 1
  unfold famPartsMod
  rw [partsF_append, partsF_append, add_assoc]
  congr 1
  · unfold grpPartsRows
    rw [partsF_map, partsF_map, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun Gt hGt => ?_)
    simp only [Function.comp_apply]
    refine specTree_eq_of_leaf (specRows (certMod p zmul C) Gt.1.kpos Gt.1.lpos Gt.2 lr)
      (ruleSpecF (certMod p zmul C) 1 (-(den3 C.d : ℤ)) Gt.1.kpos Gt.1.lpos)
      (by funext m; rw [hrowsR Gt hGt m]; rfl) rfl (fun m1 m2 m3 lf k => hleaf _ _ _ _ _ k) _ _ _ _ _
  · unfold otherPartsMod
    rw [hC, partsF_append]

end NPT.Cert.KR
