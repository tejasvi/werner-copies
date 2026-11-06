/-
NPT.Cert.Ident.KRIdFactB — the kernel route with each equality part as ONE λ-box part (`EqBox`) instead of its
rank-one terms: `slicesKRB` has the packed word values of `famPartsMod` (`slicesKRB_gv`), so the
class-sum facts `classSums_modPB` / `hsum_of_checksB` hold exactly as for `slicesKR`.
-/
import NPT.Cert.Ident.KRIdFact
import NPT.Cert.Ident.EqBox

open BigOperators Finset NPT.Cert.Sem NPT.Cert.Ident NPT.Brauer

namespace NPT.Cert.KR

/-- `otherPartsMod` with the equality parts as λ-boxes. -/
noncomputable def otherPartsModB (p zmul : ℕ) (C : CertD) (f : ℕ) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : List Part :=
  (if f = 0 then [rank1Part (objE zs za) ((2 * C.Lden : ℤ) % (p : ℤ))] else []) ++ eqBoxPartsF (certModR p zmul C) f eqT

/-- **The 24 slices of family `f`, data mod `p`, equality parts as λ-boxes** (otherwise as `slicesKR`). -/
noncomputable def slicesKRB (p zmul : ℕ) (C : CertD) (f : ℕ) (gts : List (GrpF × List (List (List SInt))))
    (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (b : ℕ) : List SInt :=
  addLR (foldrR (fun Gt acc => addLR (evalTreeRR (certModR p zmul C) Gt.1.kpos Gt.1.lpos Gt.2 lr b Gt.1.tree) acc) [] gts)
    (foldrR (fun P acc => addLR (evalTree P.S b P.tree) acc) [] (otherPartsModB p zmul C f zs za eqT))

lemma slicesKRB_eq (p zmul : ℕ) (C : CertD) (f : ℕ) (gts : List (GrpF × List (List (List SInt))))
    (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (hlr : LRShape lr) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (b : ℕ) :
    slicesKRB p zmul C f gts lr zs za eqT b =
      addL (partsSlices b (grpPartsRows (certModR p zmul C) gts lr))
        (partsSlices b (otherPartsModB p zmul C f zs za eqT)) := by
  unfold slicesKRB partsSlices grpPartsRows
  rw [addLR_eq, foldrR_eq, foldrR_eq, List.map_map, List.foldr_map, List.foldr_map]
  congr 1
  · refine congrArg (fun g => List.foldr g [] gts) (funext fun Gt => funext fun acc => ?_)
    rw [addLR_eq, evalTreeRR_eq _ _ _ _ lr b hlr]
    rfl
  · refine congrArg (fun g => List.foldr g [] _) (funext fun P => funext fun acc => ?_)
    rw [addLR_eq]

lemma otherPartsMod_rows (p zmul : ℕ) (C : CertD) (f : ℕ) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : ∀ P ∈ otherPartsMod p zmul C f zs za eqT, ∀ m, (P.S.rows m).length = 24 := by
  intro P hP m
  unfold otherPartsMod eqPartsF at hP
  rw [List.mem_append] at hP
  rcases hP with hP | hP
  · by_cases hf : f = 0
    · rw [ite_eq_left hf, List.mem_singleton] at hP; subst hP; exact rank1Spec_rows _ _ m
    · rw [ite_eq_right hf] at hP; simp at hP
  · rw [List.mem_flatMap] at hP
    obtain ⟨g, _, hP⟩ := hP
    rw [List.mem_flatMap] at hP
    obtain ⟨P', _, hP'⟩ := hP
    by_cases hf : P'.fam = f
    · rw [ite_eq_left hf, List.mem_map] at hP'; obtain ⟨ol, _, rfl⟩ := hP'; exact rank1Spec_rows _ _ m
    · rw [ite_eq_right hf] at hP'; simp at hP'

lemma otherPartsModB_rows (p zmul : ℕ) (C : CertD) (f : ℕ) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : ∀ P ∈ otherPartsModB p zmul C f zs za eqT, ∀ m, (P.S.rows m).length = 24 := by
  intro P hP m
  unfold otherPartsModB at hP
  rw [List.mem_append] at hP
  rcases hP with hP | hP
  · by_cases hf : f = 0
    · rw [ite_eq_left hf, List.mem_singleton] at hP; subst hP; exact rank1Spec_rows _ _ m
    · rw [ite_eq_right hf] at hP; simp at hP
  · exact eqBoxPartsF_rows _ f eqT P hP m

/-- `slicesKRB` and `slicesKR` have the same packed words. -/
theorem slicesKRB_gv_eq (p zmul : ℕ) (C : CertD) (f : ℕ) (gts : List (GrpF × List (List (List SInt))))
    (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (hlr : LRShape lr) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (b : ℕ) (w3 : ℕ) (hw : w3 < 24) :
    gv (slicesKRB p zmul C f gts lr zs za eqT b) w3 = gv (slicesKR p zmul C f gts lr zs za eqT b) w3 := by
  rw [slicesKRB_eq p zmul C f gts lr hlr zs za eqT b, slicesKR_eq p zmul C f gts lr hlr zs za eqT b, gv_addL, gv_addL]
  congr 1
  rw [partsSlices_gv b _ (otherPartsModB_rows p zmul C f zs za eqT) w3 hw,
    partsSlices_gv b _ (otherPartsMod_rows p zmul C f zs za eqT) w3 hw]
  refine Finset.sum_congr rfl fun w2 hw2 => ?_
  congr 1
  refine Finset.sum_congr rfl fun w1 hw1 => ?_
  congr 1
  refine Finset.sum_congr rfl fun w0 hw0 => ?_
  congr 1
  unfold otherPartsModB otherPartsMod
  rw [partsF_append, partsF_append]
  congr 1
  exact partsF_eqBox (certModR p zmul C) f eqT ⟨w0, mem_range.1 hw0⟩ ⟨w1, mem_range.1 hw1⟩ ⟨w2, mem_range.1 hw2⟩
    ⟨w3, hw⟩

/-- **The packed word values of the mod-`p` parts** (as `slicesKR_gv`). -/
theorem slicesKRB_gv (p zmul : ℕ) (C : CertD) (f : ℕ) (gts : List (GrpF × List (List (List SInt))))
    (htab : ∀ Gt ∈ gts, Gt.2 = mkTab C Gt.1.kpos Gt.1.lpos (supps 2 Gt.1.kpos Gt.1.lpos) (supps 3 Gt.1.kpos Gt.1.lpos))
    (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (b : ℕ)
    (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (hlr : LRShape lr)
    (hleaf : ∀ d0 d1 d2 d3 items k, gv (lr d0 d1 d2 d3 items).flatten k =
      gv ((items.map (itemTF (certMod p zmul C) 1 (-(den3 C.d : ℤ)) d0 d1 d2 d3)).foldr addL []) k)
    (w3 : ℕ) (hw : w3 < 24) :
    gv (slicesKRB p zmul C f gts lr zs za eqT b) w3 =
      ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24,
        partsF (famPartsMod p zmul C f (gts.map Prod.fst) zs za eqT) w0 w1 w2 w3 * 2 ^ (b * w0)) *
          2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2) := by
  rw [slicesKRB_gv_eq p zmul C f gts lr hlr zs za eqT b w3 hw]
  exact slicesKR_gv p zmul C f gts htab zs za eqT b lr hlr hleaf w3 hw

/-- `classSums_modP` for `slicesKRB`. -/
theorem classSums_modPB (p zmul : ℕ) (C : CertD) (f : ℕ) (gts : List (GrpF × List (List (List SInt))))
    (htab : ∀ Gt ∈ gts, Gt.2 = mkTab C Gt.1.kpos Gt.1.lpos (supps 2 Gt.1.kpos Gt.1.lpos) (supps 3 Gt.1.kpos Gt.1.lpos))
    (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (b : ℕ) (hb : 0 < b)
    (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (hlr : LRShape lr)
    (hleaf : ∀ d0 d1 d2 d3 items k, gv (lr d0 d1 d2 d3 items).flatten k =
      gv ((items.map (itemTF (certMod p zmul C) 1 (-(den3 C.d : ℤ)) d0 d1 d2 d3)).foldr addL []) k)
    (hF : ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
      |partsF (famPartsMod p zmul C f (gts.map Prod.fst) zs za eqT) w0 w1 w2 w3| < 2 ^ (b - 1))
    (cls : List ℕ) (hcls : cls.length = 24 * slen) (t0 : AT)
    (hchk : checkKR p b (slicesKRB p zmul C f gts lr zs za eqT b) cls t0 = true) (q : ℕ) (hq : q < 24 * slen) :
    (∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      partsF (famParts C zmul f (gts.map Prod.fst) zs za eqT) (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2
      else 0)) ≡ 0 [ZMOD p] := by
  have h24 : ∀ x : ℕ, x % 24 < 24 := fun x => Nat.mod_lt _ (by norm_num)
  have hmod := checkKR_sound p b hb _ cls t0 hchk (partsF (famPartsMod p zmul C f (gts.map Prod.fst) zs za eqT))
    (slicesKRB_gv p zmul C f gts htab zs za eqT b lr hlr hleaf)
    (fun q' hq' => hF _ _ _ _ (h24 _) (h24 _) (h24 _) (by unfold wd slen at *; simp only; omega)) hcls q hq
  refine Int.ModEq.trans ?_ hmod
  refine Int.ModEq.sum fun q' _ => ?_
  split_ifs
  · exact partsF_mod p zmul C f (gts.map Prod.fst) zs za eqT _ _ _ _
  · exact Int.ModEq.rfl

/-- **`hsum_of_checks` for `slicesKRB`.** -/
theorem hsum_of_checksB (d : ℕ) (types : List TypeD) (mods : List ModD) (eqs : List EqGroupD)
    (Z : List NPT.Cert.PBlock) (Lden : ℕ) (hd : 0 < d) (hL : 0 < Lden) (zmul f b : ℕ) (hb : 0 < b)
    (gts : List (GrpF × List (List (List SInt))))
    (htab : ∀ Gt ∈ gts, Gt.2 = mkTab ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ Gt.1.kpos Gt.1.lpos
      (supps 2 Gt.1.kpos Gt.1.lpos) (supps 3 Gt.1.kpos Gt.1.lpos))
    (hG : ∀ G ∈ gts.map Prod.fst, grpOK ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ zmul G = true)
    (hperm : ((gts.map Prod.fst).flatMap fun G => itemsOf G.tree).Perm
      (allItems ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ f))
    (zs za : Fin 24 → ℤ)
    (hzs : ∀ p, (zs p : ℚ) = 2 * Matrix.trace (VG ℚ d 0 p) - Matrix.trace (VG ℚ d 0 21 * VG ℚ d 0 p))
    (hza : ∀ p, (za p : ℚ) = Matrix.trace (VG ℚ 2 0 21 * VG ℚ 2 0 p))
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ)
    (heq : ∀ g ∈ eqs, ∀ P ∈ g.parts, ∀ l : Fin (3 + 1), ∀ p o,
      (eqT (P.specs.getD l.val default) (nfN d l.val) p o : ℚ) =
        CertD.eqLoc ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ (P.specs.getD l.val default) (nf 3 d l) p o)
    (lr : ℕ → ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (hlr : ∀ p, LRShape (lr p))
    (hleaf : ∀ p d0 d1 d2 d3 items k, gv (lr p d0 d1 d2 d3 items).flatten k =
      gv ((items.map (itemTF (certMod p zmul ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩) 1
        (-(den3 d : ℤ)) d0 d1 d2 d3)).foldr addL []) k)
    (ps : List ℕ) (hcop : ps.Pairwise Nat.Coprime)
    (hFmod : ∀ p ∈ ps, ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
      |partsF (famPartsMod p zmul ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ f (gts.map Prod.fst) zs za eqT)
        w0 w1 w2 w3| < 2 ^ (b - 1))
    (B : ℕ) (hB : ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
      |partsF (famParts ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ zmul f (gts.map Prod.fst) zs za eqT)
        w0 w1 w2 w3| ≤ B)
    (hBp : 24 * slen * B < ps.prod)
    (cls : List ℕ) (hcls : cls.length = 24 * slen) (t0 : AT)
    (hchecks : ∀ p ∈ ps, checkKR p b (slicesKRB p zmul ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ f gts (lr p)
      zs za eqT b) cls t0 = true)
    (w₀ : Fin (3 + 1) → Fin 24) :
    ∑ w ∈ univ.filter (fun w : Fin (3 + 1) → Fin 24 => cls.getD (posW w) 0 = cls.getD (posW w₀) 0),
      CertD.Λ ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ f w = 0 := by
  refine hsum_of_posSums d types mods eqs Z Lden hd hL zmul f (gts.map Prod.fst) hG hperm zs za hzs hza eqT heq cls
    (fun q hq => ?_) w₀
  refine eq_zero_of_modEq_list _ ps hcop (fun p hp => ?_)
    (lt_of_le_of_lt (classSum_abs_le cls _ B hB q) hBp)
  exact classSums_modPB p zmul _ f gts htab zs za eqT b hb (lr p) (hlr p) (hleaf p) (hFmod p hp) cls hcls t0
    (hchecks p hp) q hq

end NPT.Cert.KR
