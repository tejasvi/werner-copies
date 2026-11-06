/-
NPT.K4.Route.Assembly5 — the parts of family `f` on the aux slice `w 4` (k = 4, d = 3): the rule groups, the objective
and trace rank-one parts (family 0) and the rank-one equality parts.  `ΛS_f(w) · D` is their summed word value at
`(w 0, …, w 3)`, for coefficients tied to `D` by the hypotheses `hcG`, `hcO`, `hcT`, `hcE`.
-/
import NPT.K4.Route.Group5
import NPT.K4.SemS
import NPT.Cert.Ident.ObjEqF

namespace NPT.K4.Route

open BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident NPT.Brauer NPT.K4

/-- Objective factors: sites `α tr V_p − β tr(V_21 V_p)` (n = 3), auxiliary `tr(V_21 V_p)` (n = 2). -/
def zsTt (α β : ℕ) (p : Fin 24) : ℤ := α * trF 3 p - β * trMulF 3 21 p
def zaT5 (p : Fin 24) : ℤ := trMulF 2 21 p

/-- Trace factors `tr V_p` at n = 3 and n = 2. -/
def tsT5 (p : Fin 24) : ℤ := trF 3 p
def taT5 (p : Fin 24) : ℤ := trF 2 p

/-- The rank-one equality parts of family `f` on the slice `w4` (legs 0..3 at n = 3; the auxiliary leg, n = 2, enters
the coefficient). -/
def eqParts5 (C : CertD) (f : ℕ) (cE : ℤ) (w4 : Fin 24) : List Part :=
  C.eqs.flatMap fun g => g.parts.flatMap fun P => if P.fam = f then
    g.lam.map (fun ol => rank1Part (fun l p => eqLocF C (P.specs.getD l default) 3 p (ol.1.getD l 0))
      (-(P.sign) * cE * ol.2 * eqLocF C (P.specs.getD 4 default) 2 w4 (ol.1.getD 4 0))) else []

/-- All parts of family `f` on the slice `w4`. -/
def parts5 (C : CertD) (α β : ℕ) (cG cO cT cE : ℤ) (f : ℕ) (gs : List GrpF) (w4 : Fin 24) : List Part :=
  gs.map (slicePart C cG w4.val) ++
    (if f = 0 then [rank1Part (fun _ p => zsTt α β p) (cO * zaT5 w4),
      rank1Part (fun _ p => tsT5 p) (cT * taT5 w4)] else []) ++
    eqParts5 C f cE w4

lemma groups_component5 (C : CertD) (hk : C.k = 4) (E0 : ℕ) (cG : ℤ) (f : ℕ) (gs : List GrpF)
    (hG : ∀ G ∈ gs, grpOK5 C E0 G = true) (hperm : (gs.flatMap fun G => itemsOf G.tree).Perm (allItems C f))
    (hd : 0 < C.d) (w : Fin (C.k + 1) → Fin 24) :
    ((partsF (gs.map (slicePart C cG (w 4).val)) (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) =
      cG * 2 ^ E0 * (C.types.map fun t => ∑ r ∈ range t.nrows, ∑ s ∈ range t.nrows,
        if ((t.rules.getD r []).getD s default).fam = f then C.blk t r s w else 0).sum := by
  rw [blk_allItems, ← (hperm.map _).sum_eq, sum_flatMap_map]
  unfold partsF
  rw [List.map_map, cast_list_sum, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun G hGm => ?_)
  simp only [Function.comp_apply]
  exact specTree_slicePart C hk E0 cG G (hG G hGm) hd w

lemma prod_four_fin {M : Type*} [CommMonoid M] (g : Fin 4 → M) : ∏ l, g l = g 0 * g 1 * g 2 * g 3 := by
  rw [Fin.prod_univ_four]

lemma prod_five_fin {M : Type*} [CommMonoid M] (g : Fin 5 → M) : ∏ l, g l = g 0 * g 1 * g 2 * g 3 * g 4 := by
  rw [Fin.prod_univ_five]

lemma eq_component5 (C : CertD) (hk : C.k = 4) (hd3 : C.d = 3) (f : ℕ) (cE : ℤ) (D : ℚ)
    (hcE : (cE : ℚ) = D / C.lamDen)
    (hkind : ∀ g ∈ C.eqs, ∀ P ∈ g.parts, ∀ l : Fin (C.k + 1),
      (P.specs.getD l.val default).kind = 0 ∨ nf C.k C.d l = 2)
    (w : Fin (C.k + 1) → Fin 24) :
    ((partsF (eqParts5 C f cE (w 4)) (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) =
      -D * (C.eqs.map fun g => (g.parts.map fun P =>
        if P.fam = f then (P.sign : ℚ) * C.eqVal g P w else 0).sum).sum := by
  obtain ⟨k, d, types, mods, eqs, Z, Lden, lamDen⟩ := C
  simp only at hk hd3
  subst hk hd3
  unfold eqParts5
  rw [partsF_flatMap, cast_list_sum, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun g hg => ?_)
  rw [partsF_flatMap, cast_list_sum, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun P hP => ?_)
  by_cases hf : P.fam = f
  · rw [if_pos hf, if_pos hf]
    unfold CertD.eqVal
    simp only [partsF, List.map_map, rank1Part]
    rw [cast_list_sum]
    simp only [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun ol hol => ?_)
    simp only [Function.comp_apply]
    rw [rank1_spec, prod_five_fin]
    have h3 : ∀ l : Fin (4 + 1), l.val < 4 → nf 4 3 l = 3 := fun l hl => by unfold nf; rw [if_pos hl]
    have h2 : nf 4 3 4 = 2 := rfl
    have hE : ∀ l : Fin (4 + 1), ∀ p o, (eqLocF ⟨4, 3, types, mods, eqs, Z, Lden, lamDen⟩
        (P.specs.getD l.val default) (nf 4 3 l) p o : ℚ) =
        CertD.eqLoc ⟨4, 3, types, mods, eqs, Z, Lden, lamDen⟩ (P.specs.getD l.val default) (nf 4 3 l) p o := by
      intro l p o
      have : NeZero (nf 4 3 l) := ⟨by unfold nf; split_ifs <;> norm_num⟩
      exact eqLocF_eq _ _ _ p o (hkind g hg P hP l)
    have e0 := hE 0 (w 0) (ol.1.getD 0 0); have e1 := hE 1 (w 1) (ol.1.getD 1 0)
    have e2 := hE 2 (w 2) (ol.1.getD 2 0); have e3 := hE 3 (w 3) (ol.1.getD 3 0)
    have e4 := hE 4 (w 4) (ol.1.getD 4 0)
    rw [h3 0 (by decide)] at e0; rw [h3 1 (by decide)] at e1; rw [h3 2 (by decide)] at e2
    rw [h3 3 (by decide)] at e3; rw [h2] at e4
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at e0 e1 e2
    simp only [show ((3 : Fin (4 + 1)) : ℕ) = 3 from rfl] at e3
    simp only [show ((4 : Fin (4 + 1)) : ℕ) = 4 from rfl] at e4
    push_cast
    rw [e0, e1, e2, e3, e4, hcE]
    rw [h3 0 (by decide), h3 1 (by decide), h3 2 (by decide), h3 3 (by decide), h2]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin (4 + 1)) : ℕ) = 3 from rfl,
      show ((4 : Fin (4 + 1)) : ℕ) = 4 from rfl]
    by_cases hL : (lamDen : ℚ) = 0
    · simp [hL]
    · field_simp
  · rw [if_neg hf, if_neg hf]; simp [partsF]

/-- **Assembly on a slice.** `ΛS_f(w) · D` is the summed word value of the family's parts at `(w 0, …, w 3)`. -/
theorem ΛS_partsF5 (C : CertD) (hk : C.k = 4) (hd3 : C.d = 3) (α β : ℕ) (hα : 0 < α) (nu : ℚ) (E0 : ℕ)
    (cG cO cT cE : ℤ) (D : ℚ) (f : ℕ) (gs : List GrpF)
    (hG : ∀ G ∈ gs, grpOK5 C E0 G = true) (hperm : (gs.flatMap fun G => itemsOf G.tree).Perm (allItems C f))
    (hcG : (cG : ℚ) * 2 ^ E0 = -D)
    (hcO : (cO : ℚ) = D / ((α : ℚ) ^ 4 * (2 * 3 ^ 4) ^ 4))
    (hcT : (cT : ℚ) = -(D * nu / (2 * 3 ^ 4) ^ 4))
    (hcE : (cE : ℚ) = D / C.lamDen)
    (hkind : ∀ g ∈ C.eqs, ∀ P ∈ g.parts, ∀ l : Fin (C.k + 1),
      (P.specs.getD l.val default).kind = 0 ∨ nf C.k C.d l = 2)
    (w : Fin (C.k + 1) → Fin 24) :
    ΛS C α β nu f w * D =
      ((partsF (parts5 C α β cG cO cT cE f gs (w 4)) (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) := by
  have hd : 0 < C.d := by rw [hd3]; norm_num
  unfold parts5
  rw [partsF_append, partsF_append, Int.cast_add, Int.cast_add,
    groups_component5 C hk E0 cG f gs hG hperm hd w, eq_component5 C hk hd3 f cE D hcE hkind w]
  unfold ΛS
  by_cases hf : f = 0
  · rw [if_pos hf, if_pos hf]
    have hO : ((partsF [rank1Part (fun _ p => zsTt α β p) (cO * zaT5 (w 4)),
        rank1Part (fun _ p => tsT5 p) (cT * taT5 (w 4))] (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) =
        (objT C α β w - nu * trW C w / (2 * C.d ^ C.k) ^ 4) * D := by
      simp only [partsF, rank1Part, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [rank1_spec, rank1_spec]
      obtain ⟨k, d, types, mods, eqs, Z, Lden, lamDen⟩ := C
      simp only at hk hd3
      subst hk hd3
      unfold objT trW
      rw [prod_four_fin, prod_five_fin]
      simp only [zsTt, zaT5, tsT5, taT5]
      push_cast
      have n0 : nf 4 3 0 = 3 := rfl
      have n1 : nf 4 3 1 = 3 := rfl
      have n2 : nf 4 3 2 = 3 := rfl
      have n3 : nf 4 3 3 = 3 := rfl
      have n4 : nf 4 3 4 = 2 := rfl
      have i3 : NeZero 3 := ⟨by norm_num⟩
      have i2 : NeZero 2 := ⟨by norm_num⟩
      simp only [trF_eq, trMulF_eq]
      rw [n0, n1, n2, n3, n4, hcO, hcT]
      ring
    rw [hO]
    push_cast
    rw [hcG]
    ring
  · rw [if_neg hf, if_neg hf]
    simp only [partsF, List.map_nil, List.sum_nil, Int.cast_zero, List.nil_append]
    push_cast
    rw [hcG]
    ring

end NPT.K4.Route
