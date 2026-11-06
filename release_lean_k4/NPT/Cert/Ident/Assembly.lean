/-
NPT.Cert.Ident.Assembly — `Λ_f(w) · 2Lden · den = partsF (family parts) (w)`.
The objective and equality tables enter through hypotheses (their flat forms are proved in ObjEqF.lean).
-/
import NPT.Cert.Ident.GroupBridge
import NPT.Cert.Ident.Rank1

open BigOperators Finset NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.Ident

/-- All items `(t, r, s)` of family `f`, in index order. -/
def allItems (C : CertD) (f : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range C.types.length).flatMap fun ti =>
    (List.range (C.types.getD ti default).nrows).flatMap fun r =>
      ((List.range (C.types.getD ti default).nrows).filter fun s =>
        (((C.types.getD ti default).rules.getD r []).getD s default).fam == f).map fun s => (ti, r, s)

lemma finset_sum_range_list (n : ℕ) (h : ℕ → ℚ) : ∑ r ∈ range n, h r = ((List.range n).map h).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

lemma list_map_eq_range_getD {α β : Type*} [Inhabited α] (L : List α) (g : α → β) :
    L.map g = (List.range L.length).map fun i => g (L.getD i default) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa using h1)]; rfl

lemma sum_ite_filter (L : List ℕ) (P : ℕ → Bool) (h : ℕ → ℚ) :
    (L.map fun s => if P s = true then h s else 0).sum = ((L.filter P).map h).sum := by
  induction L with
  | nil => simp
  | cons a L ih => by_cases hp : P a = true <;> simp [List.filter_cons, hp, ih]

/-- The block part of `Λ` as a sum over `allItems`. -/
lemma blk_allItems (C : CertD) (f : ℕ) (w : Fin (C.k + 1) → Fin 24) :
    (C.types.map fun t => ∑ r ∈ range t.nrows, ∑ s ∈ range t.nrows,
        if ((t.rules.getD r []).getD s default).fam = f then C.blk t r s w else 0).sum =
      ((allItems C f).map fun it => C.blk (C.types.getD it.1 default) it.2.1 it.2.2 w).sum := by
  rw [list_map_eq_range_getD C.types, allItems, sum_flatMap_map]
  refine congrArg List.sum (List.map_congr_left fun ti _ => ?_)
  rw [finset_sum_range_list, sum_flatMap_map]
  refine congrArg List.sum (List.map_congr_left fun r _ => ?_)
  rw [finset_sum_range_list, List.map_map]
  rw [← sum_ite_filter _ (fun s => (((C.types.getD ti default).rules.getD r []).getD s default).fam == f)]
  refine congrArg List.sum (List.map_congr_left fun s _ => ?_)
  simp only [beq_iff_eq, Function.comp_apply]


/-- The objective column tables as one leg function (sites `zs`, aux `za`). -/
def objE (zs za : Fin 24 → ℤ) : ℕ → Fin 24 → ℤ := fun l p => if l < 3 then zs p else za p

/-- The objective part of `Λ`, scaled by `den = 2^3 (2 d^3)^4`. -/
lemma obj_component (C : CertD) (hk : C.k = 3) (zs za : Fin 24 → ℤ)
    (hzs : ∀ p, (zs p : ℚ) = 2 * Matrix.trace (VG ℚ C.d 0 p) - Matrix.trace (VG ℚ C.d 0 21 * VG ℚ C.d 0 p))
    (hza : ∀ p, (za p : ℚ) = Matrix.trace (VG ℚ 2 0 21 * VG ℚ 2 0 p)) (hd : 0 < C.d)
    (w : Fin (C.k + 1) → Fin 24) :
    C.obj w * (2 ^ 3 * (2 * (C.d : ℚ) ^ 3) ^ 4) =
      (objE zs za 0 (w 0) * objE zs za 1 (w 1) * objE zs za 2 (w 2) * objE zs za 3 (w 3) : ℤ) := by
  obtain ⟨k, d, types, mods, eqs, Z, Lden, lamDen⟩ := C
  simp only at hk
  subst hk
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold CertD.obj
  simp only [objE]
  push_cast
  rw [hzs, hzs, hzs, hza]
  simp only [Fin.prod_univ_three]
  field_simp
  rw [show (Fin.castSucc (0 : Fin 3) : Fin (3 + 1)) = 0 from rfl,
    show (Fin.castSucc (1 : Fin 3) : Fin (3 + 1)) = 1 from rfl,
    show (Fin.castSucc (2 : Fin 3) : Fin (3 + 1)) = 2 from rfl]
  ring


/-- `den = 2^3 (2 d^3)^4`. -/
def den3 (d : ℕ) : ℕ := 2 ^ 3 * (2 * d ^ 3) ^ 4

/-- Local dimension of leg `l` (sites `d`, aux `2`). -/
def nfN (d l : ℕ) : ℕ := if l < 3 then d else 2

/-- The rank-one parts of the equality multipliers of family `f`. -/
def eqPartsF (C : CertD) (f : ℕ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : List Part :=
  C.eqs.flatMap fun g => g.parts.flatMap fun P => if P.fam = f then
    g.lam.map (fun ol => rank1Part (fun l p => eqT (P.specs.getD l default) (nfN C.d l) p (ol.1.getD l 0))
      (-(P.sign) * (den3 C.d : ℤ) * ol.2)) else []

/-- All parts of family `f`. -/
def famParts (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : List Part :=
  gs.map (fun G => ⟨ruleSpecF C zmul (-(den3 C.d : ℤ)) G.kpos G.lpos, G.tree⟩) ++
    (if f = 0 then [rank1Part (objE zs za) (2 * C.Lden)] else []) ++ eqPartsF C f eqT

lemma partsF_append (ps qs : List Part) (w0 w1 w2 w3 : ℕ) :
    partsF (ps ++ qs) w0 w1 w2 w3 = partsF ps w0 w1 w2 w3 + partsF qs w0 w1 w2 w3 := by
  simp [partsF, List.map_append, List.sum_append]


lemma groups_component (C : CertD) (hk : C.k = 3) (zmul f : ℕ) (gs : List GrpF)
    (hG : ∀ G ∈ gs, grpOK C zmul G = true) (hperm : (gs.flatMap fun G => itemsOf G.tree).Perm (allItems C f))
    (hd : 0 < C.d) (hL : 0 < C.Lden) (w : Fin (C.k + 1) → Fin 24) :
    ((partsF (gs.map fun G => ⟨ruleSpecF C zmul (-(den3 C.d : ℤ)) G.kpos G.lpos, G.tree⟩)
        (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) =
      -((2 * C.Lden * den3 C.d : ℕ) : ℚ) * (C.types.map fun t => ∑ r ∈ range t.nrows, ∑ s ∈ range t.nrows,
        if ((t.rules.getD r []).getD s default).fam = f then C.blk t r s w else 0).sum := by
  rw [blk_allItems, ← (hperm.map _).sum_eq, sum_flatMap_map]
  unfold partsF
  rw [List.map_map, cast_list_sum, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun G hGm => ?_)
  simp only [Function.comp_apply]
  rw [specTree_ruleSpecF C hk zmul _ G (hG G hGm) hd hL w]
  push_cast; ring


lemma partsF_flatMap {α : Type*} (L : List α) (h : α → List Part) (w0 w1 w2 w3 : ℕ) :
    partsF (L.flatMap h) w0 w1 w2 w3 = (L.map fun x => partsF (h x) w0 w1 w2 w3).sum := by
  induction L with
  | nil => simp [partsF]
  | cons a L ih => rw [List.flatMap_cons, partsF_append, ih]; simp

lemma nfN_eq (d : ℕ) (l : Fin (3 + 1)) : nfN d l.val = nf 3 d l := by
  unfold nfN nf; rfl

lemma prod_four_eq {M : Type*} [CommMonoid M] (g : Fin (3 + 1) → M) : ∏ l, g l = g 0 * g 1 * g 2 * g 3 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_one]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [mul_assoc, mul_assoc, show (Fin.succ (2 : Fin 3) : Fin (3 + 1)) = 3 from rfl]

lemma eq_component (C : CertD) (hk : C.k = 3) (hlam : C.lamDen = 2 * C.Lden) (hL : 0 < C.Lden) (f : ℕ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ)
    (heq : ∀ g ∈ C.eqs, ∀ P ∈ g.parts, ∀ l : Fin (C.k + 1), ∀ p o,
      (eqT (P.specs.getD l.val default) (nfN C.d l.val) p o : ℚ) = C.eqLoc (P.specs.getD l.val default) (nf C.k C.d l) p o)
    (w : Fin (C.k + 1) → Fin 24) :
    ((partsF (eqPartsF C f eqT) (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) =
      -((2 * C.Lden * den3 C.d : ℕ) : ℚ) * (C.eqs.map fun g => (g.parts.map fun P =>
        if P.fam = f then (P.sign : ℚ) * C.eqVal g P w else 0).sum).sum := by
  obtain ⟨k, d, types, mods, eqs, Z, Lden, lamDen⟩ := C
  simp only at hk hlam
  subst hk hlam
  unfold eqPartsF
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
    rw [rank1_spec, prod_four_eq]
    rw [← heq g hg P hP 0, ← heq g hg P hP 1, ← heq g hg P hP 2, ← heq g hg P hP 3]
    have hL' : (Lden : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, show ((3 : Fin (3 + 1)) : ℕ) = 3 from rfl]
    push_cast
    field_simp
  · rw [if_neg hf, if_neg hf]; simp [partsF]


/-- **Assembly.** `Λ_f(w) · 2Lden · den` is the summed word value of the family's parts. -/
theorem Λ_partsF (C : CertD) (hk : C.k = 3) (hlam : C.lamDen = 2 * C.Lden) (hd : 0 < C.d) (hL : 0 < C.Lden)
    (zmul f : ℕ) (gs : List GrpF) (hG : ∀ G ∈ gs, grpOK C zmul G = true)
    (hperm : (gs.flatMap fun G => itemsOf G.tree).Perm (allItems C f)) (zs za : Fin 24 → ℤ)
    (hzs : ∀ p, (zs p : ℚ) = 2 * Matrix.trace (VG ℚ C.d 0 p) - Matrix.trace (VG ℚ C.d 0 21 * VG ℚ C.d 0 p))
    (hza : ∀ p, (za p : ℚ) = Matrix.trace (VG ℚ 2 0 21 * VG ℚ 2 0 p))
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ)
    (heq : ∀ g ∈ C.eqs, ∀ P ∈ g.parts, ∀ l : Fin (C.k + 1), ∀ p o,
      (eqT (P.specs.getD l.val default) (nfN C.d l.val) p o : ℚ) = C.eqLoc (P.specs.getD l.val default) (nf C.k C.d l) p o)
    (w : Fin (C.k + 1) → Fin 24) :
    C.Λ f w * ((2 * C.Lden * den3 C.d : ℕ) : ℚ) =
      ((partsF (famParts C zmul f gs zs za eqT) (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) := by
  unfold famParts
  rw [partsF_append, partsF_append, Int.cast_add, Int.cast_add, groups_component C hk zmul f gs hG hperm hd hL w,
    eq_component C hk hlam hL f eqT heq w]
  unfold CertD.Λ
  by_cases hf : f = 0
  · rw [if_pos hf, if_pos hf]
    have hO : ((partsF [rank1Part (objE zs za) (2 * C.Lden)] (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) =
        C.obj w * ((2 * C.Lden * den3 C.d : ℕ) : ℚ) := by
      simp only [partsF, rank1Part, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [rank1_spec]
      have := obj_component C hk zs za hzs hza hd w
      push_cast
      rw [show (den3 C.d : ℚ) = 2 ^ 3 * (2 * (C.d : ℚ) ^ 3) ^ 4 by unfold den3; push_cast; ring,
        show C.obj w * (2 * (C.Lden : ℚ) * (2 ^ 3 * (2 * (C.d : ℚ) ^ 3) ^ 4)) =
          2 * C.Lden * (C.obj w * (2 ^ 3 * (2 * (C.d : ℚ) ^ 3) ^ 4)) by ring, this]
      push_cast; ring
    rw [hO]; ring
  · rw [if_neg hf, if_neg hf]
    simp only [partsF, List.map_nil, List.sum_nil, Int.cast_zero]
    ring

end NPT.Cert.Ident
