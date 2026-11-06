/-
NPT.K4.Route.Group5 — a rule group on the aux slice `w 4` (k = 4): its multilinear form at `(w 0, …, w 3)` is
`coef · 2^E · Σ_items blk t r s w`, given the data conditions `grpOK5` (checked by the checker).
-/
import NPT.K4.Route.Item5

namespace NPT.K4.Route

open BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident

/-- The table of a group gives the local rows of every module. -/
lemma lookTab_rowTab (C : CertD) (kpos lpos : List ℕ) (ms : List ℕ) (m : ℕ) :
    lookTab C kpos lpos (rowTab C kpos lpos ms) m = localRowsF (C.mods.getD m default) kpos lpos := by
  unfold lookTab rowTab
  induction ms with
  | nil => rfl
  | cons a ms ih =>
    simp only [List.map_cons, List.find?_cons]
    by_cases h : a = m
    · subst h; simp
    · have h' : (a == m) = false := by simpa using h
      rw [h']
      exact ih

lemma sliceSpec_rows (C : CertD) (coef : Int) (kpos lpos : List ℕ) (ms : List ℕ) (w4 m : ℕ) :
    (sliceSpec C coef kpos lpos (rowTab C kpos lpos ms) w4).rows m = localRowsF (C.mods.getD m default) kpos lpos :=
  lookTab_rowTab C kpos lpos ms m

lemma sliceSpec_rows_length (C : CertD) (coef : Int) (kpos lpos : List ℕ) (ms : List ℕ) (w4 m : ℕ) :
    ((sliceSpec C coef kpos lpos (rowTab C kpos lpos ms) w4).rows m).length = 24 := by
  rw [sliceSpec_rows]; exact localRowsF_length _ _ _

/-- The box form of a slice leaf is the sum of its items' box forms. -/
lemma boxF_sliceSpec (C : CertD) (coef : ℤ) (kpos lpos : List ℕ) (ms : List ℕ) (m1 m2 m3 : ℕ) (lf : Leaf)
    (w0 w1 w2 w3 w4 : Fin 24) :
    boxF (sliceSpec C coef kpos lpos (rowTab C kpos lpos ms) w4.val) m1 m2 m3 lf w0.val w1.val w2.val w3.val =
      (lf.items.map fun it => boxItem5 C coef kpos lpos lf.m0 m1 m2 m3 (m4Of C it) it w0 w1 w2 w3 w4).sum := by
  unfold boxF boxItem5
  simp only [sliceSpec_rows]
  simp only [sliceSpec, lookTab_rowTab, gv_foldr_map]
  rw [← sum_list1]
  refine Finset.sum_congr rfl fun i0 hi0 => ?_
  rw [← sum_list1]
  refine Finset.sum_congr rfl fun i1 hi1 => ?_
  rw [← sum_list1]
  refine Finset.sum_congr rfl fun i2 hi2 => ?_
  rw [← sum_list1]
  refine Finset.sum_congr rfl fun i3 hi3 => ?_
  rw [mul_list_sum]
  refine congrArg List.sum (List.map_congr_left fun it _ => ?_)
  rw [itemTF5c_gv _ _ _ _ _ _ _ _ _ _ _ _ _ (Finset.mem_range.1 hi0) (Finset.mem_range.1 hi1)
    (Finset.mem_range.1 hi2) (Finset.mem_range.1 hi3)]

/-- Data conditions of one item at tree position `m3 → m2 → m1 → m0` of a slice group (checked by the checker). -/
def itemOK5 (C : CertD) (E0 fam : ℕ) (kpos lpos : List ℕ) (m0 m1 m2 m3 : ℕ) (it : ℕ × ℕ × ℕ) : Bool :=
  let t := C.types.getD it.1 default
  let R := (t.rules.getD it.2.1 []).getD it.2.2 default
  t.mods == [m0, m1, m2, m3, t.mods.getD 4 0] && R.kpos == kpos && R.lpos == lpos && R.fam == fam &&
  (C.mods.getD m0 default).n == C.d && (C.mods.getD m1 default).n == C.d &&
  (C.mods.getD m2 default).n == C.d && (C.mods.getD m3 default).n == C.d &&
  (C.mods.getD (t.mods.getD 4 0) default).n == 2 &&
  (C.Z.getD t.zi default).uent.isEmpty && (C.Z.getD t.zi default).E == E0

/-- Data conditions of a slice group. -/
def grpOK5 (C : CertD) (E0 : ℕ) (G : GrpF) : Bool :=
  G.tree.all fun n3 => n3.kids.all fun n2 => n2.kids.all fun n1 => n1.kids.all fun lf =>
    lf.items.all (itemOK5 C E0 G.fam G.kpos G.lpos lf.m0 n1.m1 n2.m2 n3.m3)

lemma itemOK5_bridge (C : CertD) (hk : C.k = 4) (E0 fam : ℕ) (coef : ℤ) (kpos lpos : List ℕ) (m0 m1 m2 m3 : ℕ)
    (it : ℕ × ℕ × ℕ) (h : itemOK5 C E0 fam kpos lpos m0 m1 m2 m3 it = true) (hd : 0 < C.d)
    (w : Fin (C.k + 1) → Fin 24) :
    ((boxItem5 C coef kpos lpos m0 m1 m2 m3 (m4Of C it) it (w 0) (w 1) (w 2) (w 3) (w 4) : ℤ) : ℚ) =
      coef * 2 ^ E0 * C.blk (C.types.getD it.1 default) it.2.1 it.2.2 w := by
  obtain ⟨ti, r, s⟩ := it
  simp only [itemOK5, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, hkp⟩, hlp⟩, _⟩, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, hu⟩, hE⟩ := h
  rw [← hE]
  exact item5_bridge C hk coef ti r s m0 m1 m2 m3 (m4Of C (ti, r, s)) kpos lpos hm hkp hlp h0 h1 h2 h3 h4 hd hu w

/-- **Group bridge on a slice.** -/
theorem specTree_slicePart (C : CertD) (hk : C.k = 4) (E0 : ℕ) (coef : ℤ) (G : GrpF)
    (hG : grpOK5 C E0 G = true) (hd : 0 < C.d) (w : Fin (C.k + 1) → Fin 24) :
    ((specTree (slicePart C coef (w 4).val G).S G.tree (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) =
      coef * 2 ^ E0 * ((itemsOf G.tree).map fun it => C.blk (C.types.getD it.1 default) it.2.1 it.2.2 w).sum := by
  unfold slicePart
  simp only
  rw [specTree_paths, itemsOf]
  simp only [grpOK5, List.all_eq_true] at hG
  simp only [sum_flatMap_map, cast_list_sum, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun n3 hn3 => ?_)
  refine congrArg List.sum (List.map_congr_left fun n2 hn2 => ?_)
  refine congrArg List.sum (List.map_congr_left fun n1 hn1 => ?_)
  refine congrArg List.sum (List.map_congr_left fun lf hlf => ?_)
  rw [boxF_sliceSpec, cast_list_sum]
  refine congrArg List.sum (List.map_congr_left fun it hit => ?_)
  exact itemOK5_bridge C hk E0 G.fam coef G.kpos G.lpos lf.m0 n1.m1 n2.m2 n3.m3 it
    (hG n3 hn3 n2 hn2 n1 hn1 lf hlf it hit) hd w

end NPT.K4.Route
