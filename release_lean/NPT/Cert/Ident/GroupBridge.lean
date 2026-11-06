/-
NPT.Cert.Ident.GroupBridge — the multilinear form of a native rule group is `coef · 2Lden · Σ_items blk`.
-/
import NPT.Cert.Ident.ItemBridge

open BigOperators Finset NPT.Cert.Sem

namespace NPT.Cert.Ident

/-- A rule group for the native checker: family, entry rule (position codes), box tree. -/
structure GrpF where
  fam : ℕ
  kpos : List ℕ
  lpos : List ℕ
  tree : List Nd3
  deriving Inhabited

/-- The box form of a native rule-group leaf is the sum of its items' box forms. -/
lemma boxF_ruleSpecF (C : CertD) (zmul : ℕ) (coef : ℤ) (kpos lpos : List ℕ) (m1 m2 m3 : ℕ) (lf : Leaf)
    (w0 w1 w2 w3 : Fin 24) :
    boxF (ruleSpecF C zmul coef kpos lpos) m1 m2 m3 lf w0.val w1.val w2.val w3.val =
      (lf.items.map fun it => boxItem C zmul coef kpos lpos lf.m0 m1 m2 m3 it w0 w1 w2 w3).sum := by
  unfold boxF boxItem
  simp only [ruleSpecF, gv_foldr_map]
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
  rw [itemTF_gv _ _ _ _ _ _ _ _ _ _ _ _ (Finset.mem_range.1 hi0) (Finset.mem_range.1 hi1)
    (Finset.mem_range.1 hi2) (Finset.mem_range.1 hi3)]


/-- Data conditions of one item in a group (checked by the checker). -/
def itemOK (C : CertD) (zmul fam : ℕ) (kpos lpos : List ℕ) (m0 m1 m2 m3 : ℕ) (it : ℕ × ℕ × ℕ) : Bool :=
  let t := C.types.getD it.1 default
  let R := (t.rules.getD it.2.1 []).getD it.2.2 default
  t.mods == [m0, m1, m2, m3] && R.kpos == kpos && R.lpos == lpos && R.fam == fam &&
  (C.mods.getD m0 default).n == C.d && (C.mods.getD m1 default).n == C.d &&
  (C.mods.getD m2 default).n == C.d && (C.mods.getD m3 default).n == 2 &&
  2 * C.Lden == zmul * 2 ^ (C.Z.getD t.zi default).E

def grpOK (C : CertD) (zmul : ℕ) (G : GrpF) : Bool :=
  G.tree.all fun n3 => n3.kids.all fun n2 => n2.kids.all fun n1 => n1.kids.all fun lf =>
    lf.items.all (itemOK C zmul G.fam G.kpos G.lpos lf.m0 n1.m1 n2.m2 n3.m3)

/-- All items of a group. -/
def itemsOf (tree : List Nd3) : List (ℕ × ℕ × ℕ) :=
  tree.flatMap fun n3 => n3.kids.flatMap fun n2 => n2.kids.flatMap fun n1 => n1.kids.flatMap fun lf => lf.items

lemma sum_flatMap_map {α β : Type*} (L : List α) (g : α → List β) (f : β → ℚ) :
    ((L.flatMap g).map f).sum = (L.map fun x => ((g x).map f).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

lemma cast_list_sum {α : Type*} (L : List α) (f : α → ℤ) : (((L.map f).sum : ℤ) : ℚ) = (L.map fun x => (f x : ℚ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih]

lemma itemOK_bridge (C : CertD) (hk : C.k = 3) (zmul fam : ℕ) (coef : ℤ) (kpos lpos : List ℕ) (m0 m1 m2 m3 : ℕ)
    (it : ℕ × ℕ × ℕ) (h : itemOK C zmul fam kpos lpos m0 m1 m2 m3 it = true) (hd : 0 < C.d) (hL : 0 < C.Lden)
    (w : Fin (C.k + 1) → Fin 24) :
    ((boxItem C zmul coef kpos lpos m0 m1 m2 m3 it (w 0) (w 1) (w 2) (w 3) : ℤ) : ℚ) =
      coef * (2 * C.Lden) * C.blk (C.types.getD it.1 default) it.2.1 it.2.2 w := by
  obtain ⟨ti, r, s⟩ := it
  simp only [itemOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hm, hkp⟩, hlp⟩, _⟩, h0⟩, h1⟩, h2⟩, h3⟩, hz⟩ := h
  exact item_bridge C hk zmul coef ti r s m0 m1 m2 m3 kpos lpos hm hkp hlp h0 h1 h2 h3 hd hz hL w

/-- **Group bridge.** -/
theorem specTree_ruleSpecF (C : CertD) (hk : C.k = 3) (zmul : ℕ) (coef : ℤ) (G : GrpF)
    (hG : grpOK C zmul G = true) (hd : 0 < C.d) (hL : 0 < C.Lden) (w : Fin (C.k + 1) → Fin 24) :
    ((specTree (ruleSpecF C zmul coef G.kpos G.lpos) G.tree (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) =
      coef * (2 * C.Lden) * ((itemsOf G.tree).map fun it => C.blk (C.types.getD it.1 default) it.2.1 it.2.2 w).sum := by
  rw [specTree_paths, itemsOf]
  simp only [grpOK, List.all_eq_true] at hG
  simp only [sum_flatMap_map, cast_list_sum, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun n3 hn3 => ?_)
  refine congrArg List.sum (List.map_congr_left fun n2 hn2 => ?_)
  refine congrArg List.sum (List.map_congr_left fun n1 hn1 => ?_)
  refine congrArg List.sum (List.map_congr_left fun lf hlf => ?_)
  rw [boxF_ruleSpecF, cast_list_sum]
  refine congrArg List.sum (List.map_congr_left fun it hit => ?_)
  exact itemOK_bridge C hk zmul G.fam coef G.kpos G.lpos lf.m0 n1.m1 n2.m2 n3.m3 it
    (hG n3 hn3 n2 hn2 n1 hn1 lf hlf it hit) hd hL w

end NPT.Cert.Ident
