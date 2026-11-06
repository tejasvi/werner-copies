/-
NPT.Cert.Ident.Family — from packed slices to vanishing class sums.
If 24 slices pack a word function `F` (digits `|F| < 2^(b-1)`), then routing the extracted digits by `cls`
with all leaf flags set and all leaf sums zero proves `Σ_{q' : cls q' = cls q} F (word q') = 0` for every word `q`.
-/
import NPT.Cert.Ident.Pipe
import NPT.Cert.Ident.Extract
import NPT.Cert.Ident.Route
import NPT.Cert.Ident.Bound

open BigOperators Finset

namespace NPT.Cert.Ident

/-- Word of position `q = w3·13824 + w2·576 + w1·24 + w0`. -/
def wd (q : Nat) : Nat × Nat × Nat × Nat := (q % 24, q / 24 % 24, q / 576 % 24, q / 13824)

lemma sum_range_mul (f : Nat → Int) (m : Nat) : ∀ n, ∑ p ∈ range (n * m), f p = ∑ i ∈ range n, ∑ j ∈ range m, f (i * m + j)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul f m n, Finset.sum_range_succ]

lemma pack3 (b : Nat) (g : Nat → Nat → Nat → Int) :
    ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24, g w0 w1 w2 * 2 ^ (b * w0)) * 2 ^ (24 * b * w1)) *
      2 ^ (576 * b * w2) = ∑ p ∈ range slen, g (p % 24) (p / 24 % 24) (p / 576) * 2 ^ (b * p) := by
  rw [show slen = 24 * 576 by rfl, sum_range_mul _ 576 24]
  refine Finset.sum_congr rfl fun w2 hw2 => ?_
  rw [show (576 : Nat) = 24 * 24 by rfl, sum_range_mul _ 24 24, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w1 hw1 => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w0 hw0 => ?_
  have h0 := Finset.mem_range.1 hw0; have h1 := Finset.mem_range.1 hw1; have h2 := Finset.mem_range.1 hw2
  have e0 : (w2 * (24 * 24) + (w1 * 24 + w0)) % 24 = w0 := by omega
  have e1 : (w2 * (24 * 24) + (w1 * 24 + w0)) / 24 % 24 = w1 := by omega
  have e2 : (w2 * (24 * 24) + (w1 * 24 + w0)) / 576 = w2 := by omega
  rw [e0, e1, e2, mul_assoc, ← pow_add, mul_assoc, ← pow_add]
  congr 2; ring


lemma slice_digits (b : Nat) (hb : 0 < b) (s : SInt) (d : Nat → Int) (hd : ∀ p < slen, |d p| < 2 ^ (b - 1))
    (hs : s.val = ∑ p ∈ range slen, d p * 2 ^ (b * p)) :
    (extL b 15 slen (fieldNat (offL b slen) s) []).map (unfield (1 <<< (b - 1))) =
      (List.range slen).map fun p => unfield (1 <<< (b - 1)) (fld b (d p)) := by
  rw [fieldNat_eq b slen hb s d hd hs,
    extL_eq b 15 slen _ [] (fun p => fld b (d p)) (by decide) (by decide) (fun p hp => fld_lt b hb _ (hd p hp)) rfl,
    List.append_nil, List.map_map]
  rfl

lemma flatMap_getD {α β : Type} (g : α → List β) (m : Nat) (hg : ∀ x, (g x).length = m) (d : β) :
    ∀ (L : List α) (dflt : α) (i j : Nat), i < L.length → j < m →
      (L.flatMap g).getD (i * m + j) d = (g (L.getD i dflt)).getD j d
  | [], _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | x :: L, dflt, 0, j, _, hj => by
    simp only [List.flatMap_cons, zero_mul, zero_add, List.getD_cons_zero]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hg]; exact hj), ← List.getD_eq_getElem?_getD]
  | x :: L, dflt, i + 1, j, hi, hj => by
    simp only [List.flatMap_cons, List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hg]; nlinarith), hg,
      show (i + 1) * m + j - m = i * m + j by rw [Nat.succ_mul]; omega, ← List.getD_eq_getElem?_getD]
    exact flatMap_getD g m hg d L dflt i j (by simpa using hi) hj

/-- **Digits of packed slices.** -/
lemma digitsOf_val (b : Nat) (hb : 0 < b) (slices : List SInt) (F : Nat → Nat → Nat → Nat → Int)
    (hS : ∀ w3 < 24, gv slices w3 = ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24,
      F w0 w1 w2 w3 * 2 ^ (b * w0)) * 2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2))
    (hF : ∀ q < 24 * slen, |F (wd q).1 (wd q).2.1 (wd q).2.2.1 (wd q).2.2.2| < 2 ^ (b - 1))
    (q : Nat) (hq : q < 24 * slen) :
    ((digitsOf b slices).getD q SInt.zero).val = F (wd q).1 (wd q).2.1 (wd q).2.2.1 (wd q).2.2.2 := by
  set w3 := q / slen with hw3
  set p := q % slen with hp
  have hq' : q = w3 * slen + p := by rw [hw3, hp]; exact (Nat.div_add_mod' q slen).symm
  have hw3l : w3 < 24 := by rw [hw3]; exact Nat.div_lt_of_lt_mul (by simpa [mul_comm] using hq)
  have hpl : p < slen := Nat.mod_lt _ (by decide)
  have hlen : ∀ w : Nat, ((extL b 15 slen (fieldNat (offL b slen) (slices.getD w SInt.zero)) []).map
      (unfield (1 <<< (b - 1)))).length = slen := by
    intro w; rw [List.length_map, extL_length b 15 slen _ [] (by decide) (by decide)]; rfl
  unfold digitsOf
  rw [hq', flatMap_getD _ slen hlen SInt.zero (List.range 24) 0 w3 p (by simpa using hw3l) hpl]
  rw [show (List.range 24).getD w3 0 = w3 by
    rw [List.getD_eq_getElem?_getD, List.getElem?_range hw3l]; rfl]
  set d : Nat → Int := fun p => F (p % 24) (p / 24 % 24) (p / 576) w3 with hd
  have hdb : ∀ p' < slen, |d p'| < 2 ^ (b - 1) := by
    intro p' hp'
    have := hF (w3 * slen + p') (by unfold slen at hp' ⊢; omega)
    have e0 : (w3 * slen + p') % 24 = p' % 24 := by unfold slen; omega
    have e1 : (w3 * slen + p') / 24 % 24 = p' / 24 % 24 := by unfold slen; omega
    have e2 : (w3 * slen + p') / 576 % 24 = p' / 576 := by unfold slen at hp' ⊢; omega
    have e3 : (w3 * slen + p') / 13824 = w3 := by unfold slen at hp' ⊢; omega
    simpa [wd, e0, e1, e2, e3, hd] using this
  have hsv : (slices.getD w3 SInt.zero).val = ∑ p' ∈ range slen, d p' * 2 ^ (b * p') := by
    have := hS w3 hw3l
    rw [pack3] at this
    exact this
  rw [slice_digits b hb _ d hdb hsv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hpl]
  simp only [Option.map_some, Option.getD_some]
  rw [unfield_fld b _ (hdb p hpl)]
  have e0 : (w3 * slen + p) % 24 = p % 24 := by unfold slen; omega
  have e1 : (w3 * slen + p) / 24 % 24 = p / 24 % 24 := by unfold slen; omega
  have e2 : (w3 * slen + p) / 576 % 24 = p / 576 := by unfold slen at hpl ⊢; omega
  have e3 : (w3 * slen + p) / 13824 = w3 := by unfold slen at hpl ⊢; omega
  simp only [wd, e0, e1, e2, e3, hd]


lemma digitsOf_length (b : Nat) (slices : List SInt) : (digitsOf b slices).length = 24 * slen := by
  unfold digitsOf
  rw [List.length_flatMap]
  simp only [List.length_map, extL_length b 15 slen _ [] (by decide) (by decide), List.length_nil, add_zero]
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]

/-- Routing corollary: all flags set and all leaf sums zero ⇒ class sums of the routed values vanish. -/
lemma route_zero (vs : List SInt) (cs : List Nat) (t : AT) (hlen : vs.length = cs.length)
    (h0 : ∀ j < t.leaves.length, ((t.leaves.getD j dLeaf).2.1).val = 0)
    (hall : ∀ j < t.leaves.length, ((routeL vs cs t).leaves.getD j dLeaf).2.2 = true ∧
      ((routeL vs cs t).leaves.getD j dLeaf).2.1.val = 0)
    (q : Nat) (hq : q < vs.length) :
    ∑ q' ∈ range vs.length, (if cs.getD q' 0 = cs.getD q 0 then (vs.getD q' SInt.zero).val else 0) = 0 := by
  obtain ⟨_, _, hJ⟩ := routeL_spec vs cs t hlen
  set j := t.tgt (cs.getD q 0) with hj
  have hjl : j < t.leaves.length := AT.tgt_lt t _
  obtain ⟨_, h2, h3, _⟩ := hJ j hjl
  obtain ⟨hok, hzero⟩ := hall j hjl
  have hkey := h3 hok
  have hcq : cs.getD q 0 = (t.leaves.getD j dLeaf).1 := hkey q hq rfl
  rw [hzero, h0 j hjl, zero_add] at h2
  refine Eq.trans (Finset.sum_congr rfl fun q' hq' => ?_) h2.symm
  have hq'l := Finset.mem_range.1 hq'
  by_cases h : t.tgt (cs.getD q' 0) = j
  · rw [if_pos h, if_pos (by rw [hkey q' hq'l h, ← hcq])]
  · have h' : ¬ cs.getD q' 0 = cs.getD q 0 := fun e => h (by rw [e])
    rw [if_neg h, if_neg h']

/-- **Family soundness.** If the slices pack `F` with digits below `2^(b-1)` and routing their digits by `cls`
leaves every flag set and every leaf sum zero, then every class sum of `F` vanishes. -/
theorem family_sound (b : Nat) (hb : 0 < b) (slices : List SInt) (F : Nat → Nat → Nat → Nat → Int)
    (hS : ∀ w3 < 24, gv slices w3 = ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24,
      F w0 w1 w2 w3 * 2 ^ (b * w0)) * 2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2))
    (hF : ∀ q < 24 * slen, |F (wd q).1 (wd q).2.1 (wd q).2.2.1 (wd q).2.2.2| < 2 ^ (b - 1))
    (cls : List Nat) (hcls : cls.length = 24 * slen) (t : AT)
    (h0 : ∀ j < t.leaves.length, ((t.leaves.getD j dLeaf).2.1).val = 0)
    (hall : ∀ j < t.leaves.length, ((routeL (digitsOf b slices) cls t).leaves.getD j dLeaf).2.2 = true ∧
      ((routeL (digitsOf b slices) cls t).leaves.getD j dLeaf).2.1.val = 0)
    (q : Nat) (hq : q < 24 * slen) :
    ∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      F (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0) = 0 := by
  have hlen : (digitsOf b slices).length = cls.length := by rw [digitsOf_length, hcls]
  have hR := route_zero (digitsOf b slices) cls t hlen h0 hall q (by rw [digitsOf_length]; exact hq)
  have hdl := digitsOf_length b slices
  refine Eq.trans (Finset.sum_congr (by rw [hdl]) fun q' hq' => ?_) hR
  have hq'l : q' < 24 * slen := by rw [← hdl]; exact Finset.mem_range.1 hq'
  by_cases hc : cls.getD q' 0 = cls.getD q 0
  · rw [if_pos hc, if_pos hc, digitsOf_val b hb slices F hS hF q' hq'l]
  · rw [if_neg hc, if_neg hc]


lemma SInt.val_eq_zero_of_mag {a : SInt} (h : a.mag = 0) : a.val = 0 := by
  rcases a with ⟨_ | _, m⟩ <;> simp_all [SInt.val]

/-- The summed word values of the parts. -/
def partsF (ps : List Part) (w0 w1 w2 w3 : Nat) : Int := (ps.map fun P => specTree P.S P.tree w0 w1 w2 w3).sum

lemma partsSlices_gv (b : Nat) (ps : List Part) (hS : ∀ P ∈ ps, ∀ m, (P.S.rows m).length = 24) (w3 : Nat)
    (hw : w3 < 24) : gv (partsSlices b ps) w3 = ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24,
      partsF ps w0 w1 w2 w3 * 2 ^ (b * w0)) * 2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2) := by
  unfold partsSlices
  rw [gv_foldr_map]
  rw [show (ps.map fun P => gv (evalTree P.S b P.tree) w3) = (ps.map fun P =>
      ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24, specTree P.S P.tree w0 w1 w2 w3 * 2 ^ (b * w0)) *
        2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2)) from
      List.map_congr_left fun P hP => evalTree_gv P.S b (hS P hP) P.tree w3 hw,
    list_sum_map_sum]
  refine Finset.sum_congr rfl fun w2 _ => ?_
  rw [list_sum_map_mul_right, list_sum_map_sum]
  congr 1
  refine Finset.sum_congr rfl fun w1 _ => ?_
  rw [list_sum_map_mul_right, list_sum_map_sum]
  congr 1
  refine Finset.sum_congr rfl fun w0 _ => ?_
  rw [list_sum_map_mul_right]; rfl

lemma partsF_abs (ps : List Part) (hS : ∀ P ∈ ps, ∀ m, (P.S.rows m).length = 24) (w0 w1 w2 w3 : Nat)
    (hw0 : w0 < 24) (hw1 : w1 < 24) (hw2 : w2 < 24) (hw3 : w3 < 24) :
    |partsF ps w0 w1 w2 w3| ≤ (partsBound ps : Int) := by
  unfold partsF partsBound
  exact abs_list_sum_le _ _ _ fun P hP => specTree_abs P.S (hS P hP) P.tree _ _ _ _ hw0 hw1 hw2 hw3

/-- **Soundness of the family check.** -/
theorem famCheck_sound (b : Nat) (ps : List Part) (cls : List Nat) (t0 : AT) (h : famCheck b ps cls t0 = true)
    (hS : ∀ P ∈ ps, ∀ m, (P.S.rows m).length = 24) (q : Nat) (hq : q < 24 * slen) :
    ∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      partsF ps (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0) = 0 := by
  unfold famCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hb, hB⟩, hcl⟩, h0⟩, hall⟩ := h
  refine family_sound b hb (partsSlices b ps) (partsF ps) (partsSlices_gv b ps hS) ?_ cls hcl t0 ?_ ?_ q hq
  · intro q' hq'
    have h24 : ∀ x : Nat, x % 24 < 24 := fun x => Nat.mod_lt _ (by norm_num)
    have hw3 : q' / 13824 < 24 := by unfold slen at hq'; omega
    refine lt_of_le_of_lt (partsF_abs ps hS _ _ _ _ (h24 _) (h24 _) (h24 _) hw3) ?_
    exact_mod_cast hB
  · intro j hj
    exact SInt.val_eq_zero_of_mag (h0 _ (getD_mem_of_lt _ j dLeaf hj))
  · intro j hj
    have hj' : j < (routeL (digitsOf b (partsSlices b ps)) cls t0).leaves.length := by
      rw [(routeL_spec _ _ t0 (by rw [digitsOf_length, hcl])).1]; exact hj
    have := hall _ (getD_mem_of_lt _ j dLeaf hj')
    exact ⟨this.1, SInt.val_eq_zero_of_mag this.2⟩

end NPT.Cert.Ident
