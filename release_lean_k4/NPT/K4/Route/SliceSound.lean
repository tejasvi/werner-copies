/-
NPT.K4.Route.SliceSound — soundness of the slice check with offsets: when the check passes, every class sum of the
slice's packed function is the negated initial value (`offAt`) of the accumulator leaf of its class.
-/
import NPT.K4.Route.Slice

namespace NPT.K4.Route

open BigOperators Finset NPT.Cert.Ident

/-- Initial value of the accumulator leaf reached by key `c` (the offset of class `c`). -/
def offAt (t : AT) (c : Nat) : Int := ((t.leaves.getD (t.tgt c) dLeaf).2.1).val

/-- **Routing with offsets.** All flags set and all final leaf sums zero ⇒ the class sums of the routed values are the
negated offsets of their leaves. -/
lemma route_off (vs : List SInt) (cs : List Nat) (t : AT) (hlen : vs.length = cs.length)
    (hall : ∀ j < t.leaves.length, ((routeL vs cs t).leaves.getD j dLeaf).2.2 = true ∧
      ((routeL vs cs t).leaves.getD j dLeaf).2.1.val = 0)
    (q : Nat) (hq : q < vs.length) :
    ∑ q' ∈ range vs.length, (if cs.getD q' 0 = cs.getD q 0 then (vs.getD q' SInt.zero).val else 0) =
      - offAt t (cs.getD q 0) := by
  obtain ⟨_, _, hJ⟩ := routeL_spec vs cs t hlen
  set j := t.tgt (cs.getD q 0) with hj
  have hjl : j < t.leaves.length := AT.tgt_lt t _
  obtain ⟨_, h2, h3, _⟩ := hJ j hjl
  obtain ⟨hok, hzero⟩ := hall j hjl
  have hkey := h3 hok
  have hcq : cs.getD q 0 = (t.leaves.getD j dLeaf).1 := hkey q hq rfl
  have hsum : ∑ q' ∈ range vs.length, (if cs.getD q' 0 = cs.getD q 0 then (vs.getD q' SInt.zero).val else 0) =
      ∑ q' ∈ range vs.length, (if t.tgt (cs.getD q' 0) = j then (vs.getD q' SInt.zero).val else 0) := by
    refine Finset.sum_congr rfl fun q' hq' => ?_
    have hq'l := Finset.mem_range.1 hq'
    by_cases h : t.tgt (cs.getD q' 0) = j
    · rw [if_pos h, if_pos (by rw [hkey q' hq'l h, ← hcq])]
    · have h' : ¬ cs.getD q' 0 = cs.getD q 0 := fun e => h (by rw [e])
      rw [if_neg h, if_neg h']
  rw [hsum]
  unfold offAt
  rw [← hj]
  linarith

/-- **Routing with offsets, by key.** For a key `c` that is the key of its own leaf, the class sum of `c` is the
negated offset of that leaf (zero routed values if `c` does not occur). -/
lemma route_off_key (vs : List SInt) (cs : List Nat) (t : AT) (hlen : vs.length = cs.length)
    (hall : ∀ j < t.leaves.length, ((routeL vs cs t).leaves.getD j dLeaf).2.2 = true ∧
      ((routeL vs cs t).leaves.getD j dLeaf).2.1.val = 0)
    (c : Nat) (hc : (t.leaves.getD (t.tgt c) dLeaf).1 = c) :
    ∑ q' ∈ range vs.length, (if cs.getD q' 0 = c then (vs.getD q' SInt.zero).val else 0) = - offAt t c := by
  obtain ⟨_, _, hJ⟩ := routeL_spec vs cs t hlen
  set j := t.tgt c with hj
  have hjl : j < t.leaves.length := AT.tgt_lt t _
  obtain ⟨_, h2, h3, _⟩ := hJ j hjl
  obtain ⟨hok, hzero⟩ := hall j hjl
  have hkey := h3 hok
  have hsum : ∑ q' ∈ range vs.length, (if cs.getD q' 0 = c then (vs.getD q' SInt.zero).val else 0) =
      ∑ q' ∈ range vs.length, (if t.tgt (cs.getD q' 0) = j then (vs.getD q' SInt.zero).val else 0) := by
    refine Finset.sum_congr rfl fun q' hq' => ?_
    have hq'l := Finset.mem_range.1 hq'
    by_cases h : t.tgt (cs.getD q' 0) = j
    · rw [if_pos h, if_pos (by rw [hkey q' hq'l h, hc])]
    · have h' : ¬ cs.getD q' 0 = c := fun e => h (by rw [e])
      rw [if_neg h, if_neg h']
  rw [hsum]
  unfold offAt
  rw [← hj]
  linarith

/-- **Slice soundness with offsets** (as `family_sound`, for an accumulator with initial values). -/
theorem family_sound_off (b : Nat) (hb : 0 < b) (slices : List SInt) (F : Nat → Nat → Nat → Nat → Int)
    (hS : ∀ w3 < 24, gv slices w3 = ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24,
      F w0 w1 w2 w3 * 2 ^ (b * w0)) * 2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2))
    (hF : ∀ q < 24 * slen, |F (wd q).1 (wd q).2.1 (wd q).2.2.1 (wd q).2.2.2| < 2 ^ (b - 1))
    (cls : List Nat) (hcls : cls.length = 24 * slen) (t : AT)
    (hall : ∀ j < t.leaves.length, ((routeL (digitsOf b slices) cls t).leaves.getD j dLeaf).2.2 = true ∧
      ((routeL (digitsOf b slices) cls t).leaves.getD j dLeaf).2.1.val = 0)
    (q : Nat) (hq : q < 24 * slen) :
    ∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      F (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0) = - offAt t (cls.getD q 0) := by
  have hlen : (digitsOf b slices).length = cls.length := by rw [digitsOf_length, hcls]
  have hR := route_off (digitsOf b slices) cls t hlen hall q (by rw [digitsOf_length]; exact hq)
  have hdl := digitsOf_length b slices
  refine Eq.trans (Finset.sum_congr (by rw [hdl]) fun q' hq' => ?_) hR
  have hq'l : q' < 24 * slen := by rw [← hdl]; exact Finset.mem_range.1 hq'
  by_cases hc : cls.getD q' 0 = cls.getD q 0
  · rw [if_pos hc, if_pos hc, digitsOf_val b hb slices F hS hF q' hq'l]
  · rw [if_neg hc, if_neg hc]

/-- **Soundness of the slice check.** -/
theorem sliceCheck_sound (b : Nat) (ps : List Part) (cls : List Nat) (t0 : AT) (h : sliceCheck b ps cls t0 = true)
    (hS : ∀ P ∈ ps, ∀ m, (P.S.rows m).length = 24) (q : Nat) (hq : q < 24 * slen) :
    ∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      partsF ps (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0) = - offAt t0 (cls.getD q 0) := by
  unfold sliceCheck at h
  rw [partsSlicesA_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hb, hB⟩, hcl⟩, hall⟩ := h
  refine family_sound_off b hb (partsSlices b ps) (partsF ps) (partsSlices_gv b ps hS) ?_ cls hcl t0 ?_ q hq
  · intro q' hq'
    have h24 : ∀ x : Nat, x % 24 < 24 := fun x => Nat.mod_lt _ (by norm_num)
    have hw3 : q' / 13824 < 24 := by unfold slen at hq'; omega
    refine lt_of_le_of_lt (partsF_abs ps hS _ _ _ _ (h24 _) (h24 _) (h24 _) hw3) ?_
    exact_mod_cast hB
  · intro j hj
    have hj' : j < (routeL (digitsOf b (partsSlices b ps)) cls t0).leaves.length := by
      rw [(routeL_spec _ _ t0 (by rw [digitsOf_length, hcl])).1]; exact hj
    have := hall _ (getD_mem_of_lt _ j dLeaf hj')
    exact ⟨this.1, SInt.val_eq_zero_of_mag this.2⟩

/-- **Soundness of the slice check, by key.** For a key `c` of its own accumulator leaf, the class sum of `c` over the
slice is `−offAt t0 c`. -/
theorem sliceCheck_sound_key (b : Nat) (ps : List Part) (cls : List Nat) (t0 : AT)
    (h : sliceCheck b ps cls t0 = true) (hS : ∀ P ∈ ps, ∀ m, (P.S.rows m).length = 24)
    (c : Nat) (hc : (t0.leaves.getD (t0.tgt c) dLeaf).1 = c) :
    ∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = c then
      partsF ps (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0) = - offAt t0 c := by
  unfold sliceCheck at h
  rw [partsSlicesA_eq] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hb, hB⟩, hcl⟩, hall⟩ := h
  have hF : ∀ q < 24 * slen, |partsF ps (wd q).1 (wd q).2.1 (wd q).2.2.1 (wd q).2.2.2| < 2 ^ (b - 1) := by
    intro q' hq'
    have h24 : ∀ x : Nat, x % 24 < 24 := fun x => Nat.mod_lt _ (by norm_num)
    have hw3 : q' / 13824 < 24 := by unfold slen at hq'; omega
    refine lt_of_le_of_lt (partsF_abs ps hS _ _ _ _ (h24 _) (h24 _) (h24 _) hw3) ?_
    exact_mod_cast hB
  have hall' : ∀ j < t0.leaves.length,
      ((routeL (digitsOf b (partsSlices b ps)) cls t0).leaves.getD j dLeaf).2.2 = true ∧
      ((routeL (digitsOf b (partsSlices b ps)) cls t0).leaves.getD j dLeaf).2.1.val = 0 := by
    intro j hj
    have hj' : j < (routeL (digitsOf b (partsSlices b ps)) cls t0).leaves.length := by
      rw [(routeL_spec _ _ t0 (by rw [digitsOf_length, hcl])).1]; exact hj
    have := hall _ (getD_mem_of_lt _ j dLeaf hj')
    exact ⟨this.1, SInt.val_eq_zero_of_mag this.2⟩
  have hlen : (digitsOf b (partsSlices b ps)).length = cls.length := by rw [digitsOf_length, hcl]
  have hR := route_off_key (digitsOf b (partsSlices b ps)) cls t0 hlen hall' c hc
  have hdl := digitsOf_length b (partsSlices b ps)
  refine Eq.trans (Finset.sum_congr (by rw [hdl]) fun q' hq' => ?_) hR
  have hq'l : q' < 24 * slen := by rw [← hdl]; exact Finset.mem_range.1 hq'
  by_cases hcq : cls.getD q' 0 = c
  · rw [if_pos hcq, if_pos hcq,
      digitsOf_val b hb (partsSlices b ps) (partsF ps) (partsSlices_gv b ps hS) hF q' hq'l]
  · rw [if_neg hcq, if_neg hcq]

end NPT.K4.Route
