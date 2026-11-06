/-
NPT.Cert.Ident.KRRoute — correctness of the routing with counts (`NPT.Cert.KR.RT`, `KRLib`) for the mod-p
kernel identity check (mirroring `Route.lean` and `Family.lean`):
* `routeR_spec`: after `routeR vs cs t`, leaf `j` holds its initial sum plus the sum of the values whose key is routed to
  `j`, its initial count plus their number, and its flag is set only if each of those keys equals the leaf's key;
* `okMod_sound`: if `RT.okMod p h` holds after routing from `toRT t0`, then for every position `q` the values with the
  same key as `q` sum to their count times `h`, modulo `p`.
-/
import NPT.Cert.Ident.KRLib
import NPT.Cert.Ident.Route

open BigOperators Finset NPT.Cert.Ident

namespace NPT.Cert.KR

/-! ### Leaves and targets -/

/-- Leaves in order: `(key, sum, count, flag)`. -/
def RT.leaves : RT → List (ℕ × ℕ × ℕ × Bool)
  | .leaf k s c ok => [(k, s, c, ok)]
  | .node _ l r => l.leaves ++ r.leaves

/-- Index (in `leaves`) of the leaf reached by `key`. -/
def RT.tgt : RT → ℕ → ℕ
  | .leaf _ _ _ _, _ => 0
  | .node k l r, key => if key < k then l.tgt key else l.leaves.length + r.tgt key

/-- The leaf update performed by `RT.ins`. -/
def leafUpdR (key v : ℕ) (e : ℕ × ℕ × ℕ × Bool) : ℕ × ℕ × ℕ × Bool :=
  (e.1, e.2.1 + v, e.2.2.1 + 1, e.2.2.2 && Nat.beq e.1 key)

/-- Default leaf entry. -/
def dLeafR : ℕ × ℕ × ℕ × Bool := (0, 0, 0, true)

lemma RT.frc_eq (t : RT) (k : RT → RT) : RT.frc t k = k t := by cases t <;> rfl

lemma RT.ins_leaf (k s c : ℕ) (ok : Bool) (key v : ℕ) :
    RT.ins (RT.leaf k s c ok) key v = RT.leaf k (s + v) (c + 1) (ok && Nat.beq k key) := by
  cases ok <;> rfl

lemma RT.ins_node (k : ℕ) (l r : RT) (key v : ℕ) :
    RT.ins (RT.node k l r) key v =
      if key < k then RT.node k (RT.ins l key v) r else RT.node k l (RT.ins r key v) := by
  show @Bool.rec (fun _ => RT) (RT.frc (RT.ins r key v) (fun r' => RT.node k l r'))
      (RT.frc (RT.ins l key v) (fun l' => RT.node k l' r)) (Nat.blt key k) = _
  rw [RT.frc_eq, RT.frc_eq]
  have hb : Nat.blt key k = true ↔ key < k := by rw [Nat.blt_eq]
  cases h : Nat.blt key k
  · have : ¬ key < k := fun hlt => by have := hb.2 hlt; rw [h] at this; cases this
    rw [ite_eq_right this]
  · rw [ite_eq_left (hb.1 h)]

lemma routeR_nil (cs : List ℕ) (t : RT) : routeR [] cs t = t := rfl

lemma routeR_cons_nil (v : ℕ) (vs : List ℕ) (t : RT) : routeR (v :: vs) [] t = t := rfl

lemma routeR_cons_cons (v : ℕ) (vs : List ℕ) (c : ℕ) (cs : List ℕ) (t : RT) :
    routeR (v :: vs) (c :: cs) t = routeR vs cs (RT.ins t c v) := by
  show RT.frc (RT.ins t c v) (routeR vs cs) = _
  rw [RT.frc_eq]

lemma RT.leaves_pos : ∀ (t : RT), 0 < t.leaves.length
  | .leaf _ _ _ _ => by simp [RT.leaves]
  | .node _ l r => by simp only [RT.leaves, List.length_append]; have := RT.leaves_pos l; omega

lemma RT.tgt_lt : ∀ (t : RT) (key : ℕ), t.tgt key < t.leaves.length
  | .leaf _ _ _ _, _ => by simp [RT.tgt, RT.leaves]
  | .node k l r, key => by
    simp only [RT.tgt, RT.leaves, List.length_append]
    split_ifs
    · have := RT.tgt_lt l key; omega
    · have := RT.tgt_lt r key; omega

/-- `ins` changes exactly the target leaf. -/
lemma RT.leaves_ins : ∀ (t : RT) (key v : ℕ), (t.ins key v).leaves = updAt t.leaves (t.tgt key) (leafUpdR key v)
  | .leaf k s c ok, key, v => by simp [RT.ins_leaf, RT.leaves, RT.tgt, updAt, leafUpdR]
  | .node k l r, key, v => by
    rw [RT.ins_node]
    simp only [RT.tgt]
    split_ifs with h
    · simp only [RT.leaves]
      rw [RT.leaves_ins l key v, updAt_append_left _ _ _ _ (RT.tgt_lt l key)]
    · simp only [RT.leaves]
      rw [RT.leaves_ins r key v, updAt_append_right]

lemma RT.leaves_length_ins (t : RT) (key v : ℕ) : (t.ins key v).leaves.length = t.leaves.length := by
  rw [RT.leaves_ins, updAt_length]

/-- `ins` preserves the routing (shape and node keys). -/
lemma RT.tgt_ins : ∀ (t : RT) (key key' v : ℕ), (t.ins key v).tgt key' = t.tgt key'
  | .leaf _ _ _ _, _, _, _ => by simp [RT.ins_leaf, RT.tgt]
  | .node k l r, key, key', v => by
    rw [RT.ins_node]
    split_ifs with h
    · simp only [RT.tgt]
      rw [RT.tgt_ins l key key' v, RT.leaves_length_ins]
    · simp only [RT.tgt]
      rw [RT.tgt_ins r key key' v]

/-! ### The routing invariant -/

/-- **Routing invariant.** Leaf `j` of `routeR vs cs t` keeps its key; its sum and count grow by the values routed to
it and their number; its flag stays set only if each key routed to it equals its key (and it was set before). -/
theorem routeR_spec : ∀ (vs cs : List ℕ) (t : RT), vs.length = cs.length →
    (routeR vs cs t).leaves.length = t.leaves.length ∧
    (∀ key, (routeR vs cs t).tgt key = t.tgt key) ∧
    ∀ j < t.leaves.length,
      ((routeR vs cs t).leaves.getD j dLeafR).1 = (t.leaves.getD j dLeafR).1 ∧
      ((routeR vs cs t).leaves.getD j dLeafR).2.1 = (t.leaves.getD j dLeafR).2.1 +
        ∑ q ∈ range vs.length, (if t.tgt (cs.getD q 0) = j then vs.getD q 0 else 0) ∧
      ((routeR vs cs t).leaves.getD j dLeafR).2.2.1 = (t.leaves.getD j dLeafR).2.2.1 +
        ∑ q ∈ range vs.length, (if t.tgt (cs.getD q 0) = j then 1 else 0) ∧
      (((routeR vs cs t).leaves.getD j dLeafR).2.2.2 = true →
        ∀ q < vs.length, t.tgt (cs.getD q 0) = j → cs.getD q 0 = (t.leaves.getD j dLeafR).1) ∧
      (((routeR vs cs t).leaves.getD j dLeafR).2.2.2 = true → (t.leaves.getD j dLeafR).2.2.2 = true)
  | [], [], t, _ => by
    refine ⟨rfl, fun _ => rfl, fun j _ => ⟨rfl, by simp [routeR_nil], by simp [routeR_nil],
      fun _ q hq => absurd hq (Nat.not_lt_zero _), fun h => h⟩⟩
  | v :: vs, c :: cs, t, hlen => by
    have hlen' : vs.length = cs.length := by simpa using hlen
    obtain ⟨hL, hT, hJ⟩ := routeR_spec vs cs (t.ins c v) hlen'
    rw [routeR_cons_cons]
    have hL1 := RT.leaves_length_ins t c v
    refine ⟨by rw [hL, hL1], fun key => by rw [hT, RT.tgt_ins], fun j hj => ?_⟩
    have hj' : j < (t.ins c v).leaves.length := by rw [hL1]; exact hj
    obtain ⟨h1, h2, h3, h4, h5⟩ := hJ j hj'
    have hget : (t.ins c v).leaves.getD j dLeafR =
        if j = t.tgt c then leafUpdR c v (t.leaves.getD j dLeafR) else t.leaves.getD j dLeafR := by
      rw [RT.leaves_ins, updAt_getD _ _ _ _ _ (RT.tgt_lt t c)]
    simp only [RT.tgt_ins] at h2 h3 h4
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h1, hget]; split_ifs <;> rfl
    · rw [h2, hget, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      by_cases hc : j = t.tgt c
      · rw [ite_eq_left hc, ite_eq_left hc.symm]
        simp only [leafUpdR]
        ring
      · rw [ite_eq_right hc, ite_eq_right (Ne.symm hc), add_zero]
    · rw [h3, hget, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      by_cases hc : j = t.tgt c
      · rw [ite_eq_left hc, ite_eq_left hc.symm]
        simp only [leafUpdR]
        ring
      · rw [ite_eq_right hc, ite_eq_right (Ne.symm hc), add_zero]
    · intro hok q hq htq
      rcases q with _ | q
      · simp only [List.getD_cons_zero] at htq ⊢
        have hflag := h5 hok
        rw [hget, ite_eq_left htq.symm] at hflag
        simp only [leafUpdR, Bool.and_eq_true] at hflag
        exact (Nat.eq_of_beq_eq_true hflag.2).symm
      · simp only [List.getD_cons_succ] at htq ⊢
        have := h4 hok q (by simpa using hq) htq
        rw [this, hget]
        split_ifs <;> rfl
    · intro hok
      have hflag := h5 hok
      rw [hget] at hflag
      split_ifs at hflag
      · simp only [leafUpdR, Bool.and_eq_true] at hflag; exact hflag.1
      · exact hflag
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-! ### The initial tree and the check -/

lemma toRT_leaves : ∀ (t0 : AT), (toRT t0).leaves = t0.leaves.map fun e => (e.1, 0, 0, true)
  | .leaf k _ _ => by simp [toRT, RT.leaves, AT.leaves]
  | .node k l r => by simp [toRT, RT.leaves, AT.leaves, toRT_leaves l, toRT_leaves r]

lemma toRT_tgt : ∀ (t0 : AT) (key : ℕ), (toRT t0).tgt key = t0.tgt key
  | .leaf _ _ _, _ => by simp [toRT, RT.tgt, AT.tgt]
  | .node k l r, key => by
    simp only [toRT, RT.tgt, AT.tgt, toRT_tgt l key, toRT_tgt r key, toRT_leaves, List.length_map]

lemma toRT_getD (t0 : AT) (j : ℕ) (hj : j < t0.leaves.length) :
    (toRT t0).leaves.getD j dLeafR = ((t0.leaves.getD j dLeaf).1, 0, 0, true) := by
  rw [toRT_leaves, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

lemma RT.okMod_leaf (p h k s c : ℕ) (ok : Bool) :
    RT.okMod p h (RT.leaf k s c ok) = (ok && Nat.beq (s % p) ((c * h) % p)) := by
  cases ok <;> rfl

lemma RT.okMod_node (p h k : ℕ) (l r : RT) :
    RT.okMod p h (RT.node k l r) = (RT.okMod p h l && RT.okMod p h r) := by
  show @Bool.rec (fun _ => Bool) false (RT.okMod p h r) (RT.okMod p h l) = _
  cases RT.okMod p h l <;> rfl

/-- `okMod` holds iff every leaf is flagged and its sum is its count times `h`, mod `p`. -/
lemma RT.okMod_iff (p h : ℕ) : ∀ (t : RT), RT.okMod p h t = true ↔
    ∀ e ∈ t.leaves, e.2.2.2 = true ∧ e.2.1 % p = (e.2.2.1 * h) % p
  | .leaf k s c ok => by
    rw [RT.okMod_leaf]
    simp only [RT.leaves, List.mem_singleton, forall_eq, Bool.and_eq_true]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, Nat.eq_of_beq_eq_true h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h2]; exact Nat.beq_refl _⟩
  | .node k l r => by
    rw [RT.okMod_node, Bool.and_eq_true, RT.okMod_iff p h l, RT.okMod_iff p h r]
    simp only [RT.leaves, List.mem_append]
    constructor
    · rintro ⟨hl, hr⟩ e (he | he)
      · exact hl e he
      · exact hr e he
    · intro hall; exact ⟨fun e he => hall e (Or.inl he), fun e he => hall e (Or.inr he)⟩

/-- **Soundness of the mod-p class check.** If `RT.okMod p h` holds after routing the values `vs` with keys `cs` from
`toRT t0`, then for every position `q` the values with the key of `q` sum to their number times `h`, modulo `p`. -/
theorem okMod_sound (p h : ℕ) (vs cs : List ℕ) (t0 : AT) (hok : RT.okMod p h (routeR vs cs (toRT t0)) = true)
    (hlen : vs.length = cs.length) (q : ℕ) (hq : q < vs.length) :
    (∑ q' ∈ range vs.length, (if cs.getD q' 0 = cs.getD q 0 then vs.getD q' 0 else 0)) % p =
      (((range vs.length).filter fun q' => cs.getD q' 0 = cs.getD q 0).card * h) % p := by
  obtain ⟨hL, _, hJ⟩ := routeR_spec vs cs (toRT t0) hlen
  set j := t0.tgt (cs.getD q 0) with hj
  have hjl : j < t0.leaves.length := AT.tgt_lt t0 _
  have hjl' : j < (toRT t0).leaves.length := by rw [toRT_leaves, List.length_map]; exact hjl
  obtain ⟨h1, h2, h3, h4, _⟩ := hJ j hjl'
  simp only [toRT_tgt, toRT_getD t0 j hjl] at h1 h2 h3 h4
  have hmem : (routeR vs cs (toRT t0)).leaves.getD j dLeafR ∈ (routeR vs cs (toRT t0)).leaves := by
    have hlt : j < (routeR vs cs (toRT t0)).leaves.length := by rw [hL]; exact hjl'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem hlt
  obtain ⟨hflag, hmod⟩ := (RT.okMod_iff p h _).1 hok _ hmem
  have hkey := h4 hflag
  have hcq : cs.getD q 0 = (t0.leaves.getD j dLeaf).1 := hkey q hq rfl
  -- the positions routed to leaf `j` are exactly those with the key of `q`
  have hiff : ∀ q' < vs.length, (t0.tgt (cs.getD q' 0) = j ↔ cs.getD q' 0 = cs.getD q 0) := by
    intro q' hq'
    constructor
    · intro ht; rw [hkey q' hq' ht, hcq]
    · intro he; rw [he]
  have hsum : (∑ q' ∈ range vs.length, (if cs.getD q' 0 = cs.getD q 0 then vs.getD q' 0 else 0)) =
      ∑ q' ∈ range vs.length, (if t0.tgt (cs.getD q' 0) = j then vs.getD q' 0 else 0) := by
    refine Finset.sum_congr rfl fun q' hq' => ?_
    by_cases ht : t0.tgt (cs.getD q' 0) = j
    · rw [ite_eq_left ht, ite_eq_left ((hiff q' (Finset.mem_range.1 hq')).1 ht)]
    · rw [ite_eq_right ht, ite_eq_right fun he => ht ((hiff q' (Finset.mem_range.1 hq')).2 he)]
  have hcard : ((range vs.length).filter fun q' => cs.getD q' 0 = cs.getD q 0) =
      (range vs.length).filter fun q' => t0.tgt (cs.getD q' 0) = j :=
    Finset.filter_congr fun q' hq' => (hiff q' (Finset.mem_range.1 hq')).symm
  rw [hsum, hcard]
  have e2 : ((routeR vs cs (toRT t0)).leaves.getD j dLeafR).2.1 =
      ∑ q' ∈ range vs.length, (if t0.tgt (cs.getD q' 0) = j then vs.getD q' 0 else 0) := by
    rw [h2]; simp
  have e3 : ((routeR vs cs (toRT t0)).leaves.getD j dLeafR).2.2.1 =
      ((range vs.length).filter fun q' => t0.tgt (cs.getD q' 0) = j).card := by
    rw [h3, Finset.card_filter]; simp
  rw [← e2, ← e3]
  exact hmod

end NPT.Cert.KR
