/-
NPT.Cert.Ident.Route — correctness of the class accumulation: after routing values `vs` with keys `cs`,
if every leaf flag is set, the leaf reached by a key `c` that occurs in `cs` holds the initial value plus the sum of
the values with key `c`.
-/
import NPT.Cert.Ident.Lemmas

open BigOperators Finset

namespace NPT.Cert.Ident

/-- Index (in `leaves`) of the leaf reached by `key`. -/
def AT.tgt : AT → Nat → Nat
  | .leaf _ _ _, _ => 0
  | .node k l r, key => if key < k then l.tgt key else l.leaves.length + r.tgt key

/-- Update entry `j` of a list. -/
def updAt {β : Type} : List β → Nat → (β → β) → List β
  | [], _, _ => []
  | x :: xs, 0, f => f x :: xs
  | x :: xs, j + 1, f => x :: updAt xs j f

lemma updAt_length {β : Type} : ∀ (xs : List β) (j : Nat) (f : β → β), (updAt xs j f).length = xs.length
  | [], _, _ => rfl
  | x :: xs, 0, f => rfl
  | x :: xs, j + 1, f => by simp [updAt, updAt_length xs j f]

lemma updAt_getD {β : Type} (d : β) : ∀ (xs : List β) (j i : Nat) (f : β → β), j < xs.length →
    (updAt xs j f).getD i d = if i = j then f (xs.getD i d) else xs.getD i d
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | x :: xs, 0, 0, f, _ => by simp [updAt]
  | x :: xs, 0, i + 1, f, _ => by simp [updAt]
  | x :: xs, j + 1, 0, f, _ => by simp [updAt]
  | x :: xs, j + 1, i + 1, f, h => by
    simp only [updAt, List.getD_cons_succ]
    rw [updAt_getD d xs j i f (by simpa using h)]
    simp

lemma updAt_append_left {β : Type} (f : β → β) : ∀ (xs ys : List β) (j : Nat), j < xs.length →
    updAt (xs ++ ys) j f = updAt xs j f ++ ys
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | x :: xs, ys, 0, _ => rfl
  | x :: xs, ys, j + 1, h => by simp [updAt, updAt_append_left f xs ys j (by simpa using h)]

lemma updAt_append_right {β : Type} (f : β → β) : ∀ (xs ys : List β) (j : Nat),
    updAt (xs ++ ys) (xs.length + j) f = xs ++ updAt ys j f
  | [], ys, j => by simp
  | x :: xs, ys, j => by
    rw [List.cons_append, List.length_cons, show xs.length + 1 + j = (xs.length + j) + 1 by omega]
    simp [updAt, updAt_append_right f xs ys j]

/-- The leaf update performed by `AT.add`. -/
def leafUpd (key : Nat) (v : SInt) (e : Nat × SInt × Bool) : Nat × SInt × Bool :=
  (e.1, e.2.1.add v, e.2.2 && e.1 == key)

lemma AT.leaves_pos : ∀ (t : AT), 0 < t.leaves.length
  | .leaf _ _ _ => by simp [AT.leaves]
  | .node _ l r => by simp only [AT.leaves, List.length_append]; have := AT.leaves_pos l; omega

lemma AT.tgt_lt : ∀ (t : AT) (key : Nat), t.tgt key < t.leaves.length
  | .leaf _ _ _, _ => by simp [AT.tgt, AT.leaves]
  | .node k l r, key => by
    simp only [AT.tgt, AT.leaves, List.length_append]
    split_ifs
    · have := AT.tgt_lt l key; omega
    · have := AT.tgt_lt r key; omega

lemma AT.nodeL_eq (k : Nat) (l r : AT) : AT.nodeL k l r = .node k l r := by cases l <;> rfl
lemma AT.nodeR_eq (k : Nat) (l r : AT) : AT.nodeR k l r = .node k l r := by cases r <;> rfl

/-- `add` changes exactly the target leaf. -/
lemma AT.leaves_add : ∀ (t : AT) (key : Nat) (v : SInt),
    (t.add key v).leaves = updAt t.leaves (t.tgt key) (leafUpd key v)
  | .leaf k s ok, key, v => by simp [AT.add, AT.leaves, AT.tgt, updAt, leafUpd]
  | .node k l r, key, v => by
    simp only [AT.add, AT.tgt]
    split_ifs with h
    · rw [AT.nodeL_eq]; simp only [AT.leaves]
      rw [AT.leaves_add l key v, updAt_append_left _ _ _ _ (AT.tgt_lt l key)]
    · rw [AT.nodeR_eq]; simp only [AT.leaves]
      rw [AT.leaves_add r key v, updAt_append_right]

/-- `add` preserves the routing (shape and node keys). -/
lemma AT.tgt_add : ∀ (t : AT) (key key' : Nat) (v : SInt), (t.add key v).tgt key' = t.tgt key'
  | .leaf _ _ _, _, _, _ => by simp [AT.add, AT.tgt]
  | .node k l r, key, key', v => by
    simp only [AT.add]
    split_ifs with h
    · rw [AT.nodeL_eq]; simp only [AT.tgt]
      rw [AT.tgt_add l key key' v, show (l.add key v).leaves.length = l.leaves.length by
        rw [AT.leaves_add, updAt_length]]
    · rw [AT.nodeR_eq]; simp only [AT.tgt]
      rw [AT.tgt_add r key key' v]

lemma AT.leaves_length_add (t : AT) (key : Nat) (v : SInt) : (t.add key v).leaves.length = t.leaves.length := by
  rw [AT.leaves_add, updAt_length]

/-- Default leaf entry. -/
def dLeaf : Nat × SInt × Bool := (0, SInt.zero, true)

/-- **Routing invariant.** -/
lemma routeL_spec : ∀ (vs : List SInt) (cs : List Nat) (t : AT), vs.length = cs.length →
    (routeL vs cs t).leaves.length = t.leaves.length ∧
    (∀ key, (routeL vs cs t).tgt key = t.tgt key) ∧
    ∀ j < t.leaves.length,
      ((routeL vs cs t).leaves.getD j dLeaf).1 = (t.leaves.getD j dLeaf).1 ∧
      ((routeL vs cs t).leaves.getD j dLeaf).2.1.val = (t.leaves.getD j dLeaf).2.1.val +
        ∑ q ∈ range vs.length, (if t.tgt (cs.getD q 0) = j then (vs.getD q SInt.zero).val else 0) ∧
      (((routeL vs cs t).leaves.getD j dLeaf).2.2 = true →
        ∀ q < vs.length, t.tgt (cs.getD q 0) = j → cs.getD q 0 = (t.leaves.getD j dLeaf).1) ∧
      (((routeL vs cs t).leaves.getD j dLeaf).2.2 = true → (t.leaves.getD j dLeaf).2.2 = true)
  | [], [], t, _ => by
    refine ⟨rfl, fun _ => rfl, fun j _ => ⟨rfl, by simp [routeL], fun _ q hq => absurd hq (Nat.not_lt_zero _),
      fun h => h⟩⟩
  | v :: vs, c :: cs, t, hlen => by
    have hlen' : vs.length = cs.length := by simpa using hlen
    obtain ⟨hL, hT, hJ⟩ := routeL_spec vs cs (t.add c v) hlen'
    simp only [routeL]
    have hL1 := AT.leaves_length_add t c v
    refine ⟨by rw [hL, hL1], fun key => by rw [hT, AT.tgt_add], fun j hj => ?_⟩
    have hj' : j < (t.add c v).leaves.length := by rw [hL1]; exact hj
    obtain ⟨h1, h2, h3, h4⟩ := hJ j hj'
    have hget : (t.add c v).leaves.getD j dLeaf =
        if j = t.tgt c then leafUpd c v (t.leaves.getD j dLeaf) else t.leaves.getD j dLeaf := by
      rw [AT.leaves_add, updAt_getD _ _ _ _ _ (AT.tgt_lt t c)]
    simp only [AT.tgt_add] at h2 h3
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, hget]; split_ifs <;> rfl
    · rw [h2, hget, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      by_cases hc : j = t.tgt c
      · rw [if_pos hc, if_pos hc.symm]
        simp only [leafUpd, SInt.val_add]
        ring
      · rw [if_neg hc, if_neg (Ne.symm hc), add_zero]
    · intro hok q hq htq
      rcases q with _ | q
      · simp only [List.getD_cons_zero] at htq ⊢
        have hflag := h4 hok
        rw [hget, if_pos htq.symm] at hflag
        simp only [leafUpd, Bool.and_eq_true, beq_iff_eq] at hflag
        exact hflag.2.symm
      · simp only [List.getD_cons_succ] at htq ⊢
        have := h3 hok q (by simpa using hq) htq
        rw [this, hget]
        split_ifs <;> rfl
    · intro hok
      have hflag := h4 hok
      rw [hget] at hflag
      split_ifs at hflag
      · simp only [leafUpd, Bool.and_eq_true] at hflag; exact hflag.1
      · exact hflag
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

end NPT.Cert.Ident
