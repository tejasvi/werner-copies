/-
NPT.K4.RouteKeys — class keys from the slice checks.

* `sliceCheck_keys`: a passing slice check routes every class code of the slice to a leaf with that key
  (the leaf flags record key matches, `routeL_spec`);
* `tOff_tgt`, `tOff_key`: adding offsets (`tOff`) keeps the routing and the leaf keys;
* `key_all`, `key_mem`: hence a class code found in one slice is the key of its leaf in every accumulator built from
  the same tree, and it is one of the tree's keys.
-/
import NPT.K4.Route.Offs
import NPT.K4.Route.SliceSound

namespace NPT.K4.Route

open BigOperators Finset NPT.Cert.Ident

theorem sliceCheck_keys (b : Nat) (ps : List Part) (cls : List Nat) (t0 : AT) (h : sliceCheck b ps cls t0 = true)
    (q : Nat) (hq : q < cls.length) : (t0.leaves.getD (t0.tgt (cls.getD q 0)) dLeaf).1 = cls.getD q 0 := by
  unfold sliceCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨_, _⟩, hcl⟩, hall⟩ := h
  have hlen : (digitsOf b (partsSlicesA b ps)).length = cls.length := by rw [digitsOf_length, hcl]
  obtain ⟨hL, _, hJ⟩ := routeL_spec _ _ t0 hlen
  have hjl : t0.tgt (cls.getD q 0) < t0.leaves.length := AT.tgt_lt t0 _
  obtain ⟨_, _, h3, _⟩ := hJ _ hjl
  have hflag := (hall _ (getD_mem_of_lt _ _ dLeaf (by rw [hL]; exact hjl))).1
  exact (h3 hflag q (by rw [hlen]; exact hq) rfl).symm

lemma tOff_cons (t : AT) (e : Nat × Int) (offs : List (Nat × Int)) :
    tOff t (e :: offs) = tOff (t.add e.1 (SInt.ofInt e.2)) offs := rfl

lemma tOff_tgt (offs : List (Nat × Int)) : ∀ (t : AT) (key : Nat), (tOff t offs).tgt key = t.tgt key := by
  induction offs with
  | nil => intro t key; rfl
  | cons e offs ih => intro t key; rw [tOff_cons, ih, AT.tgt_add]

lemma tOff_key (offs : List (Nat × Int)) :
    ∀ (t : AT) (j : Nat), ((tOff t offs).leaves.getD j dLeaf).1 = (t.leaves.getD j dLeaf).1 := by
  induction offs with
  | nil => intro t j; rfl
  | cons e offs ih =>
    intro t j
    rw [tOff_cons, ih, AT.leaves_add, updAt_getD dLeaf _ _ _ _ (AT.tgt_lt t e.1)]
    split_ifs <;> simp [leafUpd]

/-- **A class code found in one slice is a key in every accumulator built from the same tree.** -/
theorem key_all (b : Nat) (ps : List Part) (cls : List Nat) (t0 : AT) (offs offs' : List (Nat × Int))
    (h : sliceCheck b ps cls (tOff t0 offs) = true) (q : Nat) (hq : q < cls.length) :
    ((tOff t0 offs').leaves.getD ((tOff t0 offs').tgt (cls.getD q 0)) dLeaf).1 = cls.getD q 0 := by
  have hk := sliceCheck_keys b ps cls (tOff t0 offs) h q hq
  rw [tOff_tgt, tOff_key] at hk ⊢
  exact hk

/-- A key of a tree is the first component of one of its leaves. -/
theorem key_mem (t0 : AT) (c : Nat) (hc : (t0.leaves.getD (t0.tgt c) dLeaf).1 = c) :
    ∃ e ∈ t0.leaves, e.1 = c :=
  ⟨_, getD_mem_of_lt _ _ dLeaf (AT.tgt_lt t0 c), hc⟩

end NPT.K4.Route

#print axioms NPT.K4.Route.key_all
