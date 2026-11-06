/-
NPT.K4.Route.OffsK — the offset hypothesis `hoff` from kernel-cheap checks.

Adding the offsets of a slice to the fixed tree is routing (`tOff_eq_routeL`), so the initial value of the leaf of a
key `c` is its own initial value plus the offsets whose keys reach the same leaf (`offAt_tOff`). When every
representative routes to its own leaf (one routing pass of the representatives, `routeL_keys`) and all initial values
are zero, the offsets reaching `c`'s leaf are exactly those keyed `c`. One merge of each offset list against the
representatives (`mergeOffs`, which must consume every offset) gives the per-representative offsets; their sums over
the slices are compared with the negated residuals (`hoffK`).
-/
import NPT.K4.Route.SliceSound
import NPT.K4.Route.Offs

namespace NPT.K4.Route

open BigOperators Finset NPT.Cert.Ident

lemma tOff_eq_routeL (t : AT) (offs : List (Nat × Int)) :
    tOff t offs = routeL (offs.map fun e => SInt.ofInt e.2) (offs.map Prod.fst) t := by
  induction offs generalizing t with
  | nil => rfl
  | cons e es ih =>
    show tOff (t.add e.1 (SInt.ofInt e.2)) es = _
    rw [ih]
    rfl

lemma getD_map_fst (offs : List (Nat × Int)) (q : Nat) : (offs.map Prod.fst).getD q 0 = (offs.getD q (0, 0)).1 := by
  induction offs generalizing q with
  | nil => rfl
  | cons e es ih => cases q with
    | zero => rfl
    | succ q => exact ih q

lemma getD_map_ofInt (offs : List (Nat × Int)) (q : Nat) :
    ((offs.map fun e => SInt.ofInt e.2).getD q SInt.zero).val = (offs.getD q (0, 0)).2 := by
  induction offs generalizing q with
  | nil => simp [SInt.val, SInt.zero]
  | cons e es ih => cases q with
    | zero => exact SInt.val_ofInt e.2
    | succ q => exact ih q

/-- **Offsets at a key**: own initial value plus the offsets routed to the same leaf. -/
lemma offAt_tOff (t : AT) (offs : List (Nat × Int)) (c : Nat) :
    offAt (tOff t offs) c = offAt t c + ∑ q ∈ range offs.length,
      (if t.tgt (offs.getD q (0, 0)).1 = t.tgt c then (offs.getD q (0, 0)).2 else 0) := by
  rw [tOff_eq_routeL]
  obtain ⟨_, htgt, hJ⟩ := routeL_spec (offs.map fun e => SInt.ofInt e.2) (offs.map Prod.fst) t (by simp)
  obtain ⟨_, h2, _, _⟩ := hJ _ (AT.tgt_lt t c)
  unfold offAt
  rw [htgt, h2, List.length_map]
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [getD_map_fst, getD_map_ofInt]

/-- With `c` and every offset key routing to their own leaves, the offsets reaching `c`'s leaf are those keyed `c`. -/
lemma sum_tgt_eq_key (t : AT) (offs : List (Nat × Int)) (c : Nat)
    (hc : (t.leaves.getD (t.tgt c) dLeaf).1 = c)
    (hk : ∀ e ∈ offs, (t.leaves.getD (t.tgt e.1) dLeaf).1 = e.1) :
    ∑ q ∈ range offs.length, (if t.tgt (offs.getD q (0, 0)).1 = t.tgt c then (offs.getD q (0, 0)).2 else 0) =
      ∑ q ∈ range offs.length, (if (offs.getD q (0, 0)).1 = c then (offs.getD q (0, 0)).2 else 0) := by
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' := Finset.mem_range.1 hq
  by_cases h : (offs.getD q (0, 0)).1 = c
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg]
    intro ht
    apply h
    rw [← hk _ (getD_mem_of_lt offs q (0, 0) hq'), ht, hc]

lemma sum_range_getD {β : Type} (l : List β) (d : β) (f : β → Int) :
    ∑ q ∈ range l.length, f (l.getD q d) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]
    ring

/-! ### Merge of offsets against the representatives -/

/-- Merge of an offset list against the representatives: the offset of each representative (`0` if absent) and the
offsets not consumed (keys out of order, repeated, or not representatives). -/
def mergeOffs : List Nat → List (Nat × Int) → List Int × List (Nat × Int)
  | [], es => ([], es)
  | _ :: cs, [] => (0 :: (mergeOffs cs []).1, (mergeOffs cs []).2)
  | c :: cs, e :: es =>
    if e.1 = c then (e.2 :: (mergeOffs cs es).1, (mergeOffs cs es).2)
    else (0 :: (mergeOffs cs (e :: es)).1, (mergeOffs cs (e :: es)).2)

lemma mergeOffs_length : ∀ (reps : List Nat) (offs : List (Nat × Int)),
    (mergeOffs reps offs).1.length = reps.length
  | [], _ => rfl
  | _ :: cs, [] => by simp only [mergeOffs, List.length_cons, mergeOffs_length cs []]
  | c :: cs, e :: es => by
    simp only [mergeOffs]
    split_ifs <;> simp only [List.length_cons, mergeOffs_length]

lemma mergeOffs_keys : ∀ (reps : List Nat) (offs : List (Nat × Int)), (mergeOffs reps offs).2 = [] →
    ∀ e ∈ offs, e.1 ∈ reps
  | [], es, h, e, he => by
    simp only [mergeOffs] at h
    subst h
    simp at he
  | _ :: _, [], _, _, he => by simp at he
  | c :: cs, e' :: es, h, e, he => by
    simp only [mergeOffs] at h
    split_ifs at h with hc
    · rcases List.mem_cons.1 he with rfl | he
      · rw [hc]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mergeOffs_keys cs es h e he)
    · exact List.mem_cons_of_mem _ (mergeOffs_keys cs (e' :: es) h e he)

lemma sum_ite_key_zero (offs : List (Nat × Int)) (c : Nat) (h : ∀ e ∈ offs, e.1 ≠ c) :
    (offs.map fun e => if e.1 = c then e.2 else 0).sum = 0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  rw [if_neg (h e he)]

/-- **The merge gives the per-representative offsets** (representatives without repetition, all offsets consumed). -/
lemma mergeOffs_val : ∀ (reps : List Nat) (offs : List (Nat × Int)), (mergeOffs reps offs).2 = [] → reps.Nodup →
    ∀ i < reps.length, (mergeOffs reps offs).1.getD i 0 =
      (offs.map fun e => if e.1 = reps.getD i 0 then e.2 else 0).sum
  | [], _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | c :: cs, [], h, hnd, i, hi => by
    cases i with
    | zero => simp [mergeOffs]
    | succ i =>
      simp only [mergeOffs] at h
      simp only [mergeOffs, List.getD_cons_succ, List.map_nil, List.sum_nil]
      have := mergeOffs_val cs [] h (List.nodup_cons.1 hnd).2 i (by simpa using hi)
      simpa using this
  | c :: cs, e :: es, h, hnd, i, hi => by
    have hc' := (List.nodup_cons.1 hnd).1
    have hnd' := (List.nodup_cons.1 hnd).2
    simp only [mergeOffs] at h ⊢
    split_ifs at h ⊢ with hec
    · have hkeys := mergeOffs_keys cs es h
      cases i with
      | zero =>
        simp only [List.getD_cons_zero, List.map_cons, List.sum_cons, if_pos hec]
        rw [sum_ite_key_zero es c (fun e' he' h' => hc' (h' ▸ hkeys e' he')), add_zero]
      | succ i =>
        have hi' : i < cs.length := by simpa using hi
        simp only [List.getD_cons_succ, List.map_cons, List.sum_cons]
        have hne : ¬ e.1 = cs.getD i 0 := by
          rw [hec]
          intro h'
          exact hc' (h' ▸ getD_mem_of_lt cs i 0 hi')
        rw [if_neg hne, zero_add]
        exact mergeOffs_val cs es h hnd' i hi'
    · have hkeys := mergeOffs_keys cs (e :: es) h
      cases i with
      | zero =>
        simp only [List.getD_cons_zero]
        exact (sum_ite_key_zero (e :: es) c (fun e' he' h' => hc' (h' ▸ hkeys e' he'))).symm
      | succ i =>
        simp only [List.getD_cons_succ]
        exact mergeOffs_val cs (e :: es) h hnd' i (by simpa using hi)

/-! ### Row sums -/

/-- Entrywise sum of two rows (up to the shorter length). -/
def addZ : List Int → List Int → List Int
  | a :: as, b :: bs => (a + b) :: addZ as bs
  | [], _ => []
  | _ :: _, [] => []

lemma addZ_length : ∀ (as bs : List Int), (addZ as bs).length = min as.length bs.length
  | _ :: as, _ :: bs => by simp only [addZ, List.length_cons, addZ_length as bs]; omega
  | [], _ => by simp [addZ]
  | _ :: _, [] => by simp [addZ]

lemma addZ_getD : ∀ (as bs : List Int) (i : Nat), i < as.length → i < bs.length →
    (addZ as bs).getD i 0 = as.getD i 0 + bs.getD i 0
  | _ :: _, _ :: _, 0, _, _ => rfl
  | a :: as, b :: bs, i + 1, h1, h2 => by
    simp only [addZ, List.getD_cons_succ]
    exact addZ_getD as bs i (by simpa using h1) (by simpa using h2)
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ :: _, [], _, _, h => absurd h (Nat.not_lt_zero _)

/-- Entrywise sum of rows of length `n`. -/
def sumRows (rows : List (List Int)) (n : Nat) : List Int := rows.foldr addZ (List.replicate n 0)

lemma sumRows_length (rows : List (List Int)) (n : Nat) (hlen : ∀ r ∈ rows, r.length = n) :
    (sumRows rows n).length = n := by
  induction rows with
  | nil => simp [sumRows]
  | cons r rs ih =>
    show (addZ r (sumRows rs n)).length = n
    rw [addZ_length, hlen r List.mem_cons_self, ih fun r' hr' => hlen r' (List.mem_cons_of_mem _ hr'), min_self]

lemma sumRows_getD (rows : List (List Int)) (n : Nat) (hlen : ∀ r ∈ rows, r.length = n) (i : Nat) (hi : i < n) :
    (sumRows rows n).getD i 0 = (rows.map fun r => r.getD i 0).sum := by
  induction rows with
  | nil => simp [sumRows, List.getD_eq_getElem?_getD, hi]
  | cons r rs ih =>
    have hrs : ∀ r' ∈ rs, r'.length = n := fun r' hr' => hlen r' (List.mem_cons_of_mem _ hr')
    show (addZ r (sumRows rs n)).getD i 0 = _
    rw [addZ_getD _ _ i (by rw [hlen r List.mem_cons_self]; exact hi) (by rw [sumRows_length rs n hrs]; exact hi),
      ih hrs, List.map_cons, List.sum_cons]

/-! ### The checks -/

/-- Strictly increasing. -/
def sortedLt : List Nat → Bool
  | a :: b :: l => decide (a < b) && sortedLt (b :: l)
  | _ => true

lemma sortedLt_lt : ∀ (a : Nat) (l : List Nat), sortedLt (a :: l) = true → ∀ x ∈ l, a < x
  | _, [], _, _, hx => absurd hx List.not_mem_nil
  | a, b :: l, h, x, hx => by
    simp only [sortedLt, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (sortedLt_lt b l h.2 x hx)

lemma sortedLt_nodup : ∀ l : List Nat, sortedLt l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [a], _ => List.nodup_singleton a
  | a :: b :: l, h => by
    have h' := h
    simp only [sortedLt, Bool.and_eq_true] at h'
    exact List.nodup_cons.2 ⟨fun hm => lt_irrefl a (sortedLt_lt a (b :: l) h a hm), sortedLt_nodup (b :: l) h'.2⟩

/-- The merged offsets of all slices: every offset consumed, and the per-representative sums are the negated
residuals (in the order of the representatives). -/
def hoffK (reps : List Nat) (resL : List Int) (offsL : List (List (Nat × Int))) : Bool :=
  (offsL.all fun offs => (mergeOffs reps offs).2.isEmpty) && (resL.length == reps.length) &&
    (sumRows (offsL.map fun offs => (mergeOffs reps offs).1) reps.length == resL.map Neg.neg)

/-- Every representative routes to its own leaf (one routing pass). -/
lemma routeL_keys (t0 : AT) (reps : List Nat)
    (hK : (routeL (reps.map fun _ => SInt.zero) reps t0).leaves.all (fun e => e.2.2) = true) :
    ∀ c ∈ reps, (t0.leaves.getD (t0.tgt c) dLeaf).1 = c := by
  intro c hc
  obtain ⟨hlen, _, hJ⟩ := routeL_spec (reps.map fun _ => SInt.zero) reps t0 (by simp)
  have hj := AT.tgt_lt t0 c
  obtain ⟨_, _, h3, _⟩ := hJ _ hj
  have hok : ((routeL (reps.map fun _ => SInt.zero) reps t0).leaves.getD (t0.tgt c) dLeaf).2.2 = true :=
    List.all_eq_true.1 hK _ (getD_mem_of_lt _ _ dLeaf (by rw [hlen]; exact hj))
  have hq := List.idxOf_lt_length_of_mem hc
  have hgc : reps.getD (reps.idxOf c) 0 = c := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some, List.getElem_idxOf hq]
  have := h3 hok (reps.idxOf c) (by simpa using hq) (by rw [hgc])
  rw [hgc] at this
  exact this.symm

/-- **The offset hypothesis from the checks.** -/
theorem hoff_of_checks (t0 : AT) (reps : List Nat) (resL : List Int) (offsL : List (List (Nat × Int)))
    (h24 : offsL.length = 24) (hsort : sortedLt reps = true)
    (hkeys : (routeL (reps.map fun _ => SInt.zero) reps t0).leaves.all (fun e => e.2.2) = true)
    (hzero : t0.leaves.all (fun e => e.2.1.mag == 0) = true)
    (hK : hoffK reps resL offsL = true) :
    ∀ c ∈ reps, ∑ j : Fin 24, offAt (tOff t0 (offsL.getD j.val [])) c = -RintOfR reps resL c := by
  intro c hc
  have hnd := sortedLt_nodup reps hsort
  have hkey := routeL_keys t0 reps hkeys
  unfold hoffK at hK
  simp only [Bool.and_eq_true, List.all_eq_true, List.isEmpty_iff, beq_iff_eq] at hK
  obtain ⟨⟨hcons, hrl⟩, hsum⟩ := hK
  have hz : offAt t0 c = 0 := by
    unfold offAt
    have hm := List.all_eq_true.1 hzero _ (getD_mem_of_lt _ _ dLeaf (AT.tgt_lt t0 c))
    exact SInt.val_eq_zero_of_mag (by simpa using hm)
  set i := reps.idxOf c with hi
  have hq : i < reps.length := List.idxOf_lt_length_of_mem hc
  have hgc : reps.getD i 0 = c := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some, List.getElem_idxOf hq]
  -- each slice: the offset at `c` is the merged entry `i`
  have hslice : ∀ offs ∈ offsL, offAt (tOff t0 offs) c = (mergeOffs reps offs).1.getD i 0 := by
    intro offs hoffs
    have hmk := mergeOffs_keys reps offs (hcons offs hoffs)
    rw [offAt_tOff, hz, zero_add, sum_tgt_eq_key t0 offs c (hkey c hc) (fun e he => hkey e.1 (hmk e he)),
      sum_range_getD offs (0, 0) (fun e => if e.1 = c then e.2 else 0),
      mergeOffs_val reps offs (hcons offs hoffs) hnd i hq, hgc]
  have hfin : ∑ j : Fin 24, offAt (tOff t0 (offsL.getD j.val [])) c =
      (offsL.map fun offs => (mergeOffs reps offs).1.getD i 0).sum := by
    rw [Fin.sum_univ_eq_sum_range (fun j => offAt (tOff t0 (offsL.getD j [])) c) 24, ← h24,
      sum_range_getD offsL [] (fun offs => offAt (tOff t0 offs) c)]
    exact congrArg List.sum (List.map_congr_left fun offs hoffs => hslice offs hoffs)
  rw [hfin]
  have hrows : ∀ r ∈ offsL.map (fun offs => (mergeOffs reps offs).1), r.length = reps.length := by
    intro r hr
    obtain ⟨offs, _, rfl⟩ := List.mem_map.1 hr
    exact mergeOffs_length reps offs
  have hg := sumRows_getD _ reps.length hrows i hq
  rw [hsum, List.map_map] at hg
  rw [show (offsL.map fun offs => (mergeOffs reps offs).1.getD i 0) =
      List.map ((fun r => r.getD i 0) ∘ fun offs => (mergeOffs reps offs).1) offsL from rfl, ← hg]
  unfold RintOfR
  rw [if_pos hc, ← hi]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases resL[i]? with _ | v
  · simp
  · simp

end NPT.K4.Route
