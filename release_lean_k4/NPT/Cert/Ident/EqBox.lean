/-
NPT.Cert.Ident.EqBox — the equality parts of a family as one λ-tensor box per (group, part): instead of
one rank-one part per multiplier entry, leg `l` has the rows `o ↦ eqT spec_l n_l p o` and the leaf is the dense
λ-tensor `Σ_{entries at o} coef · λ`.  Same word values (`partsF_eqBox`); far fewer packed slices to build.
-/
import NPT.Cert.Ident.Assembly
import NPT.Cert.Ident.Paths
import NPT.Cert.Ident.Rank1

open BigOperators Finset NPT.Cert.Sem

namespace NPT.Cert.Ident

/-- Rows of one leg: `R[p][o] = eqT sp n p o`, `o < N`. -/
def eqRows (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (sp : EqSpecD) (n N : ℕ) : List (List SInt) :=
  (List.finRange 24).map fun p => (List.range N).map fun o => SInt.ofInt (eqT sp n p o)

/-- Leg size: one more than the largest index of leg `l` among the entries. -/
def lamN (lam : List (List ℕ × ℤ)) (l : ℕ) : ℕ := (lam.map fun ol => ol.1.getD l 0 + 1).foldr max 1

/-- Mixed-radix code of four indices. -/
def enc4 (N1 N2 N3 : ℕ) (o : List ℕ) : ℕ := ((o.getD 0 0 * N1 + o.getD 1 0) * N2 + o.getD 2 0) * N3 + o.getD 3 0

/-- The dense λ-tensor: entry `k` is `Σ_{entries with code k} coef · λ`. -/
def eqLeaf (N0 N1 N2 N3 : ℕ) (lam : List (List ℕ × ℤ)) (coef : ℤ) : List SInt :=
  (List.range (N0 * (N1 * (N2 * N3)))).map fun k =>
    SInt.ofInt ((lam.map fun ol => if enc4 N1 N2 N3 ol.1 = k then coef * ol.2 else 0).sum)

def eqBoxSpec (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (P : EqPartD) (d : ℕ) (lam : List (List ℕ × ℤ)) (coef : ℤ) :
    Spec where
  rows m := eqRows eqT (P.specs.getD m default) (nfN d m) (lamN lam m)
  dimsq m := lamN lam m
  leaf _ _ _ _ := eqLeaf (lamN lam 0) (lamN lam 1) (lamN lam 2) (lamN lam 3) lam coef

def eqBoxPart (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (P : EqPartD) (d : ℕ) (lam : List (List ℕ × ℤ)) (coef : ℤ) :
    Part := ⟨eqBoxSpec eqT P d lam coef, rank1Tree⟩

/-- The equality parts of family `f`, one λ-box per (group, part). -/
def eqBoxPartsF (C : CertD) (f : ℕ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : List Part :=
  C.eqs.flatMap fun g => g.parts.flatMap fun P => if P.fam = f then
    [eqBoxPart eqT P C.d g.lam (-(P.sign) * (den3 C.d : ℤ))] else []

lemma lt_lamN (lam : List (List ℕ × ℤ)) (l : ℕ) : ∀ ol ∈ lam, ol.1.getD l 0 < lamN lam l := by
  intro ol hol
  unfold lamN
  induction lam with
  | nil => simp at hol
  | cons a lam ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 hol with rfl | h
    · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact lt_of_lt_of_le (ih h) (le_max_right _ _)

lemma aval_eqRows (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (sp : EqSpecD) (n N : ℕ) (p : Fin 24) (o : ℕ) (ho : o < N) :
    aval (eqRows eqT sp n N) p.val o = eqT sp n p o := by
  unfold aval eqRows
  rw [map_finRange_getD, getD_range_map _ _ _ _ ho, SInt.val_ofInt]

/-- Quotient and remainder determine a number. -/
lemma divmod_unique {x e x' e' N : ℕ} (he : e < N) (he' : e' < N) (h : x * N + e = x' * N + e') :
    x = x' ∧ e = e' := by
  have hN : 0 < N := by omega
  have q : ∀ y r, r < N → (y * N + r) / N = y ∧ (y * N + r) % N = r := fun y r hr => by
    constructor
    · rw [add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hr, zero_add]
    · rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  obtain ⟨h1, h2⟩ := q x e he
  obtain ⟨h3, h4⟩ := q x' e' he'
  rw [h] at h1 h2
  exact ⟨h1.symm.trans h3, h2.symm.trans h4⟩

/-- Mixed-radix codes are unique on the box. -/
lemma mr_eq_iff {N1 N2 N3 a b c e a' b' c' e' : ℕ} (hb : b < N1) (hc : c < N2) (he : e < N3) (hb' : b' < N1)
    (hc' : c' < N2) (he' : e' < N3) :
    ((a * N1 + b) * N2 + c) * N3 + e = ((a' * N1 + b') * N2 + c') * N3 + e' ↔ a = a' ∧ b = b' ∧ c = c' ∧ e = e' := by
  constructor
  · intro h
    obtain ⟨h3', h3⟩ := divmod_unique he he' h
    obtain ⟨h2', h2⟩ := divmod_unique hc hc' h3'
    obtain ⟨h0, h1⟩ := divmod_unique hb hb' h2'
    exact ⟨h0, h1, h2, h3⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

/-- The four-fold indicator sum over the box picks the entry's own index. -/
lemma box_indicator (N0 N1 N2 N3 : ℕ) (E0 E1 E2 E3 : ℕ → ℤ) (o : List ℕ) (c : ℤ)
    (h0 : o.getD 0 0 < N0) (h1 : o.getD 1 0 < N1) (h2 : o.getD 2 0 < N2) (h3 : o.getD 3 0 < N3) :
    ∑ i0 ∈ range N0, ∑ i1 ∈ range N1, ∑ i2 ∈ range N2, ∑ i3 ∈ range N3,
      E0 i0 * E1 i1 * E2 i2 * E3 i3 * (if enc4 N1 N2 N3 o = ((i0 * N1 + i1) * N2 + i2) * N3 + i3 then c else 0) =
    c * (E0 (o.getD 0 0) * E1 (o.getD 1 0) * E2 (o.getD 2 0) * E3 (o.getD 3 0)) := by
  have key : ∀ i0 i1 i2 i3, i1 < N1 → i2 < N2 → i3 < N3 →
      (enc4 N1 N2 N3 o = ((i0 * N1 + i1) * N2 + i2) * N3 + i3 ↔
        o.getD 0 0 = i0 ∧ o.getD 1 0 = i1 ∧ o.getD 2 0 = i2 ∧ o.getD 3 0 = i3) :=
    fun i0 i1 i2 i3 hi1 hi2 hi3 => mr_eq_iff h1 h2 h3 hi1 hi2 hi3
  rw [Finset.sum_eq_single_of_mem (o.getD 0 0) (Finset.mem_range.2 h0) ?z0,
    Finset.sum_eq_single_of_mem (o.getD 1 0) (Finset.mem_range.2 h1) ?z1,
    Finset.sum_eq_single_of_mem (o.getD 2 0) (Finset.mem_range.2 h2) ?z2,
    Finset.sum_eq_single_of_mem (o.getD 3 0) (Finset.mem_range.2 h3) ?z3]
  · rw [ite_eq_left (show enc4 N1 N2 N3 o = ((o.getD 0 0 * N1 + o.getD 1 0) * N2 + o.getD 2 0) * N3 + o.getD 3 0 from rfl)]
    ring
  case z3 =>
    intro i3 hi3 hne
    rw [ite_eq_right fun h => hne ((key _ _ _ _ h1 h2 (Finset.mem_range.1 hi3)).1 h).2.2.2.symm, mul_zero]
  case z2 =>
    intro i2 hi2 hne
    refine Finset.sum_eq_zero fun i3 hi3 => ?_
    rw [ite_eq_right fun h => hne ((key _ _ _ _ h1 (Finset.mem_range.1 hi2) (Finset.mem_range.1 hi3)).1 h).2.2.1.symm,
      mul_zero]
  case z1 =>
    intro i1 hi1 hne
    refine Finset.sum_eq_zero fun i2 hi2 => Finset.sum_eq_zero fun i3 hi3 => ?_
    rw [ite_eq_right fun h => hne ((key _ _ _ _ (Finset.mem_range.1 hi1) (Finset.mem_range.1 hi2)
      (Finset.mem_range.1 hi3)).1 h).2.1.symm, mul_zero]
  case z0 =>
    intro i0 _ hne
    refine Finset.sum_eq_zero fun i1 hi1 => Finset.sum_eq_zero fun i2 hi2 => Finset.sum_eq_zero fun i3 hi3 => ?_
    rw [ite_eq_right fun h => hne ((key _ _ _ _ (Finset.mem_range.1 hi1) (Finset.mem_range.1 hi2)
      (Finset.mem_range.1 hi3)).1 h).1.symm, mul_zero]

/-- **The λ-box has the word values of the rank-one parts.** -/
theorem specTree_eqBox (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (P : EqPartD) (d : ℕ) (lam : List (List ℕ × ℤ))
    (coef : ℤ) (w0 w1 w2 w3 : Fin 24) :
    specTree (eqBoxSpec eqT P d lam coef) rank1Tree w0.val w1.val w2.val w3.val =
      (lam.map fun ol => specTree (rank1Spec (fun l p => eqT (P.specs.getD l default) (nfN d l) p (ol.1.getD l 0))
        (coef * ol.2)) rank1Tree w0.val w1.val w2.val w3.val).sum := by
  simp only [rank1_spec]
  rw [specTree_paths]
  simp only [rank1Tree, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, boxF]
  have hd : ∀ m, (eqBoxSpec eqT P d lam coef).dimsq m = lamN lam m := fun _ => rfl
  simp only [hd]
  -- rows and leaf entries
  have hrow : ∀ (m : ℕ) (w : Fin 24) (o : ℕ), o < lamN lam m →
      aval ((eqBoxSpec eqT P d lam coef).rows m) w.val o = eqT (P.specs.getD m default) (nfN d m) w o :=
    fun m w o ho => aval_eqRows eqT _ _ _ w o ho
  have hleaf : ∀ i0 i1 i2 i3, i0 < lamN lam 0 → i1 < lamN lam 1 → i2 < lamN lam 2 → i3 < lamN lam 3 →
      gv ((eqBoxSpec eqT P d lam coef).leaf 1 2 3 ⟨0, []⟩)
          (i0 * (lamN lam 1 * lamN lam 2 * lamN lam 3) + (i1 * (lamN lam 2 * lamN lam 3) + (i2 * lamN lam 3 + i3))) =
        (lam.map fun ol => if enc4 (lamN lam 1) (lamN lam 2) (lamN lam 3) ol.1 =
          ((i0 * lamN lam 1 + i1) * lamN lam 2 + i2) * lamN lam 3 + i3 then coef * ol.2 else 0).sum := by
    intro i0 i1 i2 i3 h0 h1 h2 h3
    have hk : i0 * (lamN lam 1 * lamN lam 2 * lamN lam 3) + (i1 * (lamN lam 2 * lamN lam 3) + (i2 * lamN lam 3 + i3)) =
        ((i0 * lamN lam 1 + i1) * lamN lam 2 + i2) * lamN lam 3 + i3 := by ring
    have hlt : ((i0 * lamN lam 1 + i1) * lamN lam 2 + i2) * lamN lam 3 + i3 <
        lamN lam 0 * (lamN lam 1 * (lamN lam 2 * lamN lam 3)) := by
      have := mr4_lt (lamN lam 0) (lamN lam 1) (lamN lam 2) (lamN lam 3) i0 i1 i2 i3 h0 h1 h2 h3
      unfold mr4 at this
      rw [show lamN lam 0 * (lamN lam 1 * (lamN lam 2 * lamN lam 3)) =
        lamN lam 0 * lamN lam 1 * lamN lam 2 * lamN lam 3 by ring]
      exact this
    simp only [eqBoxSpec, eqLeaf, gv]
    rw [hk, getD_range_map _ _ _ _ hlt, SInt.val_ofInt]
  rw [Finset.sum_congr rfl fun i0 hi0 => Finset.sum_congr rfl fun i1 hi1 => Finset.sum_congr rfl fun i2 hi2 =>
    Finset.sum_congr rfl fun i3 hi3 => by
      rw [hrow 0 w0 i0 (Finset.mem_range.1 hi0), hrow 1 w1 i1 (Finset.mem_range.1 hi1),
        hrow 2 w2 i2 (Finset.mem_range.1 hi2), hrow 3 w3 i3 (Finset.mem_range.1 hi3),
        hleaf i0 i1 i2 i3 (Finset.mem_range.1 hi0) (Finset.mem_range.1 hi1) (Finset.mem_range.1 hi2)
          (Finset.mem_range.1 hi3)]]
  -- exchange the list sum outward, then evaluate the indicator entry by entry
  simp only [mul_list_sum, sum_list1]
  refine congrArg List.sum (List.map_congr_left fun ol hol => ?_)
  exact box_indicator _ _ _ _ (fun i => eqT (P.specs.getD 0 default) (nfN d 0) w0 i)
    (fun i => eqT (P.specs.getD 1 default) (nfN d 1) w1 i) (fun i => eqT (P.specs.getD 2 default) (nfN d 2) w2 i)
    (fun i => eqT (P.specs.getD 3 default) (nfN d 3) w3 i) ol.1 (coef * ol.2)
    (lt_lamN lam 0 ol hol) (lt_lamN lam 1 ol hol) (lt_lamN lam 2 ol hol) (lt_lamN lam 3 ol hol)

/-- **The λ-boxes of a family have the word values of its rank-one equality parts.** -/
theorem partsF_eqBox (C : CertD) (f : ℕ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (w0 w1 w2 w3 : Fin 24) :
    partsF (eqBoxPartsF C f eqT) w0.val w1.val w2.val w3.val = partsF (eqPartsF C f eqT) w0.val w1.val w2.val w3.val := by
  unfold eqBoxPartsF eqPartsF
  rw [partsF_flatMap, partsF_flatMap]
  refine congrArg List.sum (List.map_congr_left fun g _ => ?_)
  rw [partsF_flatMap, partsF_flatMap]
  refine congrArg List.sum (List.map_congr_left fun P _ => ?_)
  split_ifs with hf
  · simp only [partsF, eqBoxPart, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.map_map]
    rw [specTree_eqBox]
    rfl
  · rfl

lemma eqBoxPartsF_rows (C : CertD) (f : ℕ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) :
    ∀ P ∈ eqBoxPartsF C f eqT, ∀ m, (P.S.rows m).length = 24 := by
  intro P hP m
  unfold eqBoxPartsF at hP
  simp only [List.mem_flatMap] at hP
  obtain ⟨g, _, P', _, hP'⟩ := hP
  split_ifs at hP' with hf
  · rw [List.mem_singleton] at hP'
    subst hP'
    simp [eqBoxPart, eqBoxSpec, eqRows]
  · simp at hP'

end NPT.Cert.Ident
