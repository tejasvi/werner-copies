/-
NPT.K4.CRT — class sums of the slack functional from mod-p checks with residual targets, and the integer form of
the slack inequality.

* `classSum_of_modEq`: if `ZS f w = D · ΛS f w` (integers) and a class sum of `ZS` is `≡ Rj` modulo every `p` of a
  pairwise-coprime list whose product exceeds `2 (D · 24^(k+1) · B + R)`, with `|ΛS| ≤ B` (`abs_ΛS_le`) and
  `|Rj| ≤ R`, then the class sum of `ΛS` is exactly `Rj / D`.  This gives `IdFactS.hsum` with `res = Rint / D`.
* `hslack_of_int`: the slack hypothesis of `soundness_slack` for `res = Rint / D` and `nu = nuNum / nuDen`, from one
  integer inequality `(2 d^k)^4 · 786^k · 496 · S · nuDen ≤ nuNum · D · 8640^k · 2880` with `S ≥ Σ |Rint|`.
-/
import NPT.K4.Bound
import NPT.K4.SoundS
import NPT.Cert.Ident.KRIdFact

open BigOperators Finset NPT.Cert NPT.Cert.Sem

namespace NPT.K4

/-- **CRT with a target**: `S ≡ T` modulo pairwise-coprime moduli with `|S − T| < ∏ p` forces `S = T`. -/
theorem eq_of_modEq_list (S T : ℤ) (ps : List ℕ) (hcop : ps.Pairwise Nat.Coprime)
    (hmod : ∀ p ∈ ps, S ≡ T [ZMOD p]) (hlt : (S - T).natAbs < ps.prod) : S = T := by
  have h := NPT.Cert.KR.eq_zero_of_modEq_list (S - T) ps hcop (fun p hp => by
    have h1 := Int.ModEq.sub_right T (hmod p hp)
    rwa [sub_self] at h1) hlt
  linarith

/-- **Class sums with residual targets.** -/
theorem classSum_of_modEq (C : CertD) (α β : ℕ) (nu : ℚ) (D : ℕ) (hD : 0 < D)
    (ZS : ℕ → (Fin (C.k + 1) → Fin 24) → ℤ) (hZS : ∀ f w, (ZS f w : ℚ) = D * ΛS C α β nu f w)
    (B : ℚ) (hB : ∀ f w, |ΛS C α β nu f w| ≤ B) (R : ℕ) (ps : List ℕ) (hcop : ps.Pairwise Nat.Coprime)
    (hP : 2 * ((D : ℚ) * 24 ^ (C.k + 1) * B + R) < ps.prod)
    (cls : (Fin (C.k + 1) → Fin 24) → ℕ) (f j : ℕ) (Rj : ℤ) (hR : |Rj| ≤ R)
    (hmod : ∀ p ∈ ps, (∑ w ∈ univ.filter (fun w => cls w = j), ZS f w) ≡ Rj [ZMOD p]) :
    ∑ w ∈ univ.filter (fun w => cls w = j), ΛS C α β nu f w = (Rj : ℚ) / D := by
  set S : ℤ := ∑ w ∈ univ.filter (fun w => cls w = j), ZS f w with hS
  have hSq : (S : ℚ) = D * ∑ w ∈ univ.filter (fun w => cls w = j), ΛS C α β nu f w := by
    rw [hS]; push_cast; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => hZS f w
  have hcl := abs_classSum_le C α β nu B hB cls f j
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB f fun _ => 0)
  have hbound : |((S - Rj : ℤ) : ℚ)| < ps.prod := by
    rw [Int.cast_sub]
    have hR' : |(Rj : ℚ)| ≤ R := by exact_mod_cast hR
    have hX : 0 ≤ (D : ℚ) * 24 ^ (C.k + 1) * B + R := by positivity
    calc |(S : ℚ) - Rj| ≤ |(S : ℚ)| + |(Rj : ℚ)| := abs_sub _ _
      _ ≤ (D : ℚ) * 24 ^ (C.k + 1) * B + R := by
          rw [hSq, abs_mul, Nat.abs_cast, mul_assoc]
          exact add_le_add (mul_le_mul_of_nonneg_left hcl (Nat.cast_nonneg _)) hR'
      _ < ps.prod := by linarith
  have hnat : (S - Rj).natAbs < ps.prod := by
    have : (((S - Rj).natAbs : ℕ) : ℚ) < ps.prod := by
      rw [Nat.cast_natAbs, Int.cast_abs]; exact hbound
    exact_mod_cast this
  have hEq := eq_of_modEq_list S Rj ps hcop hmod hnat
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [eq_div_iff hDq, mul_comm, ← hSq, hEq]

/-- **The slack inequality from one integer check.** -/
theorem hslack_of_int (k d D : ℕ) (hD : 0 < D) (nuNum : ℤ) (nuDen : ℕ) (hnuDen : 0 < nuDen)
    (codes : ℕ → Finset ℕ) (Rint : ℕ → ℕ → ℤ) (Ssum : ℕ)
    (hS : ∑ f ∈ Finset.range 3, ∑ j ∈ codes f, |Rint f j| ≤ Ssum)
    (hchk : (((2 * d ^ k) ^ 4 * 786 ^ k * 496 * Ssum * nuDen : ℕ) : ℤ) ≤ nuNum * ((D * (8640 ^ k * 2880) : ℕ) : ℤ)) :
    (2 * (d : ℚ) ^ k) ^ 4 * Kq k * ∑ f ∈ Finset.range 3, ∑ j ∈ codes f, |(Rint f j : ℚ) / D| ≤
      (nuNum : ℚ) / nuDen := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hnq : (0 : ℚ) < nuDen := by exact_mod_cast hnuDen
  have hsum : ∑ f ∈ Finset.range 3, ∑ j ∈ codes f, |(Rint f j : ℚ) / D| =
      ((∑ f ∈ Finset.range 3, ∑ j ∈ codes f, |Rint f j| : ℤ) : ℚ) / D := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [abs_div, Nat.abs_cast]
  have hT : ((∑ f ∈ Finset.range 3, ∑ j ∈ codes f, |Rint f j| : ℤ) : ℚ) ≤ Ssum := by exact_mod_cast hS
  have hK : Kq k = (786 : ℚ) ^ k * 496 / ((8640 : ℚ) ^ k * 2880) := by
    unfold Kq; rw [div_pow]; ring
  have hchk' : ((2 * (d : ℚ) ^ k) ^ 4 * 786 ^ k * 496 * Ssum) * nuDen ≤ nuNum * ((8640 : ℚ) ^ k * 2880 * D) := by
    have h := (Int.cast_le (R := ℚ)).2 hchk
    push_cast at h
    convert h using 1
    ring
  rw [hsum, hK]
  have hpos : (0 : ℚ) < (8640 : ℚ) ^ k * 2880 * D := by positivity
  calc (2 * (d : ℚ) ^ k) ^ 4 * ((786 : ℚ) ^ k * 496 / ((8640 : ℚ) ^ k * 2880)) *
        (((∑ f ∈ Finset.range 3, ∑ j ∈ codes f, |Rint f j| : ℤ) : ℚ) / D)
      ≤ (2 * (d : ℚ) ^ k) ^ 4 * ((786 : ℚ) ^ k * 496 / ((8640 : ℚ) ^ k * 2880)) * ((Ssum : ℚ) / D) := by
        gcongr
    _ = ((2 * (d : ℚ) ^ k) ^ 4 * 786 ^ k * 496 * Ssum) / ((8640 : ℚ) ^ k * 2880 * D) := by
        field_simp
    _ ≤ (nuNum : ℚ) / nuDen := by
        rw [div_le_div_iff₀ hpos hnq]
        exact hchk'

lemma sum_range_getD_abs (l : List ℤ) :
    ∑ j ∈ Finset.range l.length, |l.getD j 0| = (((l.map Int.natAbs).sum : ℕ) : ℤ) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, Nat.cast_add, ← ih]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Int.natCast_natAbs]
    ring

/-- List form of the residual mass: with residuals read from lists (`Rint f j = (RL f).getD j 0`) and
`codes f = range (RL f).length`, the mass is a sum of list entries (one kernel evaluation). -/
theorem resMass_list (RL : ℕ → List ℤ) :
    ∑ f ∈ Finset.range 3, ∑ j ∈ Finset.range (RL f).length, |(RL f).getD j 0| =
      ((((RL 0).map Int.natAbs).sum + ((RL 1).map Int.natAbs).sum + ((RL 2).map Int.natAbs).sum : ℕ) : ℤ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, sum_range_getD_abs]
  push_cast
  ring

/-! ### Residuals stored at the representatives -/

/-- Residual of the class with code `j`: the entry of `vals` at the position of `j` in `reps`, 0 off the reps. -/
def RintOf (reps : List ℕ) (vals : List ℤ) (j : ℕ) : ℤ := if j ∈ reps then vals.getD (reps.idxOf j) 0 else 0

lemma sum_getD_abs_le (vals : List ℤ) (T : Finset ℕ) :
    ∑ i ∈ T, |vals.getD i 0| ≤ (((vals.map Int.natAbs).sum : ℕ) : ℤ) := by
  rw [← sum_range_getD_abs]
  rw [← Finset.sum_filter_of_ne (p := fun i => i < vals.length) (fun i _ hne => by
    by_contra h
    exact hne (by rw [NPT.Cert.Ident.getD_ge vals 0 i (by omega)]; simp))]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_) fun i _ _ => abs_nonneg _
  rw [Finset.mem_filter] at hi
  exact Finset.mem_range.2 hi.2

/-- **Residual mass from the representative list**: for any code range `N`, the residual mass of
`RintOf reps vals` is at most the mass of the list `vals` (no distinctness needed). -/
theorem resMass_reps_le (reps : List ℕ) (vals : List ℤ) (N : ℕ) :
    ∑ j ∈ Finset.range N, |RintOf reps vals j| ≤ (((vals.map Int.natAbs).sum : ℕ) : ℤ) := by
  have e : ∑ j ∈ Finset.range N, |RintOf reps vals j| =
      ∑ j ∈ (Finset.range N).filter (fun j => j ∈ reps), |vals.getD (reps.idxOf j) 0| := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold RintOf
    split_ifs <;> simp
  rw [e, ← Finset.sum_image (f := fun i => |vals.getD i 0|) (g := fun j => reps.idxOf j)]
  · exact sum_getD_abs_le vals _
  · intro x hx y _ hxy
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    exact (List.idxOf_inj hx.2).1 hxy

/-! ### Class sums from slices with offsets -/

/-- A class sum is the sum of its slice sums (slices = the letter of one leg). -/
theorem classSum_split {W : Type*} [Fintype W] (F : W → ℤ) (cls : W → ℕ) (sl : W → Fin 24) (c : ℕ) :
    ∑ w ∈ univ.filter (fun w => cls w = c), F w =
      ∑ j, ∑ w ∈ univ.filter (fun w => sl w = j ∧ cls w = c), F w := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun w => cls w = c)) (t := univ) (g := sl)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.filter_filter]
  exact Finset.sum_congr (Finset.filter_congr fun w _ => and_comm) fun _ _ => rfl

/-- **Exact class sums from slices with offsets** (native route). -/
theorem classSum_exact_of_slices {W : Type*} [Fintype W] (F : W → ℤ) (cls : W → ℕ) (sl : W → Fin 24)
    (off : Fin 24 → ℕ → ℤ) (Rc : ℕ → ℤ)
    (hsl : ∀ j c, ∑ w ∈ univ.filter (fun w => sl w = j ∧ cls w = c), F w = -off j c)
    (hoff : ∀ c, ∑ j, off j c = -Rc c) (c : ℕ) :
    ∑ w ∈ univ.filter (fun w => cls w = c), F w = Rc c := by
  rw [classSum_split F cls sl c, Finset.sum_congr rfl fun j _ => hsl j c, Finset.sum_neg_distrib, hoff c, neg_neg]

/-- **Class sums mod `p` from slices with offsets** (kernel route). -/
theorem classSum_mod_of_slices {W : Type*} [Fintype W] (F : W → ℤ) (cls : W → ℕ) (sl : W → Fin 24)
    (off : Fin 24 → ℕ → ℤ) (Rc : ℕ → ℤ) (p : ℤ)
    (hsl : ∀ j c, ∑ w ∈ univ.filter (fun w => sl w = j ∧ cls w = c), F w ≡ -off j c [ZMOD p])
    (hoff : ∀ c, ∑ j, off j c ≡ -Rc c [ZMOD p]) (c : ℕ) :
    ∑ w ∈ univ.filter (fun w => cls w = c), F w ≡ Rc c [ZMOD p] := by
  rw [classSum_split F cls sl c]
  have h1 : ∑ j, ∑ w ∈ univ.filter (fun w => sl w = j ∧ cls w = c), F w ≡ ∑ j, -off j c [ZMOD p] :=
    Int.ModEq.sum fun j _ => hsl j c
  have h2 : ∑ j, -off j c ≡ Rc c [ZMOD p] := by
    rw [Finset.sum_neg_distrib]
    have := (hoff c).neg
    rwa [neg_neg] at this
  exact h1.trans h2

end NPT.K4

#print axioms NPT.K4.resMass_list
#print axioms NPT.K4.classSum_of_modEq
#print axioms NPT.K4.hslack_of_int
#print axioms NPT.K4.resMass_reps_le
#print axioms NPT.K4.classSum_exact_of_slices
#print axioms NPT.K4.classSum_mod_of_slices
