/-
NPT.Product — product operators, the product formula, and the sharpness example.
-/
import NPT.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

open Matrix BigOperators Finset

namespace NPT

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- Single-copy squared Frobenius norm. -/
def frob1 (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := ∑ a, ∑ b, Complex.normSq (X a b)

/-- Single-copy form `q_1(t, X) = ‖X‖² - t |Tr X|²`. -/
def q1 (t : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) : ℝ := frob1 X - t * Complex.normSq (Matrix.trace X)

/-- Product operator `⊗_i C i`. -/
def tprod (C : ι → Matrix (Fin d) (Fin d) ℂ) : Op ι d := fun x y => ∏ i, C i (x i) (y i)

/-- Sum over pairs of multi-indices of a product factorizes. -/
lemma sum_sum_prod {R : Type*} [CommSemiring R] (h : ι → Fin d → Fin d → R) :
    (∑ x : Idx ι d, ∑ y : Idx ι d, ∏ i, h i (x i) (y i)) = ∏ i, ∑ a, ∑ b, h i a b := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.prod_sum]

/-- Partial trace of a product operator. -/
lemma ptrace_tprod [NeZero d] (J : Finset ι) (C : ι → Matrix (Fin d) (Fin d) ℂ) (x y : Idx ι d) :
    ptrace J (tprod C) x y =
      if ZeroOn J x ∧ ZeroOn J y then (∏ i ∈ J, Matrix.trace (C i)) * ∏ i ∈ Jᶜ, C i (x i) (y i)
      else 0 := by
  unfold ptrace
  split_ifs with h
  · have key : ∀ z : J → Fin d, (∏ i, C i (upd J x z i) (upd J y z i)) =
        (∏ i : J, C i (z i) (z i)) * ∏ i ∈ Jᶜ, C i (x i) (y i) := by
      intro z
      rw [← Finset.prod_mul_prod_compl J]
      congr 1
      · rw [← Finset.prod_coe_sort J]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp [upd, i.2]
      · refine Finset.prod_congr rfl fun i hi => ?_
        have hiJ : i ∉ J := by simpa using hi
        simp [upd, hiJ]
    simp only [tprod]
    simp_rw [key, ← Finset.sum_mul]
    congr 1
    rw [← Fintype.prod_sum (fun (i : J) (a : Fin d) => C i a a), ← Finset.prod_coe_sort J]
    rfl
  · rfl

/-- Squared Frobenius norm of a partial trace of a product operator. -/
lemma frobSq_ptrace_tprod [NeZero d] (J : Finset ι) (C : ι → Matrix (Fin d) (Fin d) ℂ) :
    frobSq (ptrace J (tprod C)) =
      Complex.normSq (∏ i ∈ J, Matrix.trace (C i)) * ∏ i ∈ Jᶜ, frob1 (C i) := by
  set T := ∏ i ∈ J, Matrix.trace (C i) with hT
  let h : ι → Fin d → Fin d → ℝ := fun i a b =>
    if i ∈ J then (if a = 0 ∧ b = 0 then 1 else 0) else Complex.normSq (C i a b)
  have hpt : ∀ x y : Idx ι d,
      Complex.normSq (ptrace J (tprod C) x y) = Complex.normSq T * ∏ i, h i (x i) (y i) := by
    intro x y
    rw [ptrace_tprod]
    split_ifs with hxy
    · rw [Complex.normSq_mul]
      congr 1
      rw [map_prod Complex.normSq, ← Finset.prod_mul_prod_compl J (fun i => h i (x i) (y i))]
      have h1 : ∏ i ∈ J, h i (x i) (y i) = 1 := by
        refine Finset.prod_eq_one fun i hi => ?_
        simp [h, hi, hxy.1 i hi, hxy.2 i hi]
      rw [h1, one_mul]
      apply Finset.prod_congr rfl
      intro i hi
      have hiJ : i ∉ J := by simpa using hi
      simp [h, hiJ]
    · rw [map_zero]
      symm
      apply mul_eq_zero_of_right
      push Not at hxy
      by_cases hx : ZeroOn J x
      · obtain ⟨i, hi, hyi⟩ := (by simpa [ZeroOn] using hxy hx : ∃ i ∈ J, y i ≠ 0)
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h, hi, hyi])
      · obtain ⟨i, hi, hxi⟩ := (by simpa [ZeroOn] using hx : ∃ i ∈ J, x i ≠ 0)
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h, hi, hxi])
  unfold frobSq
  simp_rw [hpt, ← Finset.mul_sum]
  rw [sum_sum_prod h]
  congr 1
  rw [← Finset.prod_mul_prod_compl J]
  have h1 : ∏ i ∈ J, ∑ a, ∑ b, h i a b = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    simp only [h, hi, ite_true, ite_and]
    simp
  rw [h1, one_mul]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hiJ : i ∉ J := by simpa using hi
  simp [h, hiJ, frob1]

/-- Product formula: `q_k(t, ⊗ C_i) = ∏ q_1(t, C_i)`. -/
theorem q_tprod [NeZero d] (t : ℝ) (C : ι → Matrix (Fin d) (Fin d) ℂ) :
    q t (tprod C) = ∏ i, q1 t (C i) := by
  have hq1 : ∀ i, q1 t (C i) = (-t * Complex.normSq (Matrix.trace (C i))) + frob1 (C i) := by
    intro i; simp [q1]; ring
  simp_rw [hq1]
  rw [Finset.prod_add, Finset.powerset_univ]
  unfold q
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [frobSq_ptrace_tprod, map_prod Complex.normSq, ← mul_assoc, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.compl_eq_univ_sdiff]

end NPT
