/-
NPT.Cert.Ident.PiSum — sums over dependent 4-tuples and over index pairs.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

open BigOperators Finset

namespace NPT.Cert.Ident

lemma sum_cons {R : Type*} [AddCommMonoid R] {n : ℕ} {α : Fin (n + 1) → Type*} [∀ i, Fintype (α i)]
    (F : (∀ i, α i) → R) : ∑ x, F x = ∑ a : α 0, ∑ y : (∀ i : Fin n, α i.succ), F (Fin.cons a y) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv α) _ _ fun p => rfl).symm

lemma sum_fin_zero {R : Type*} [AddCommMonoid R] {α : Fin 0 → Type*} [∀ i, Fintype (α i)]
    (F : (∀ i, α i) → R) : ∑ x, F x = F (fun i => i.elim0) := by
  rw [Fintype.sum_eq_single (fun i => i.elim0)]
  · intro x hx; exact absurd (funext fun i => i.elim0) hx
  
/-- Sums over dependent 4-tuples as four nested sums. -/
lemma sum_pi_four {R : Type*} [AddCommMonoid R] (d : Fin 4 → ℕ) (F : ((l : Fin 4) → Fin (d l)) → R) :
    ∑ x, F x = ∑ a : Fin (d 0), ∑ b : Fin (d 1), ∑ c : Fin (d 2), ∑ e : Fin (d 3),
      F (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons e (fun i => i.elim0))))) := by
  rw [sum_cons]; refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_cons]; refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum_cons]; refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum_cons]; refine Finset.sum_congr rfl fun e _ => ?_
  rw [sum_fin_zero]

lemma sum_range_mul' {R : Type*} [AddCommMonoid R] (f : ℕ → R) (d : ℕ) :
    ∀ m, ∑ i ∈ range (m * d), f i = ∑ μ ∈ range m, ∑ ν ∈ range d, f (μ * d + ν)
  | 0 => by simp
  | m + 1 => by rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul' f d m, Finset.sum_range_succ]

/-- Pairs `(μ, ν) ∈ [d]²` as a single index `μ·d + ν`. -/
lemma sum_pair {R : Type*} [AddCommMonoid R] (d : ℕ) (g : ℕ → ℕ → R) :
    ∑ μ ∈ range d, ∑ ν ∈ range d, g μ ν = ∑ i ∈ range (d * d), g (i / d) (i % d) := by
  rw [sum_range_mul' _ d d]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν hν => ?_
  have hν' := Finset.mem_range.1 hν
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hν', zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hν']

end NPT.Cert.Ident
