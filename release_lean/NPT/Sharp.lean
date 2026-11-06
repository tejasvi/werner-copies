/-
NPT.Sharp — the sharpness example at local dimension 2 (zero padding transports it to every d ≥ 2):
`C = 1₂ ⊗ |0⟩⟨1| ⊗ |0⟩⟨1|` has rank 2 and `q_3(t, C) = 2 - 4t`, negative for `t > 1/2`.
-/
import NPT.Product

open Matrix BigOperators Finset

namespace NPT

/-- `|0⟩⟨1|` on `ℂ²`. -/
def E01 : Matrix (Fin 2) (Fin 2) ℂ := fun a b => if a = 0 ∧ b = 1 then 1 else 0

/-- The example operator on three copies of `ℂ²`. -/
def Cex : Op (Fin 3) 2 := tprod ![(1 : Matrix (Fin 2) (Fin 2) ℂ), E01, E01]

lemma q1_one (t : ℝ) : q1 t (1 : Matrix (Fin 2) (Fin 2) ℂ) = 2 - 4 * t := by
  simp [q1, frob1, Matrix.trace, Matrix.one_apply]
  norm_num [Complex.normSq]
  ring

lemma q1_E01 (t : ℝ) : q1 t E01 = 1 := by
  simp only [q1, frob1, E01, Fin.sum_univ_two, Matrix.trace, Matrix.diag]
  norm_num

theorem q_Cex (t : ℝ) : q t Cex = 2 - 4 * t := by
  rw [Cex, q_tprod, Fin.prod_univ_three]
  simp [q1_one, q1_E01]

/-- Factor `A` of `Cex = A Bᴴ`. -/
def CexA : Matrix (Idx (Fin 3) 2) (Fin 2) ℂ :=
  Matrix.of fun x r => (if x 0 = r then 1 else 0) * (if x 1 = 0 then 1 else 0) * (if x 2 = 0 then 1 else 0)

/-- Factor `B` of `Cex = A Bᴴ`. -/
def CexB : Matrix (Idx (Fin 3) 2) (Fin 2) ℂ :=
  Matrix.of fun y r => (if y 0 = r then 1 else 0) * (if y 1 = 1 then 1 else 0) * (if y 2 = 1 then 1 else 0)

/-- `Cex` has rank at most two. -/
theorem rank_Cex : RankLE2 Cex := by
  refine ⟨CexA, CexB, ?_⟩
  ext x y
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Cex, tprod, Fin.prod_univ_three, CexA, CexB, Matrix.of_apply, Matrix.conjTranspose_apply,
    E01, Matrix.one_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  have h0 : ∀ a : Fin 2, a = 0 ∨ a = 1 := fun a => by fin_cases a <;> simp
  rcases h0 (x 0) with hx0 | hx0 <;> rcases h0 (y 0) with hy0 | hy0 <;>
    rcases h0 (x 1) with hx1 | hx1 <;> rcases h0 (y 1) with hy1 | hy1 <;>
    rcases h0 (x 2) with hx2 | hx2 <;> rcases h0 (y 2) with hy2 | hy2 <;>
    simp [hx0, hy0, hx1, hy1, hx2, hy2]

/-- Sharpness at `d = 2`: for `t > 1/2` the three-copy form takes a negative value on a rank-2 operator. -/
theorem not_EP3_d2_of_gt {t : ℝ} (ht : 1 / 2 < t) : ¬ EP (Fin 3) 2 t := by
  intro h
  have := h Cex rank_Cex
  rw [q_Cex] at this
  linarith

end NPT
