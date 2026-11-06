/-
NPT.Reductions — from the matrix inequality to Werner-state statements.

Costa Rico's criterion is NOT formalized: it enters as the hypothesis structure `CostaRico Distillable`,
where `Distillable k d α` is an abstract predicate standing for "the Werner state ρ(d, α) is k-copy
distillable". Everything else below is proved.
-/
import NPT.Sharp
import NPT.Padding
import NPT.Restrict

open Matrix BigOperators Finset

namespace NPT

/-- Costa Rico's criterion (P. Costa Rico, Lett. Math. Phys. 115:47 (2025), Theorem 1), as a hypothesis:
for `α ∈ [-1, 1]` the Werner state `ρ(d,α) = (I + αF)/(d² + αd)` is `k`-copy distillable iff some
rank-≤2 operator `C` on `k` copies of `ℂ^d` has `q_k(-α, C) < 0`. -/
structure CostaRico (Distillable : ℕ → ℕ → ℝ → Prop) : Prop where
  crit : ∀ (k d : ℕ) [NeZero d] (α : ℝ), -1 ≤ α → α ≤ 1 →
    (Distillable k d α ↔ ∃ C : Op (Fin k) d, RankLE2 C ∧ q (-α) C < 0)

/-- Sharpness in every dimension `d ≥ 2`: for `t > 1/2` some rank-2 operator on three copies has `q < 0`. -/
theorem exists_neg_q3 (d : ℕ) [NeZero d] (hd : 2 ≤ d) {t : ℝ} (ht : 1 / 2 < t) :
    ∃ C : Op (Fin 3) d, RankLE2 C ∧ q t C < 0 := by
  refine ⟨pad (d := d) Cex, rank_pad Cex rank_Cex, ?_⟩
  rw [q_pad hd, q_Cex]
  linarith

/-- If `EP` holds at `g ∈ (0, 1)` on `k` copies of `ℂ^d`, then `ρ(d,α)` is `k`-copy undistillable for
every `α ∈ [-g, 1]`. -/
theorem undistillable_of_EP {D : ℕ → ℕ → ℝ → Prop} (hCR : CostaRico D) (k d : ℕ) [NeZero d] {g : ℝ}
    (hg : 0 < g) (hg1 : g < 1) (hEP : EP (Fin k) d g) {α : ℝ} (hα : -g ≤ α) (hα1 : α ≤ 1) :
    ¬ D k d α := by
  intro hD
  obtain ⟨C, hC, hneg⟩ := (hCR.crit k d α (by linarith) hα1).1 hD
  by_cases ht : -α ≤ 0
  · exact absurd (q_nonneg_of_nonpos ht C) (not_le.mpr hneg)
  · have hEPt : EP (Fin k) d (-α) := EP_mono_t hg hg1 (by linarith) (by linarith) hEP
    exact absurd (hEPt C hC) (not_le.mpr hneg)

/-- Three-copy theorem in Werner form, from the matrix inequality at the endpoint:
`ρ(d,α)` is 3-copy distillable iff `α < -1/2`. -/
theorem werner_three_copy {D : ℕ → ℕ → ℝ → Prop} (hCR : CostaRico D) (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hEP : EP (Fin 3) d (1 / 2)) {α : ℝ} (hα0 : -1 ≤ α) (hα1 : α ≤ 1) :
    D 3 d α ↔ α < -1 / 2 := by
  constructor
  · intro hD
    by_contra hcon
    push Not at hcon
    exact undistillable_of_EP hCR 3 d (by norm_num) (by norm_num) hEP (by linarith) hα1 hD
  · intro hlt
    refine (hCR.crit 3 d α hα0 hα1).2 ?_
    exact exists_neg_q3 d hd (by linarith)

end NPT
