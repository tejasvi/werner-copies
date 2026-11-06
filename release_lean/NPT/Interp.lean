/-
NPT.Interp — monotonicity in `t` (the paper's Lemma M2 / sc's Lemma 9.2), stated combinatorially:
`q t C = ∑_S (1 - t/g)^{|Sᶜ|} (t/g)^{|S|} Qpart g S C`, where `Qpart g S C` is the form with only the copies
in `S` traced at parameter `g` (the copies outside `S` are spectators).
-/
import NPT.Basic

open Matrix BigOperators Finset

namespace NPT

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- The form at parameter `g` with only the copies in `S` traced. -/
def Qpart [NeZero d] (g : ℝ) (S : Finset ι) (C : Op ι d) : ℝ :=
  ∑ J ∈ S.powerset, (-g) ^ J.card * frobSq (ptrace J C)

/-- Binomial identity: `∑_{S ⊇ J} (1-u)^{|Sᶜ|} u^{|S|} = u^{|J|}`. -/
lemma sum_superset_weights (u : ℝ) (J : Finset ι) :
    ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => J ⊆ S), (1 - u) ^ Sᶜ.card * u ^ S.card
      = u ^ J.card := by
  -- reindex S = J ∪ T with T ⊆ Jᶜ
  have hbij : ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => J ⊆ S), (1 - u) ^ Sᶜ.card * u ^ S.card
      = ∑ T ∈ Jᶜ.powerset, (1 - u) ^ (Jᶜ.card - T.card) * u ^ (J.card + T.card) := by
    refine Finset.sum_nbij' (fun S => S \ J) (fun T => J ∪ T) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_powerset]
      intro x hx; simp only [Finset.mem_sdiff] at hx; simp [hx.2]
    · intro T hT
      simp
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      exact Finset.union_sdiff_of_subset hS
    · intro T hT
      simp only [Finset.mem_powerset] at hT
      ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1 h2
        · exact h1
      · intro h1
        refine ⟨Or.inr h1, ?_⟩
        have := hT h1; simpa using this
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      have hcardS : S.card = J.card + (S \ J).card := by
        rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hS]
      have hcardc : Sᶜ.card = Jᶜ.card - (S \ J).card := by
        have h1 : Sᶜ.card = Fintype.card ι - S.card := Finset.card_compl S
        have h2 : Jᶜ.card = Fintype.card ι - J.card := Finset.card_compl J
        have h3 : S.card ≤ Fintype.card ι := Finset.card_le_univ S
        omega
      rw [hcardS, hcardc]
  rw [hbij]
  have : ∀ T ∈ Jᶜ.powerset, (1 - u) ^ (Jᶜ.card - T.card) * u ^ (J.card + T.card)
      = u ^ J.card * (u ^ T.card * (1 - u) ^ (Jᶜ.card - T.card)) := by
    intro T _; rw [pow_add]; ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_pow_mul_eq_add_pow]
  simp

/-- The interpolation identity. -/
theorem q_eq_sum_Qpart [NeZero d] (t g : ℝ) (hg : g ≠ 0) (C : Op ι d) :
    q t C = ∑ S : Finset ι, ((1 - t / g) ^ Sᶜ.card * (t / g) ^ S.card) * Qpart g S C := by
  unfold Qpart q
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun J => (Finset.univ : Finset (Finset ι)).filter (fun S => J ⊆ S))]
  · refine Finset.sum_congr rfl fun J _ => ?_
    have hrw : ∀ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => J ⊆ S),
        (1 - t / g) ^ Sᶜ.card * (t / g) ^ S.card * ((-g) ^ J.card * frobSq (ptrace J C))
          = ((1 - t / g) ^ Sᶜ.card * (t / g) ^ S.card) * ((-g) ^ J.card * frobSq (ptrace J C)) := by
      intro S _; ring
    rw [Finset.sum_congr rfl hrw, ← Finset.sum_mul, sum_superset_weights, ← mul_assoc, ← mul_pow]
    congr 2
    field_simp
  · intro S J
    simp [Finset.mem_powerset]

/-- If every partial form is nonnegative at `g`, then `q t C ≥ 0` for all `t ∈ [0, g]`. -/
theorem q_nonneg_of_Qpart [NeZero d] {t g : ℝ} (hg : 0 < g) (ht0 : 0 ≤ t) (htg : t ≤ g) (C : Op ι d)
    (hQ : ∀ S : Finset ι, 0 ≤ Qpart g S C) : 0 ≤ q t C := by
  rw [q_eq_sum_Qpart t g hg.ne' C]
  refine Finset.sum_nonneg fun S _ => mul_nonneg (mul_nonneg ?_ ?_) (hQ S)
  · apply pow_nonneg
    have : t / g ≤ 1 := by rw [div_le_one hg]; exact htg
    linarith
  · exact pow_nonneg (div_nonneg ht0 hg.le) _

end NPT
