/-
NPT.K4.Werner4 — the four-copy Werner corollary of the K4 certificate at t = 4979/10000.

`NPT.werner_four_copy_d3` (module `NPT.Main`) turns a certificate theorem `EP (Fin 4) 3 g` with `0 < g < 1` into the
statement that, given Costa Rico's criterion, the Werner state `ρ(3, α)` is not 4-copy distillable for
`α ∈ [−g, 1]`.  With `NPT.K4.D3T4979.EP_K4_4979` this holds for `g = 4979/10000`.
-/
import NPT.Main
import NPT.K4.Final4979

namespace NPT.K4

/-- **Four qutrit copies**: given Costa Rico's criterion, `ρ(3, α)` is not 4-copy distillable for
`−4979/10000 ≤ α ≤ 1`. -/
theorem werner_four_copy_4979 {D : ℕ → ℕ → ℝ → Prop} (hCR : NPT.CostaRico D) {α : ℝ}
    (hα : -(4979 / 10000 : ℝ) ≤ α) (h1 : α ≤ 1) : ¬ D 4 3 α :=
  NPT.werner_four_copy_d3 hCR (by norm_num) (by norm_num) NPT.K4.D3T4979.EP_K4_4979 hα h1

end NPT.K4

#print axioms NPT.K4.werner_four_copy_4979
