/-
NPT.Main — integration of the published results.

Certificate-dependent statements take the certificate theorem as an explicit hypothesis `hcert` until the
corresponding `NPT.Cert.*` module proves it; then `hcert` is discharged by
`NPT.Cert.EP3_d3` etc. No `sorry` is used anywhere.
-/
import NPT.Reductions

namespace NPT

/-- Paper, Theorem 1.1 at `d = 3` (Werner form), given the certificate theorem `EP (Fin 3) 3 (1/2)`
and Costa Rico's criterion. -/
theorem werner_three_copy_d3 {D : ℕ → ℕ → ℝ → Prop} (hCR : CostaRico D)
    (hcert : EP (Fin 3) 3 (1 / 2)) {α : ℝ} (h0 : -1 ≤ α) (h1 : α ≤ 1) : D 3 3 α ↔ α < -1 / 2 :=
  werner_three_copy hCR 3 (by norm_num) hcert h0 h1

/-- A certificate in dimension `d` covers every smaller dimension (zero padding). -/
theorem EP3_of_le {d' d : ℕ} [NeZero d'] [NeZero d] (h : d' ≤ d) (hcert : EP (Fin 3) d (1 / 2)) :
    EP (Fin 3) d' (1 / 2) :=
  EP_mono_dim h hcert

/-- Four qutrit copies (paper, Theorem 1.3 part): from a certificate `EP (Fin 4) 3 g` with `0 < g < 1`,
`ρ(3,α)` is 4-copy undistillable for every `α ∈ [-g, 1]` (the release certifies `g = 4979/10000`). -/
theorem werner_four_copy_d3 {D : ℕ → ℕ → ℝ → Prop} (hCR : CostaRico D) {g : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hcert : EP (Fin 4) 3 g) {α : ℝ} (hα : -g ≤ α) (h1 : α ≤ 1) : ¬ D 4 3 α :=
  undistillable_of_EP hCR 4 3 hg hg1 hcert hα h1

/-- Five qutrit copies: from a certificate `EP (Fin 5) 3 g` (the release certifies `g = 47/100`). -/
theorem werner_five_copy_d3 {D : ℕ → ℕ → ℝ → Prop} (hCR : CostaRico D) {g : ℝ} (hg : 0 < g) (hg1 : g < 1)
    (hcert : EP (Fin 5) 3 g) {α : ℝ} (hα : -g ≤ α) (h1 : α ≤ 1) : ¬ D 5 3 α :=
  undistillable_of_EP hCR 5 3 hg hg1 hcert hα h1

end NPT
