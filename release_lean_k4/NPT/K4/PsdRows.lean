/-
NPT.K4.PsdRows — the PSD check of one multiplier block from its parts: the header conditions and the
dominance condition of every row, so that a large block (n ≈ 100-135) is checked row by row in separate kernel
declarations instead of one `O(n³)` declaration.
-/
import NPT.Cert.PsdSound

namespace NPT.K4

open NPT.Cert

/-- `PBlock.check` from the header conditions and the dominance of every row. -/
theorem check_of_rows (b : PBlock) (Lden UB : ℕ)
    (hhdr : (decide (UB ≤ 2 * b.F + b.E) && b.symOK && b.lenOK && b.uOK Lden UB) = true)
    (hr : ∀ i < b.n, b.rowOK UB i = true) : b.check Lden UB = true := by
  unfold PBlock.check
  simp only [Bool.and_eq_true] at hhdr ⊢
  refine ⟨hhdr, ?_⟩
  rw [List.all_eq_true]
  intro i hi
  exact hr i (List.mem_range.1 hi)

end NPT.K4
