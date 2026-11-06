/-
NPT.Cert.EP3D4.KLem — objective tables and equality maps against `NPT.Cert.Sem` for the kernel identity fact (the
proofs of `EP3D4.IdFact`, renamed so that the native identity fact can coexist).
-/
import NPT.Cert.EP3D4.IdDefs

open BigOperators Finset NPT.Cert.Ident NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.EP3D4

/-- Equality specs of kind 1 (Stiefel, auxiliary qubit) sit on the auxiliary leg. -/
theorem eqKindsK : eqs.all (fun g => g.parts.all fun P => (List.finRange 4).all fun l =>
    (P.specs.getD l.val default).kind == 0 || nfN 4 l.val == 2) = true := by decide +kernel

theorem LdenK_pos : 0 < Lden := by decide +kernel

lemma hzsTK (p : Fin 24) : (zsT p : ℚ) = 2 * Matrix.trace (VG ℚ 4 0 p) - Matrix.trace (VG ℚ 4 0 21 * VG ℚ 4 0 p) := by
  unfold zsT; push_cast; rw [trF_eq, trMulF_eq]

lemma hzaTK (p : Fin 24) : (zaT p : ℚ) = Matrix.trace (VG ℚ 2 0 21 * VG ℚ 2 0 p) := by
  unfold zaT; rw [trMulF_eq]

lemma heqTF : ∀ g ∈ eqs, ∀ P ∈ g.parts, ∀ l : Fin (3 + 1), ∀ p o,
    (eqLocF cert (P.specs.getD l.val default) (nfN 4 l.val) p o : ℚ) =
      cert.eqLoc (P.specs.getD l.val default) (nf 3 4 l) p o := by
  intro g hg P hP l p o
  have hk := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 eqKindsK g hg) P hP) l (List.mem_finRange l)
  simp only [Bool.or_eq_true, beq_iff_eq] at hk
  have : NeZero (nfN 4 l.val) := ⟨by unfold nfN; split_ifs <;> norm_num⟩
  rw [eqLocF_eq cert _ _ p o hk, nfN_eq]

end NPT.Cert.EP3D4
