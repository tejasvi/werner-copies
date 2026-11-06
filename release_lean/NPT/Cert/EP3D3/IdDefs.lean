/-
NPT.Cert.EP3D3.IdDefs — tables and parameters of the d = 3 identity check; see `NPT.Cert.EP3D3.IdFact`.
-/
import NPT.Cert.EP3D3.SemData
import NPT.Cert.EP3D3.GrpF
import NPT.Cert.Ident.Fast
import NPT.Cert.Ident.Witness

open BigOperators Finset NPT.Cert.Ident NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.EP3D3


/-- `Zq = zget · zmul + 2 · num` with `zmul = 2 Lden / 2^E` (`E = 171` for every block; checked in `grpOK`). -/
def zmul : ℕ := 2 * Lden / 2 ^ 171

/-- Objective tables: site factor `2 tr V_p − tr(V_21 V_p)` (n = 3), auxiliary factor `tr(V_21 V_p)` (n = 2). -/
def zsT (p : Fin 24) : ℤ := 2 * trF 3 p - trMulF 3 21 p
def zaT (p : Fin 24) : ℤ := trMulF 2 21 p

/-- Packing digit width (bits); `famCheck` checks the a-priori bound against it. -/
def bits : ℕ := 5500

/-- The parts of family `f` (rule groups `gs`, objective, equality entries). -/
def partsN (f : ℕ) (gs : List GrpF) : List Part := famPartsT cert zmul f gs zsT zaT (eqLocF cert)

/-- Equality specs of kind 1 (Stiefel, auxiliary qubit) sit on the auxiliary leg. -/
theorem eqKinds : eqs.all (fun g => g.parts.all fun P => (List.finRange 4).all fun l =>
    (P.specs.getD l.val default).kind == 0 || nfN 3 l.val == 2) = true := by decide +kernel

theorem Lden_pos : 0 < Lden := by decide +kernel

lemma hzsT (p : Fin 24) : (zsT p : ℚ) = 2 * Matrix.trace (VG ℚ 3 0 p) - Matrix.trace (VG ℚ 3 0 21 * VG ℚ 3 0 p) := by
  unfold zsT; push_cast; rw [trF_eq, trMulF_eq]

lemma hzaT (p : Fin 24) : (zaT p : ℚ) = Matrix.trace (VG ℚ 2 0 21 * VG ℚ 2 0 p) := by
  unfold zaT; rw [trMulF_eq]

lemma heqT : ∀ g ∈ eqs, ∀ P ∈ g.parts, ∀ l : Fin (3 + 1), ∀ p o,
    (eqLocF cert (P.specs.getD l.val default) (nfN 3 l.val) p o : ℚ) =
      cert.eqLoc (P.specs.getD l.val default) (nf 3 3 l) p o := by
  intro g hg P hP l p o
  have hk := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 eqKinds g hg) P hP) l (List.mem_finRange l)
  simp only [Bool.or_eq_true, beq_iff_eq] at hk
  have : NeZero (nfN 3 l.val) := ⟨by unfold nfN; split_ifs <;> norm_num⟩
  rw [eqLocF_eq cert _ _ p o hk, nfN_eq]


end NPT.Cert.EP3D3
