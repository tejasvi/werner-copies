/-
NPT.K4.BlkSignR — sign of a multiplier type with record rules (five-family certificate): `NPT.Cert.Sem.CertD.blk_type_nonneg`
with the block operator `blockR` (rules given as `RuleRec` records instead of indices into `ruleTab`); same proof.
-/
import NPT.K4.Rule5
import NPT.Cert.BlkSign

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.Sem.CertD
open scoped ComplexOrder

namespace NPT.K4

/-- **Sign of a multiplier type**, record rules. -/
theorem blk_type_nonnegR (C : CertD) (t : TypeD) {R : ℕ} (ri : Fin R → Fin R → RuleRec) (fam : Fin R → Fin R → ℕ)
    (hkp : ∀ r s, posOf (ruleOf t r.val s.val).kpos = (ri r s).kp)
    (hlp : ∀ r s, posOf (ruleOf t r.val s.val).lpos = (ri r s).lp)
    (Y : ℕ → Matrix (GI (nf C.k C.d)) (GI (nf C.k C.d)) ℂ)
    (hM : (blockR ri fam Y).PosSemidef) (hZ : ((C.blkZ t).Zmat C.Lden).PosSemidef) :
    0 ≤ ∑ r : Fin R, ∑ s : Fin R, C.blkOp t r.val s.val (Y (fam r s)) := by
  set Z := (C.blkZ t).Zmat C.Lden
  set Wm := C.Wc t R
  set G := C.Gblk t R
  set N := Gᵀ * blockR ri fam Y * G
  have hN : N.PosSemidef := by
    have := hM.conjTranspose_mul_mul_same G
    rwa [Gblk_conjTranspose] at this
  have hQ : (Wmᵀ * N * Wm).PosSemidef := by
    have := hN.conjTranspose_mul_mul_same Wm
    rwa [Wc_conjTranspose] at this
  have e1 : ∑ r : Fin R, ∑ s : Fin R, C.blkOp t r.val s.val (Y (fam r s)) =
      ∑ x, ∑ y, (Wm * Z * Wmᵀ) x y * N x y := by
    simp only [blkOp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun ν _ => ?_
    rw [Bc_eq C t r s μ ν]
    have hNe : N (r, μ) (s, ν) = ((C.JG t)ᵀ * blockOf (blockR ri fam Y) r s * C.JG t) μ ν :=
      Gblk_entry C t _ r s μ ν
    rw [hNe, blockOf_blockR, hkp, hlp]
    congr 1
    simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have e2 : (Wm * (Zᵀ * Wmᵀ) * N).trace = (Zᵀ * (Wmᵀ * N * Wm)).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e1, sum_entry_mul, transpose_mul, transpose_mul, transpose_transpose, e2]
  exact trace_mul_psd_nonneg hZ.transpose hQ

end NPT.K4

#print axioms NPT.K4.blk_type_nonnegR
