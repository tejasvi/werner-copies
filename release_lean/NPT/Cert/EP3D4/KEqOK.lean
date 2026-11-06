/-
NPT.Cert.EP3D4.KEqOK — the equality tables `eqTabsK` are the certificate's `eqTabOf` tables (kernel checks `KEqT<i>`), hence
`eqTK eqTabsK cert = eqLocF cert` (as the d = 3 `KEqOK`).
-/
import NPT.Cert.EP3D4.KEqT0
import NPT.Cert.EP3D4.KEqT1
import NPT.Cert.EP3D4.KEqT2
import NPT.Cert.EP3D4.KEqT3
import NPT.Cert.EP3D4.KEqT4
import NPT.Cert.EP3D4.KEqT5
import NPT.Cert.EP3D4.KEqT6
import NPT.Cert.EP3D4.KEqT7
import NPT.Cert.EP3D4.KEqT8
import NPT.Cert.EP3D4.KEqT9
import NPT.Cert.EP3D4.KLem

open NPT.Cert.Ident NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.EP3D4

theorem eqTabsK_ok : ∀ e ∈ eqTabsK, ∃ N, e.2.2 = eqTabOf cert e.1 e.2.1 N := by
  intro e he
  simp only [eqTabsK, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨6, eqI0_eq.symm⟩
  · exact ⟨14, eqI1_eq.symm⟩
  · exact ⟨6, eqI2_eq.symm⟩
  · exact ⟨14, eqI3_eq.symm⟩
  · exact ⟨6, eqI4_eq.symm⟩
  · exact ⟨5, eqI5_eq.symm⟩
  · exact ⟨6, eqI6_eq.symm⟩
  · exact ⟨5, eqI7_eq.symm⟩
  · exact ⟨6, eqI8_eq.symm⟩
  · exact ⟨5, eqI9_eq.symm⟩

theorem eqTK_eqLocF : eqTK eqTabsK cert = eqLocF cert := eqTK_eq _ _ eqTabsK_ok

lemma heqTK : ∀ g ∈ eqs, ∀ P ∈ g.parts, ∀ l : Fin (3 + 1), ∀ p o,
    (eqTK eqTabsK cert (P.specs.getD l.val default) (nfN 4 l.val) p o : ℚ) =
      cert.eqLoc (P.specs.getD l.val default) (nf 3 4 l) p o := by
  rw [eqTK_eqLocF]; exact heqTF

end NPT.Cert.EP3D4
