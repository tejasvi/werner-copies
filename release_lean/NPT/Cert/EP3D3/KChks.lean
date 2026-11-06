/-
NPT.Cert.EP3D3.KChks — the mod-p kernel checks: families 0 and 2 as one statement per family, in the form
`KAssembly` consumes; family 1 from its ten split checks via `KAssemblyS.hsumS_f1`.
-/
import NPT.Cert.EP3D3.KChkW0_0
import NPT.Cert.EP3D3.KChkW1_0
import NPT.Cert.EP3D3.KChkW2_0
import NPT.Cert.EP3D3.KChkW3_0
import NPT.Cert.EP3D3.KChkW4_0
import NPT.Cert.EP3D3.KChk0_2
import NPT.Cert.EP3D3.KChk1_2
import NPT.Cert.EP3D3.KChk2_2
import NPT.Cert.EP3D3.KChk3_2
import NPT.Cert.EP3D3.KChk4_2
import NPT.Cert.EP3D3.KChk5_2
import NPT.Cert.EP3D3.KChk6_2
import NPT.Cert.EP3D3.KChk7_2
import NPT.Cert.EP3D3.KChk8_2
import NPT.Cert.EP3D3.KChk9_2
import NPT.Cert.EP3D3.KChkS0_1_0
import NPT.Cert.EP3D3.KChkS0_1_1
import NPT.Cert.EP3D3.KChkS1_1_0
import NPT.Cert.EP3D3.KChkS1_1_1
import NPT.Cert.EP3D3.KChkS2_1_0
import NPT.Cert.EP3D3.KChkS2_1_1
import NPT.Cert.EP3D3.KChkS3_1_0
import NPT.Cert.EP3D3.KChkS3_1_1
import NPT.Cert.EP3D3.KChkS4_1_0
import NPT.Cert.EP3D3.KChkS4_1_1
import NPT.Cert.EP3D3.KAssemblyS

open BigOperators Finset NPT.Cert.Ident NPT.Cert.Sem NPT.Cert.KR NPT.Brauer

namespace NPT.Cert.EP3D3

theorem hsumS_f1_done (w₀ : Fin (3 + 1) → Fin 24) :
    ∑ w ∈ univ.filter (fun w : Fin (3 + 1) → Fin 24 => cls1.getD (posW w) 0 = cls1.getD (posW w₀) 0),
      cert.Λ 1 w = 0 :=
  hsumS_f1 chkS_0_1_0 chkS_0_1_1 chkS_1_1_0 chkS_1_1_1 chkS_2_1_0 chkS_2_1_1 chkS_3_1_0 chkS_3_1_1 chkS_4_1_0 chkS_4_1_1 w₀

theorem chks_f0 : ∀ p ∈ psW, checkKR p bW (slicesKRB p zmul cert 0 gts0 (leafRowsC (certModR p zmul cert) (-(den3 3 : ℤ)))
    zsT zaT (eqTK eqTabsK cert) bW) cls0 t0_0 = true := by
  intro p hp
  simp only [psW, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact chkW_0_0
  · exact chkW_1_0
  · exact chkW_2_0
  · exact chkW_3_0
  · exact chkW_4_0

theorem chks_f2 : ∀ p ∈ ps3, checkKR p bK (slicesKR p zmul cert 2 gts2 (leafRowsC (certModR p zmul cert) (-(den3 3 : ℤ)))
    zsT zaT (eqTK eqTabsK cert) bK) cls2 t0_2 = true := by
  intro p hp
  simp only [ps3, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact chkK_0_2
  · exact chkK_1_2
  · exact chkK_2_2
  · exact chkK_3_2
  · exact chkK_4_2
  · exact chkK_5_2
  · exact chkK_6_2
  · exact chkK_7_2
  · exact chkK_8_2
  · exact chkK_9_2

end NPT.Cert.EP3D3
