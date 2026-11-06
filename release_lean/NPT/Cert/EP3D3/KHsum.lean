/-
NPT.Cert.EP3D3.KHsum — the d = 3 class sums with the crude bounds plugged in (`KBound`, `KBoundW`);
only the per-modulus kernel checks remain as hypotheses.
-/
import NPT.Cert.EP3D3.KAssembly
import NPT.Cert.EP3D3.KBoundW

open BigOperators Finset NPT.Cert.Ident NPT.Cert.Sem NPT.Cert.KR NPT.Brauer

namespace NPT.Cert.EP3D3

theorem hsumC_f0
    (hchecks : ∀ p ∈ psW, checkKR p bW (slicesKRB p zmul cert 0 gts0 (leafRowsC (certModR p zmul cert) (-(den3 3 : ℤ)))
      zsT zaT (eqTK eqTabsK cert) bW) cls0 t0_0 = true)
    (w₀ : Fin (3 + 1) → Fin 24) :
    ∑ w ∈ univ.filter (fun w : Fin (3 + 1) → Fin 24 => cls0.getD (posW w) 0 = cls0.getD (posW w₀) 0),
      cert.Λ 0 w = 0 :=
  hsumK_f0 KB (by rw [eqTK_eqLocF]; exact wordBound_f0) wordBound_prodW (by rw [eqTK_eqLocF]; exact wordBoundModW_f0) hchecks w₀

theorem hsumC_f1
    (hchecks : ∀ p ∈ psW, checkKR p bW (slicesKRB p zmul cert 1 gts1 (leafRowsC (certModR p zmul cert) (-(den3 3 : ℤ)))
      zsT zaT (eqTK eqTabsK cert) bW) cls1 t0_1 = true)
    (w₀ : Fin (3 + 1) → Fin 24) :
    ∑ w ∈ univ.filter (fun w : Fin (3 + 1) → Fin 24 => cls1.getD (posW w) 0 = cls1.getD (posW w₀) 0),
      cert.Λ 1 w = 0 :=
  hsumK_f1 KB (by rw [eqTK_eqLocF]; exact wordBound_f1) wordBound_prodW (by rw [eqTK_eqLocF]; exact wordBoundModW_f1) hchecks w₀

theorem hsumC_f2
    (hchecks : ∀ p ∈ ps3, checkKR p bK (slicesKR p zmul cert 2 gts2 (leafRowsC (certModR p zmul cert) (-(den3 3 : ℤ)))
      zsT zaT (eqTK eqTabsK cert) bK) cls2 t0_2 = true)
    (w₀ : Fin (3 + 1) → Fin 24) :
    ∑ w ∈ univ.filter (fun w : Fin (3 + 1) → Fin 24 => cls2.getD (posW w) 0 = cls2.getD (posW w₀) 0),
      cert.Λ 2 w = 0 :=
  hsumK_f2 KB (by rw [eqTK_eqLocF]; exact wordBound_f2) wordBound_prod (by rw [eqTK_eqLocF]; exact wordBoundMod_f2) hchecks w₀

end NPT.Cert.EP3D3
