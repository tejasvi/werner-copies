/-
NPT.Cert.EP3D4.KAssembly — the d = 4 class sums of the UNSPLIT families [0, 2] from the mod-p kernel checks, with the crude bounds and
the per-modulus checks as hypotheses (as the d = 3 `KAssembly`; at d ≥ 4 every unsplit family
uses λ-box equality parts, `slicesKRB`/`hsum_of_checksB`, and the sparse item rows `leafRowsC2`).  Split families:
the split assembly.
-/
import NPT.Cert.Ident.KRIdFactB
import NPT.Cert.Ident.KRItem2
import NPT.Cert.EP3D4.KPrimes
import NPT.Cert.EP3D4.KGtsT
import NPT.Cert.EP3D4.KEqOK
import NPT.Cert.EP3D3.KClsLen
import NPT.Cert.EP3D4.IdKChecks

open BigOperators Finset NPT.Cert.Ident NPT.Cert.Sem NPT.Cert.KR NPT.Brauer

namespace NPT.Cert.EP3D4

theorem hsumK_f0 (B : ℕ)
    (hB : ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
      |partsF (famParts cert zmul 0 gs0 zsT zaT (eqTK eqTabsK cert)) w0 w1 w2 w3| ≤ B)
    (hBp : 24 * slen * B < ps4.prod)
    (hFmod : ∀ p ∈ ps4, ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
      |partsF (famPartsMod p zmul cert 0 gs0 zsT zaT (eqTK eqTabsK cert)) w0 w1 w2 w3| < 2 ^ (bK - 1))
    (hchecks : ∀ p ∈ ps4, checkKR p bK (slicesKRB p zmul cert 0 gts0 (leafRowsC2 (certModR p zmul cert) (-(den3 4 : ℤ)))
      zsT zaT (eqTK eqTabsK cert) bK) NPT.Cert.EP3D3.cls0 NPT.Cert.EP3D3.t0_0 = true)
    (w₀ : Fin (3 + 1) → Fin 24) :
    ∑ w ∈ univ.filter (fun w : Fin (3 + 1) → Fin 24 => NPT.Cert.EP3D3.cls0.getD (posW w) 0 = NPT.Cert.EP3D3.cls0.getD (posW w₀) 0),
      cert.Λ 0 w = 0 :=
  hsum_of_checksB 4 types mods eqs blocks Lden (by norm_num) LdenK_pos zmul 0 bK (by decide) gts0 htab0
    (by rw [gts0_fst]; exact List.all_eq_true.1 grpOK_k_f0) (by rw [gts0_fst]; exact itemsPerm_k_f0)
    zsT zaT hzsTK hzaTK (eqTK eqTabsK cert) heqTK
    (fun p => leafRowsC2 (certModR p zmul cert) (-(den3 4 : ℤ))) (fun p => leafRowsC2_LRShape _ _)
    (fun p d0 d1 d2 d3 items k => leafRowsC2_hleaf p zmul cert _ d0 d1 d2 d3 items k)
    ps4 ps4_coprime (by rw [gts0_fst]; exact hFmod) B (by rw [gts0_fst]; exact hB) hBp NPT.Cert.EP3D3.cls0 NPT.Cert.EP3D3.cls0_len
    NPT.Cert.EP3D3.t0_0 hchecks w₀

theorem hsumK_f2 (B : ℕ)
    (hB : ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
      |partsF (famParts cert zmul 2 gs2 zsT zaT (eqTK eqTabsK cert)) w0 w1 w2 w3| ≤ B)
    (hBp : 24 * slen * B < ps4.prod)
    (hFmod : ∀ p ∈ ps4, ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
      |partsF (famPartsMod p zmul cert 2 gs2 zsT zaT (eqTK eqTabsK cert)) w0 w1 w2 w3| < 2 ^ (bK - 1))
    (hchecks : ∀ p ∈ ps4, checkKR p bK (slicesKRB p zmul cert 2 gts2 (leafRowsC2 (certModR p zmul cert) (-(den3 4 : ℤ)))
      zsT zaT (eqTK eqTabsK cert) bK) NPT.Cert.EP3D3.cls2 NPT.Cert.EP3D3.t0_2 = true)
    (w₀ : Fin (3 + 1) → Fin 24) :
    ∑ w ∈ univ.filter (fun w : Fin (3 + 1) → Fin 24 => NPT.Cert.EP3D3.cls2.getD (posW w) 0 = NPT.Cert.EP3D3.cls2.getD (posW w₀) 0),
      cert.Λ 2 w = 0 :=
  hsum_of_checksB 4 types mods eqs blocks Lden (by norm_num) LdenK_pos zmul 2 bK (by decide) gts2 htab2
    (by rw [gts2_fst]; exact List.all_eq_true.1 grpOK_k_f2) (by rw [gts2_fst]; exact itemsPerm_k_f2)
    zsT zaT hzsTK hzaTK (eqTK eqTabsK cert) heqTK
    (fun p => leafRowsC2 (certModR p zmul cert) (-(den3 4 : ℤ))) (fun p => leafRowsC2_LRShape _ _)
    (fun p d0 d1 d2 d3 items k => leafRowsC2_hleaf p zmul cert _ d0 d1 d2 d3 items k)
    ps4 ps4_coprime (by rw [gts2_fst]; exact hFmod) B (by rw [gts2_fst]; exact hB) hBp NPT.Cert.EP3D3.cls2 NPT.Cert.EP3D3.cls2_len
    NPT.Cert.EP3D3.t0_2 hchecks w₀

end NPT.Cert.EP3D4
