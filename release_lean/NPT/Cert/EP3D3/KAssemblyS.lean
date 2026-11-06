/-
NPT.Cert.EP3D3.KAssemblyS — the class sums of family 1 from the split checks (two declarations per modulus,
offsets `KOff1_<i>`), via `KR.hsum_of_checks_split` and `Ident.hsplit_last`.
-/
import NPT.Cert.Ident.KRSplitAsm
import NPT.Cert.Ident.KRGlue
import NPT.Cert.EP3D3.KPrimesW
import NPT.Cert.EP3D3.KGtsS
import NPT.Cert.EP3D3.KGtsT
import NPT.Cert.EP3D3.KEqOK
import NPT.Cert.EP3D3.KClsLen
import NPT.Cert.EP3D3.IdKChecks
import NPT.Cert.EP3D3.KBoundW
import NPT.Cert.EP3D3.KOff1_0
import NPT.Cert.EP3D3.KOff1_1
import NPT.Cert.EP3D3.KOff1_2
import NPT.Cert.EP3D3.KOff1_3
import NPT.Cert.EP3D3.KOff1_4

open BigOperators Finset NPT.Cert.Ident NPT.Cert.Sem NPT.Cert.KR NPT.Brauer

namespace NPT.Cert.EP3D3

theorem gts1_cat (o : List ℕ) : (([(gts1_0, ([] : List Part), o)].map Prod.fst).flatten ++ gts1_1) = gts1 := rfl

theorem hsumS_f1
    (c00 : checkKRo pW_0 bW (slicesG pW_0 zmul cert gts1_0 (leafRowsC (certModR pW_0 zmul cert) (-(den3 3 : ℤ))) bW []) cls1 t0_1 offs1_0_0 = true)
    (c01 : checkKRo pW_0 bW (slicesG pW_0 zmul cert gts1_1 (leafRowsC (certModR pW_0 zmul cert) (-(den3 3 : ℤ))) bW (otherPartsModB pW_0 zmul cert 1 zsT zaT (eqTK eqTabsK cert))) cls1 t0_1 offs1_0_1 = true)
    (c10 : checkKRo pW_1 bW (slicesG pW_1 zmul cert gts1_0 (leafRowsC (certModR pW_1 zmul cert) (-(den3 3 : ℤ))) bW []) cls1 t0_1 offs1_1_0 = true)
    (c11 : checkKRo pW_1 bW (slicesG pW_1 zmul cert gts1_1 (leafRowsC (certModR pW_1 zmul cert) (-(den3 3 : ℤ))) bW (otherPartsModB pW_1 zmul cert 1 zsT zaT (eqTK eqTabsK cert))) cls1 t0_1 offs1_1_1 = true)
    (c20 : checkKRo pW_2 bW (slicesG pW_2 zmul cert gts1_0 (leafRowsC (certModR pW_2 zmul cert) (-(den3 3 : ℤ))) bW []) cls1 t0_1 offs1_2_0 = true)
    (c21 : checkKRo pW_2 bW (slicesG pW_2 zmul cert gts1_1 (leafRowsC (certModR pW_2 zmul cert) (-(den3 3 : ℤ))) bW (otherPartsModB pW_2 zmul cert 1 zsT zaT (eqTK eqTabsK cert))) cls1 t0_1 offs1_2_1 = true)
    (c30 : checkKRo pW_3 bW (slicesG pW_3 zmul cert gts1_0 (leafRowsC (certModR pW_3 zmul cert) (-(den3 3 : ℤ))) bW []) cls1 t0_1 offs1_3_0 = true)
    (c31 : checkKRo pW_3 bW (slicesG pW_3 zmul cert gts1_1 (leafRowsC (certModR pW_3 zmul cert) (-(den3 3 : ℤ))) bW (otherPartsModB pW_3 zmul cert 1 zsT zaT (eqTK eqTabsK cert))) cls1 t0_1 offs1_3_1 = true)
    (c40 : checkKRo pW_4 bW (slicesG pW_4 zmul cert gts1_0 (leafRowsC (certModR pW_4 zmul cert) (-(den3 3 : ℤ))) bW []) cls1 t0_1 offs1_4_0 = true)
    (c41 : checkKRo pW_4 bW (slicesG pW_4 zmul cert gts1_1 (leafRowsC (certModR pW_4 zmul cert) (-(den3 3 : ℤ))) bW (otherPartsModB pW_4 zmul cert 1 zsT zaT (eqTK eqTabsK cert))) cls1 t0_1 offs1_4_1 = true)
    (w₀ : Fin (3 + 1) → Fin 24) :
    ∑ w ∈ univ.filter (fun w : Fin (3 + 1) → Fin 24 => cls1.getD (posW w) 0 = cls1.getD (posW w₀) 0),
      cert.Λ 1 w = 0 := by
  refine hsum_of_checks_split 3 types mods eqs blocks Lden (by norm_num) Lden_pos zmul 1 bW (by decide) gs1
    (List.all_eq_true.1 grpOK_k_f1) itemsPerm_k_f1 zsT zaT hzsT hzaT (eqTK eqTabsK cert) heqTK
    (fun p => leafRowsC (certModR p zmul cert) (-(den3 3 : ℤ))) (fun p => leafRowsC_LRShape _ _)
    (fun p d0 d1 d2 d3 items k => leafRowsC_hleaf p zmul cert _ d0 d1 d2 d3 items k)
    psW psW_coprime KB (by rw [eqTK_eqLocF]; exact wordBound_f1) wordBound_prodW cls1 cls1_len t0_1 (fun p hp => ?_) w₀
  have heqB : ∀ sp n p o, |eqTK eqTabsK cert sp n p o| ≤ (eqB cert n : ℤ) := by
    rw [eqTK_eqLocF]; exact eqLocF_le cert
  have hpl := psW_pos_le p hp
  simp only [psW, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · refine hsplit_last pW_0 zmul cert 1 gs1 zsT zaT (eqTK eqTabsK cert) heqB bW (2 ^ 1200) hpl.1 hpl.2
      (leafRowsC (certModR pW_0 zmul cert) (-(den3 3 : ℤ))) cls1 t0_1 [(gts1_0, [], offs1_0_0)] (by simp) gts1_1
      offs1_0_1 (by rw [gts1_cat, gts1_fst]) (by rw [gts1_cat]; exact htab1) crudeBMod_ltW_f1 ?_ ?_
    · intro s hs
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hs
      rcases hs with rfl | rfl
      · exact c00
      · exact c01
    · intro j _
      have h := offsOK1_0 j
      simp only [List.map_cons, List.map_nil] at h
      simpa only [List.cons_append, List.nil_append, List.map_cons, List.map_nil] using h
  · refine hsplit_last pW_1 zmul cert 1 gs1 zsT zaT (eqTK eqTabsK cert) heqB bW (2 ^ 1200) hpl.1 hpl.2
      (leafRowsC (certModR pW_1 zmul cert) (-(den3 3 : ℤ))) cls1 t0_1 [(gts1_0, [], offs1_1_0)] (by simp) gts1_1
      offs1_1_1 (by rw [gts1_cat, gts1_fst]) (by rw [gts1_cat]; exact htab1) crudeBMod_ltW_f1 ?_ ?_
    · intro s hs
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hs
      rcases hs with rfl | rfl
      · exact c10
      · exact c11
    · intro j _
      have h := offsOK1_1 j
      simp only [List.map_cons, List.map_nil] at h
      simpa only [List.cons_append, List.nil_append, List.map_cons, List.map_nil] using h
  · refine hsplit_last pW_2 zmul cert 1 gs1 zsT zaT (eqTK eqTabsK cert) heqB bW (2 ^ 1200) hpl.1 hpl.2
      (leafRowsC (certModR pW_2 zmul cert) (-(den3 3 : ℤ))) cls1 t0_1 [(gts1_0, [], offs1_2_0)] (by simp) gts1_1
      offs1_2_1 (by rw [gts1_cat, gts1_fst]) (by rw [gts1_cat]; exact htab1) crudeBMod_ltW_f1 ?_ ?_
    · intro s hs
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hs
      rcases hs with rfl | rfl
      · exact c20
      · exact c21
    · intro j _
      have h := offsOK1_2 j
      simp only [List.map_cons, List.map_nil] at h
      simpa only [List.cons_append, List.nil_append, List.map_cons, List.map_nil] using h
  · refine hsplit_last pW_3 zmul cert 1 gs1 zsT zaT (eqTK eqTabsK cert) heqB bW (2 ^ 1200) hpl.1 hpl.2
      (leafRowsC (certModR pW_3 zmul cert) (-(den3 3 : ℤ))) cls1 t0_1 [(gts1_0, [], offs1_3_0)] (by simp) gts1_1
      offs1_3_1 (by rw [gts1_cat, gts1_fst]) (by rw [gts1_cat]; exact htab1) crudeBMod_ltW_f1 ?_ ?_
    · intro s hs
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hs
      rcases hs with rfl | rfl
      · exact c30
      · exact c31
    · intro j _
      have h := offsOK1_3 j
      simp only [List.map_cons, List.map_nil] at h
      simpa only [List.cons_append, List.nil_append, List.map_cons, List.map_nil] using h
  · refine hsplit_last pW_4 zmul cert 1 gs1 zsT zaT (eqTK eqTabsK cert) heqB bW (2 ^ 1200) hpl.1 hpl.2
      (leafRowsC (certModR pW_4 zmul cert) (-(den3 3 : ℤ))) cls1 t0_1 [(gts1_0, [], offs1_4_0)] (by simp) gts1_1
      offs1_4_1 (by rw [gts1_cat, gts1_fst]) (by rw [gts1_cat]; exact htab1) crudeBMod_ltW_f1 ?_ ?_
    · intro s hs
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_nil_iff, or_false] at hs
      rcases hs with rfl | rfl
      · exact c40
      · exact c41
    · intro j _
      have h := offsOK1_4 j
      simp only [List.map_cons, List.map_nil] at h
      simpa only [List.cons_append, List.nil_append, List.map_cons, List.map_nil] using h

end NPT.Cert.EP3D3
