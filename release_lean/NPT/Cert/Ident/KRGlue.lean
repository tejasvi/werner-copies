/-
NPT.Cert.Ident.KRGlue — the leaf rows of `KRItem` satisfy the hypotheses of `hsum_of_checks`:
`LRShape (leafRowsC C coef)` and, on the reduced certificate, the `itemTF` values.
-/
import NPT.Cert.Ident.KRItem
import NPT.Cert.Ident.KRIdFact

open BigOperators NPT.Cert.Sem NPT.Cert.Ident

namespace NPT.Cert.KR

theorem leafRowsC_LRShape (C : CertD) (coef : Int) : LRShape (leafRowsC C coef) := by
  intro d0 d1 d2 d3 items
  by_cases hne : items = []
  · subst hne
    exact ⟨Or.inr rfl, fun r hr => by simp [leafRowsC, foldrR] at hr⟩
  · obtain ⟨hl, hr⟩ := leafRowsC_shape C coef d0 d1 d2 d3 items hne
    refine ⟨Or.inl hl, fun r hmem => ?_⟩
    rw [hr r hmem]; ring

theorem certMod_uent (p zmul : ℕ) (C : CertD) (i : ℕ) : ((certMod p zmul C).Z.getD i default).uent = [] := by
  have hZ : (certMod p zmul C).Z = C.Z.map (redBlock p zmul) := rfl
  rw [hZ]
  rcases Nat.lt_or_ge i C.Z.length with h | h
  · rw [getD_map_block _ _ _ h]; rfl
  · rw [(getD_map_block_out C.Z (redBlock p zmul) i h).1]; rfl

theorem leafRowsC_hleaf (p zmul : ℕ) (C : CertD) (coef : Int) (d0 d1 d2 d3 : ℕ) (items : List (ℕ × ℕ × ℕ)) (k : ℕ) :
    gv (leafRowsC (certModR p zmul C) coef d0 d1 d2 d3 items).flatten k =
      gv ((items.map (itemTF (certMod p zmul C) 1 coef d0 d1 d2 d3)).foldr addL []) k := by
  rw [certModR_eq]
  exact leafRowsC_gv _ coef d0 d1 d2 d3 items (fun it _ => certMod_uent p zmul C _) k

end NPT.Cert.KR
