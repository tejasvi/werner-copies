/-
NPT.Cert.Ident.KRBoundMod — the crude bound of `KRBound` for the word values of the parts reduced mod `p`
(`famPartsMod`, ModP.lean) (for the packed mod-`p` checks). Every reduced block entry, every reduced
equality numerator and the reduced objective coefficient lies in `[0, p)`, so for `0 < p ≤ P`

`partsF_le_crudeBMod : |partsF (famPartsMod p zmul C f gs zs za eqT) w0 w1 w2 w3| ≤ crudeBMod C f gs zs za P` for all
words `w_l < 24`, provided every equality-map value is at most `eqB C n` (`eqLocF_le`), where `crudeBMod` is a sum over
the three kinds of parts of `term count × largest coefficient × largest value`:
* rule groups: `NG · (den3 · P) · (max|W|² · max|J|^8)`, `NG` = items × `nb² · (dim² · n^8)^4` (as in `crudeN`);
* objective (family 0): `1 · P · (max|zs|³ · max|za|)`;
* equality parts: `eqCount · (max|sign| · den3 · P) · (eqB(d)³ · eqB(2))`.
No block scan is needed (the reduced entries are bounded by `P` by construction), so `crudeBMod` is cheap in the kernel.
-/
import NPT.Cert.Ident.KRBound
import NPT.Cert.Ident.ModP

open BigOperators Finset NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.Ident

noncomputable section

lemma natAbs_emod_le (x : ℤ) (p P : ℕ) (hp : 0 < p) (hpP : p ≤ P) : (x % (p : ℤ)).natAbs ≤ P := by
  have h0 : 0 ≤ x % (p : ℤ) := Int.emod_nonneg x (by exact_mod_cast hp.ne')
  have h1 : x % (p : ℤ) < p := Int.emod_lt_of_pos x (by exact_mod_cast hp)
  have h2 : ((x % (p : ℤ)).natAbs : ℤ) < (p : ℤ) := by rw [Int.natAbs_of_nonneg h0]; exact h1
  have h3 : (x % (p : ℤ)).natAbs < p := by exact_mod_cast h2
  omega

lemma maxAbsI_le (rows : List (List ℤ)) (B : ℕ) (h : ∀ r ∈ rows, ∀ x ∈ r, x.natAbs ≤ B) : maxAbsI rows ≤ B := by
  rw [maxAbsI_eq]
  refine maxNat_le fun y hy => ?_
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
  exact maxNat_le fun z hz => by obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz; exact h r hr x hx

/-! ### The reduced data -/

lemma zqB_redBlock_le (p zmul P : ℕ) (hp : 0 < p) (hpP : p ≤ P) (b : NPT.Cert.PBlock) :
    zqB (redBlock p zmul b) 1 ≤ P := by
  unfold zqB
  have hu : maxNat ((redBlock p zmul b).uent.map fun e => e.2.2.natAbs) = 0 := rfl
  rw [hu, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
  refine maxAbsI_le _ _ fun r hr x hx => ?_
  change r ∈ redRows p zmul b at hr
  unfold redRows at hr
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hr
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
  exact natAbs_emod_le _ p P hp hpP

lemma zqBmax_certMod_le (C : CertD) (p zmul P : ℕ) (hp : 0 < p) (hpP : p ≤ P) : zqBmax (certMod p zmul C) 1 ≤ P := by
  unfold zqBmax
  refine maxNat_le fun y hy => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
  change b ∈ C.Z.map (redBlock p zmul) at hb
  obtain ⟨b0, -, rfl⟩ := List.mem_map.1 hb
  exact zqB_redBlock_le p zmul P hp hpP b0

lemma nbMax_certMod (C : CertD) (p zmul : ℕ) : nbMax (certMod p zmul C) = nbMax C := by
  unfold nbMax
  change maxNat ((C.Z.map (redBlock p zmul)).map fun b => b.n) = _
  rw [List.map_map]; rfl

lemma eqCount_certMod (C : CertD) (p zmul f : ℕ) : eqCount (certMod p zmul C) f = eqCount C f := by
  unfold eqCount
  change ((modEqs p C.eqs).flatMap fun g => g.parts.flatMap fun P => if P.fam = f then g.lam else []).length = _
  unfold modEqs
  rw [List.length_flatMap, List.length_flatMap, List.map_map]
  congr 1
  refine List.map_congr_left fun g _ => ?_
  simp only [Function.comp_apply, List.length_flatMap]
  congr 1
  refine List.map_congr_left fun P _ => ?_
  split_ifs <;> simp

/-- Largest `|sign|` of an equality part. -/
def eqSignMax (C : CertD) : ℕ := maxNat (C.eqs.flatMap fun g => g.parts.map fun P => P.sign.natAbs)

lemma eqCoefMax_certMod_le (C : CertD) (p zmul f P : ℕ) (hp : 0 < p) (hpP : p ≤ P) :
    eqCoefMax (certMod p zmul C) f ≤ eqSignMax C * den3 C.d * P := by
  unfold eqCoefMax
  refine maxNat_le fun x hx => ?_
  simp only [List.mem_flatMap] at hx
  obtain ⟨g, hg, P', hP', hx⟩ := hx
  split_ifs at hx with hf
  · obtain ⟨ol, hol, rfl⟩ := List.mem_map.1 hx
    change g ∈ modEqs p C.eqs at hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    obtain ⟨ol0, -, rfl⟩ := List.mem_map.1 hol
    have hs : P'.sign.natAbs ≤ eqSignMax C :=
      le_maxNat (List.mem_flatMap.2 ⟨g0, hg0, List.mem_map.2 ⟨P', hP', rfl⟩⟩)
    have hm := natAbs_emod_le ol0.2 p P hp hpP
    simp only [Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_natCast]
    exact Nat.mul_le_mul (Nat.mul_le_mul hs le_rfl) hm
  · simp at hx

lemma famPartsMod_rows (p zmul : ℕ) (C : CertD) (f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) :
    ∀ P ∈ famPartsMod p zmul C f gs zs za eqT, ∀ m, (P.S.rows m).length = 24 := by
  intro P hP m
  simp only [famPartsMod, eqPartsF, List.mem_append, List.mem_map, List.mem_flatMap] at hP
  rcases hP with (⟨G, _, rfl⟩ | hP) | hP
  · exact localRowsF_length _ _ _
  · split_ifs at hP with hf
    · simp only [List.mem_singleton] at hP; subst hP; exact rank1Spec_rows _ _ m
    · simp at hP
  · obtain ⟨g, _, P', _, hP'⟩ := hP
    split_ifs at hP' with hf
    · simp only [List.mem_map] at hP'; obtain ⟨ol, _, rfl⟩ := hP'; exact rank1Spec_rows _ _ m
    · simp at hP'

/-! ### The bound -/

/-- **Crude bound on the reduced word values** (`0 < p ≤ P`): rule groups + objective + equality parts, each
`term count × largest coefficient × largest value`. -/
def crudeBMod (C : CertD) (f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ) (P : ℕ) : ℕ :=
  (gs.map fun G => (itemsOf G.tree).length).sum *
      (nbMax C * nbMax C * (dimMax C * dimMax C * (nMax C ^ 4 * nMax C ^ 4)) ^ 4) * (den3 C.d * P) *
      (maxWall C ^ 2 * maxJall C ^ 8) +
    (if f = 0 then 1 else 0) * (P * (tabMax zs ^ 3 * tabMax za)) +
    eqCount C f * (eqSignMax C * den3 C.d * P * (eqB C C.d ^ 3 * eqB C 2))

/-- **Crude a-priori bound on the reduced word values** of family `f`, for `0 < p ≤ P` and every `eqT` bounded by
`eqB` (e.g. `eqLocF C`). -/
theorem partsF_le_crudeBMod (p zmul : ℕ) (C : CertD) (f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (heqT : ∀ sp n p o, |eqT sp n p o| ≤ (eqB C n : ℤ)) (P : ℕ)
    (hp : 0 < p) (hpP : p ≤ P) (w0 w1 w2 w3 : ℕ) (hw0 : w0 < 24) (hw1 : w1 < 24) (hw2 : w2 < 24) (hw3 : w3 < 24) :
    |partsF (famPartsMod p zmul C f gs zs za eqT) w0 w1 w2 w3| ≤ (crudeBMod C f gs zs za P : ℤ) := by
  refine le_trans (partsF_abs _ (famPartsMod_rows p zmul C f gs zs za eqT) w0 w1 w2 w3 hw0 hw1 hw2 hw3) ?_
  -- the rule-group parts
  have hgr' : (gs.map fun G => boundTree (ruleSpecF (certMod p zmul C) 1 (-(den3 C.d : ℤ)) G.kpos G.lpos) G.tree).sum ≤
      (gs.map fun G => (itemsOf G.tree).length).sum *
        (nbMax C * nbMax C * (dimMax C * dimMax C * (nMax C ^ 4 * nMax C ^ 4)) ^ 4) * (den3 C.d * P) *
        (maxWall C ^ 2 * maxJall C ^ 8) := by
    refine le_trans (groups_bound_le (certMod p zmul C) 1 gs) ?_
    rw [nbMax_certMod]
    exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (zqBmax_certMod_le C p zmul P hp hpP))) le_rfl
  -- the objective
  have hobj : boundTree (rank1Spec (objE zs za) ((2 * C.Lden : ℤ) % (p : ℤ))) rank1Tree ≤
      P * (tabMax zs ^ 3 * tabMax za) := by
    have hz : ∀ l < 3, ∀ q, (objE zs za l q).natAbs ≤ tabMax zs := by
      intro l hl q; simp only [objE, ite_eq_left hl]; exact le_tabMax zs q
    have ha : ∀ q, (objE zs za 3 q).natAbs ≤ tabMax za := by
      intro q; simp only [objE]; exact le_tabMax za q
    refine le_trans (boundTree_rank1_le _ _ _ _ _ _ (hz 0 (by norm_num)) (hz 1 (by norm_num)) (hz 2 (by norm_num)) ha) ?_
    have hc : ((2 * C.Lden : ℤ) % (p : ℤ)).natAbs ≤ P := natAbs_emod_le _ p P hp hpP
    calc ((2 * C.Lden : ℤ) % (p : ℤ)).natAbs * (tabMax zs * tabMax zs * tabMax zs * tabMax za)
        ≤ P * (tabMax zs * tabMax zs * tabMax zs * tabMax za) := Nat.mul_le_mul hc le_rfl
      _ = P * (tabMax zs ^ 3 * tabMax za) := by ring
  -- the equality parts
  have heq' : ((eqPartsF (certMod p zmul C) f eqT).map fun P => boundTree P.S P.tree).sum ≤
      eqCount C f * (eqSignMax C * den3 C.d * P * (eqB C C.d ^ 3 * eqB C 2)) := by
    refine le_trans (eq_bound_le (certMod p zmul C) f eqT heqT) ?_
    rw [eqCount_certMod]
    exact Nat.mul_le_mul le_rfl (Nat.mul_le_mul (eqCoefMax_certMod_le C p zmul f P hp hpP) le_rfl)
  -- assemble
  have hnat : partsBound (famPartsMod p zmul C f gs zs za eqT) ≤ crudeBMod C f gs zs za P := by
    unfold partsBound famPartsMod
    simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def]
    have hsum : (if f = 0 then [rank1Part (objE zs za) ((2 * C.Lden : ℤ) % (p : ℤ))] else []).map
        (fun P => boundTree P.S P.tree) =
        if f = 0 then [boundTree (rank1Spec (objE zs za) ((2 * C.Lden : ℤ) % (p : ℤ))) rank1Tree] else [] := by
      split_ifs <;> rfl
    rw [hsum]
    have hobj' : (if f = 0 then [boundTree (rank1Spec (objE zs za) ((2 * C.Lden : ℤ) % (p : ℤ))) rank1Tree]
        else []).sum ≤ (if f = 0 then 1 else 0) * (P * (tabMax zs ^ 3 * tabMax za)) := by
      split_ifs <;> simp [hobj]
    unfold crudeBMod
    exact add_le_add (add_le_add hgr' hobj') heq'
  exact_mod_cast hnat

/-- The reduced crude bound for the certificate's own equality maps (`eqT = eqLocF C`). -/
theorem partsF_le_crudeBMod_eqLocF (p zmul : ℕ) (C : CertD) (f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ) (P : ℕ)
    (hp : 0 < p) (hpP : p ≤ P) (w0 w1 w2 w3 : ℕ) (hw0 : w0 < 24) (hw1 : w1 < 24) (hw2 : w2 < 24) (hw3 : w3 < 24) :
    |partsF (famPartsMod p zmul C f gs zs za (eqLocF C)) w0 w1 w2 w3| ≤ (crudeBMod C f gs zs za P : ℤ) :=
  partsF_le_crudeBMod p zmul C f gs zs za (eqLocF C) (eqLocF_le C) P hp hpP w0 w1 w2 w3 hw0 hw1 hw2 hw3

end

end NPT.Cert.Ident
