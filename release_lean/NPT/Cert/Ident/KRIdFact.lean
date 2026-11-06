/-
NPT.Cert.Ident.KRIdFact — class sums of `Λ` vanish, from mod-`p` kernel checks: for each modulus `p` in a
pairwise-coprime list, the mod-`p` check of a family (`checkKR` on `slicesKR`) makes every class sum of the family's
word values `≡ 0 (mod p)` (`classSums_modP`); a bound `|class sum| < ∏ p` then forces it to vanish (CRT,
`eq_zero_of_modEq_list`), and `Λ_partsF` turns this into the class sums of `Λ` (`hsum_of_checks`).
-/
import NPT.Cert.Ident.KRFamily
import NPT.Cert.Ident.IdFactGen
import Mathlib.Data.Nat.ChineseRemainder

open BigOperators Finset NPT.Cert.Sem NPT.Cert.Ident NPT.Brauer

namespace NPT.Cert.KR

/-- **One modulus**: the check makes every class sum of the family's word values `≡ 0 (mod p)`. -/
theorem classSums_modP (p zmul : ℕ) (C : CertD) (f : ℕ) (gts : List (GrpF × List (List (List SInt))))
    (htab : ∀ Gt ∈ gts, Gt.2 = mkTab C Gt.1.kpos Gt.1.lpos (supps 2 Gt.1.kpos Gt.1.lpos) (supps 3 Gt.1.kpos Gt.1.lpos))
    (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (b : ℕ) (hb : 0 < b)
    (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (hlr : LRShape lr)
    (hleaf : ∀ d0 d1 d2 d3 items k, gv (lr d0 d1 d2 d3 items).flatten k =
      gv ((items.map (itemTF (certMod p zmul C) 1 (-(den3 C.d : ℤ)) d0 d1 d2 d3)).foldr addL []) k)
    (hF : ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
      |partsF (famPartsMod p zmul C f (gts.map Prod.fst) zs za eqT) w0 w1 w2 w3| < 2 ^ (b - 1))
    (cls : List ℕ) (hcls : cls.length = 24 * slen) (t0 : AT)
    (hchk : checkKR p b (slicesKR p zmul C f gts lr zs za eqT b) cls t0 = true) (q : ℕ) (hq : q < 24 * slen) :
    (∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      partsF (famParts C zmul f (gts.map Prod.fst) zs za eqT) (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2
      else 0)) ≡ 0 [ZMOD p] := by
  have h24 : ∀ x : ℕ, x % 24 < 24 := fun x => Nat.mod_lt _ (by norm_num)
  have hmod := checkKR_sound p b hb _ cls t0 hchk (partsF (famPartsMod p zmul C f (gts.map Prod.fst) zs za eqT))
    (slicesKR_gv p zmul C f gts htab zs za eqT b lr hlr hleaf)
    (fun q' hq' => hF _ _ _ _ (h24 _) (h24 _) (h24 _) (by unfold wd slen at *; simp only; omega)) hcls q hq
  refine Int.ModEq.trans ?_ hmod
  refine Int.ModEq.sum fun q' _ => ?_
  split_ifs
  · exact partsF_mod p zmul C f (gts.map Prod.fst) zs za eqT _ _ _ _
  · exact Int.ModEq.rfl

/-- **CRT**: an integer `≡ 0` modulo pairwise-coprime moduli with `|S| < ∏ p` is zero. -/
theorem eq_zero_of_modEq_list (S : ℤ) : ∀ (ps : List ℕ), ps.Pairwise Nat.Coprime →
    (∀ p ∈ ps, S ≡ 0 [ZMOD p]) → S.natAbs < ps.prod → S = 0 := by
  intro ps hcop hmod hlt
  have hdvd : ∀ (ps : List ℕ), ps.Pairwise Nat.Coprime → (∀ p ∈ ps, S ≡ 0 [ZMOD p]) → ps.prod ∣ S.natAbs := by
    intro ps
    induction ps with
    | nil => intro _ _; exact one_dvd _
    | cons p ps ih =>
      intro hc hm
      rw [List.pairwise_cons] at hc
      have hp : p ∣ S.natAbs := by
        have h1 := (hm p (by simp)).symm.dvd
        rw [sub_zero] at h1
        exact Int.natCast_dvd.mp h1
      have hps := ih hc.2 fun q hq => hm q (by simp [hq])
      rw [List.prod_cons]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.coprime_list_prod_right_iff.mpr hc.1) hp hps
  have := hdvd ps hcop hmod
  exact Int.natAbs_eq_zero.1 (Nat.eq_zero_of_dvd_of_lt this hlt)

/-- Class sums vanish, from the conversion of `hsum_of_famCheck`: the position-level statement implies the
statement on words. -/
theorem hsum_of_posSums (d : ℕ) (types : List TypeD) (mods : List ModD) (eqs : List EqGroupD)
    (Z : List NPT.Cert.PBlock) (Lden : ℕ) (hd : 0 < d) (hL : 0 < Lden) (zmul f : ℕ) (gs : List GrpF)
    (hG : ∀ G ∈ gs, grpOK ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ zmul G = true)
    (hperm : (gs.flatMap fun G => itemsOf G.tree).Perm (allItems ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ f))
    (zs za : Fin 24 → ℤ)
    (hzs : ∀ p, (zs p : ℚ) = 2 * Matrix.trace (VG ℚ d 0 p) - Matrix.trace (VG ℚ d 0 21 * VG ℚ d 0 p))
    (hza : ∀ p, (za p : ℚ) = Matrix.trace (VG ℚ 2 0 21 * VG ℚ 2 0 p))
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ)
    (heq : ∀ g ∈ eqs, ∀ P ∈ g.parts, ∀ l : Fin (3 + 1), ∀ p o,
      (eqT (P.specs.getD l.val default) (nfN d l.val) p o : ℚ) =
        CertD.eqLoc ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ (P.specs.getD l.val default) (nf 3 d l) p o)
    (cls : List ℕ)
    (hpos : ∀ q < 24 * slen, (∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      partsF (famParts ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ zmul f gs zs za eqT)
        (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0)) = 0)
    (w₀ : Fin (3 + 1) → Fin 24) :
    ∑ w ∈ univ.filter (fun w : Fin (3 + 1) → Fin 24 => cls.getD (posW w) 0 = cls.getD (posW w₀) 0),
      CertD.Λ ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ f w = 0 := by
  set C : CertD := ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ with hC
  have hK : ((2 * C.Lden * den3 C.d : ℕ) : ℚ) ≠ 0 := by
    have : 0 < 2 * C.Lden * den3 C.d := by
      unfold den3; simp only [hC]; positivity
    exact_mod_cast this.ne'
  have key : ∀ w : Fin (3 + 1) → Fin 24, C.Λ f w = ((partsF (famParts C zmul f gs zs za eqT)
      (w 0).val (w 1).val (w 2).val (w 3).val : ℤ) : ℚ) / ((2 * C.Lden * den3 C.d : ℕ) : ℚ) := by
    intro w
    rw [eq_div_iff hK]
    exact Λ_partsF C rfl rfl hd hL zmul f gs hG hperm zs za hzs hza eqT heq w
  rw [Finset.sum_congr rfl (fun w _ => key w), ← Finset.sum_div, div_eq_zero_iff]
  left
  rw [sum_words_filter (fun w => ((partsF (famParts C zmul f gs zs za eqT) (w 0).val (w 1).val (w 2).val (w 3).val
    : ℤ) : ℚ)) (fun w => cls.getD (posW w) 0 = cls.getD (posW w₀) 0)]
  have hF := hpos (posW w₀) (posW_lt w₀)
  have hconv : (∑ q ∈ range (24 * slen),
      if cls.getD (posW (wordAt q)) 0 = cls.getD (posW w₀) 0 then
        ((partsF (famParts C zmul f gs zs za eqT) (wordAt q 0).val (wordAt q 1).val (wordAt q 2).val
          (wordAt q 3).val : ℤ) : ℚ) else 0) =
      (((∑ q' ∈ range (24 * slen), if cls.getD q' 0 = cls.getD (posW w₀) 0 then
        partsF (famParts C zmul f gs zs za eqT) (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0) : ℤ) : ℚ) := by
    push_cast
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_range.1 hq
    rw [posW_wordAt q hq']
    have hv := wordAt_val q hq'
    have e0 : (wordAt q 0).val = (wd q).1 := congrArg Prod.fst hv
    have e1 : (wordAt q 1).val = (wd q).2.1 := congrArg (fun x => x.2.1) hv
    have e2 : (wordAt q 2).val = (wd q).2.2.1 := congrArg (fun x => x.2.2.1) hv
    have e3 : (wordAt q 3).val = (wd q).2.2.2 := congrArg (fun x => x.2.2.2) hv
    split_ifs with hc
    · rw [e0, e1, e2, e3]
    · rfl
  rw [hconv, hF]; simp

/-- `|Σ_{q'} [class] F| ≤ (24·slen) · B` when `|F| ≤ B` on all words. -/
theorem classSum_abs_le (cls : List ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℤ) (B : ℕ)
    (hB : ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 → |F w0 w1 w2 w3| ≤ B) (q : ℕ) :
    (∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      F (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0)).natAbs ≤ 24 * slen * B := by
  have h24 : ∀ x : ℕ, x % 24 < 24 := fun x => Nat.mod_lt _ (by norm_num)
  have : |∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      F (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0)| ≤ ((24 * slen * B : ℕ) : ℤ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ q' ∈ range (24 * slen), |(if cls.getD q' 0 = cls.getD q 0 then
        F (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0)| ≤ (B : ℤ) := by
      intro q' hq'
      have hq'' := Finset.mem_range.1 hq'
      split_ifs
      · exact hB _ _ _ _ (h24 _) (h24 _) (h24 _) (by unfold wd slen at *; simp only; omega)
      · simp
    refine le_trans (Finset.sum_le_sum hterm) ?_
    simp
  have h3 : ((∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      F (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0)).natAbs : ℤ) ≤ ((24 * slen * B : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]; exact this
  exact_mod_cast h3

/-- **Class sums of `Λ` vanish, from the mod-`p` kernel checks** (all moduli of `ps`, pairwise coprime). -/
theorem hsum_of_checks (d : ℕ) (types : List TypeD) (mods : List ModD) (eqs : List EqGroupD)
    (Z : List NPT.Cert.PBlock) (Lden : ℕ) (hd : 0 < d) (hL : 0 < Lden) (zmul f b : ℕ) (hb : 0 < b)
    (gts : List (GrpF × List (List (List SInt))))
    (htab : ∀ Gt ∈ gts, Gt.2 = mkTab ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ Gt.1.kpos Gt.1.lpos
      (supps 2 Gt.1.kpos Gt.1.lpos) (supps 3 Gt.1.kpos Gt.1.lpos))
    (hG : ∀ G ∈ gts.map Prod.fst, grpOK ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ zmul G = true)
    (hperm : ((gts.map Prod.fst).flatMap fun G => itemsOf G.tree).Perm
      (allItems ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ f))
    (zs za : Fin 24 → ℤ)
    (hzs : ∀ p, (zs p : ℚ) = 2 * Matrix.trace (VG ℚ d 0 p) - Matrix.trace (VG ℚ d 0 21 * VG ℚ d 0 p))
    (hza : ∀ p, (za p : ℚ) = Matrix.trace (VG ℚ 2 0 21 * VG ℚ 2 0 p))
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ)
    (heq : ∀ g ∈ eqs, ∀ P ∈ g.parts, ∀ l : Fin (3 + 1), ∀ p o,
      (eqT (P.specs.getD l.val default) (nfN d l.val) p o : ℚ) =
        CertD.eqLoc ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ (P.specs.getD l.val default) (nf 3 d l) p o)
    (lr : ℕ → ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (hlr : ∀ p, LRShape (lr p))
    (hleaf : ∀ p d0 d1 d2 d3 items k, gv (lr p d0 d1 d2 d3 items).flatten k =
      gv ((items.map (itemTF (certMod p zmul ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩) 1
        (-(den3 d : ℤ)) d0 d1 d2 d3)).foldr addL []) k)
    (ps : List ℕ) (hcop : ps.Pairwise Nat.Coprime)
    (hFmod : ∀ p ∈ ps, ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
      |partsF (famPartsMod p zmul ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ f (gts.map Prod.fst) zs za eqT)
        w0 w1 w2 w3| < 2 ^ (b - 1))
    (B : ℕ) (hB : ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
      |partsF (famParts ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ zmul f (gts.map Prod.fst) zs za eqT)
        w0 w1 w2 w3| ≤ B)
    (hBp : 24 * slen * B < ps.prod)
    (cls : List ℕ) (hcls : cls.length = 24 * slen) (t0 : AT)
    (hchecks : ∀ p ∈ ps, checkKR p b (slicesKR p zmul ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ f gts (lr p)
      zs za eqT b) cls t0 = true)
    (w₀ : Fin (3 + 1) → Fin 24) :
    ∑ w ∈ univ.filter (fun w : Fin (3 + 1) → Fin 24 => cls.getD (posW w) 0 = cls.getD (posW w₀) 0),
      CertD.Λ ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ f w = 0 := by
  refine hsum_of_posSums d types mods eqs Z Lden hd hL zmul f (gts.map Prod.fst) hG hperm zs za hzs hza eqT heq cls
    (fun q hq => ?_) w₀
  refine eq_zero_of_modEq_list _ ps hcop (fun p hp => ?_)
    (lt_of_le_of_lt (classSum_abs_le cls _ B hB q) hBp)
  exact classSums_modP p zmul _ f gts htab zs za eqT b hb (lr p) (hlr p) (hleaf p) (hFmod p hp) cls hcls t0
    (hchecks p hp) q hq

end NPT.Cert.KR
