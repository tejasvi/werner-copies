/-
NPT.Cert.Ident.IdFactGen — from the family checks to the class sums of `Λ`.
-/
import NPT.Cert.Ident.Assembly
import NPT.Cert.Ident.ObjEqF

open BigOperators Finset NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.Ident

/-- Position of a word: `w3·13824 + w2·576 + w1·24 + w0`. -/
def posW (w : Fin 4 → Fin 24) : ℕ := (w 3).val * 13824 + (w 2).val * 576 + (w 1).val * 24 + (w 0).val

/-- The word at a position. -/
def wordAt (q : ℕ) : Fin 4 → Fin 24 :=
  fun l => Fin.ofNat 24 (if l.val = 0 then q % 24 else if l.val = 1 then q / 24 % 24 else
    if l.val = 2 then q / 576 % 24 else q / 13824)

lemma posW_lt (w : Fin 4 → Fin 24) : posW w < 24 * slen := by
  unfold posW slen
  have := (w 0).isLt; have := (w 1).isLt; have := (w 2).isLt; have := (w 3).isLt
  omega

lemma wordAt_posW (w : Fin 4 → Fin 24) : wordAt (posW w) = w := by
  funext l
  apply Fin.ext
  have h0 := (w 0).isLt; have h1 := (w 1).isLt; have h2 := (w 2).isLt; have h3 := (w 3).isLt
  fin_cases l <;> simp [wordAt, posW, Fin.val_ofNat] <;> omega

lemma posW_wordAt (q : ℕ) (hq : q < 24 * slen) : posW (wordAt q) = q := by
  unfold posW wordAt slen at *
  simp [Fin.val_ofNat]
  omega

lemma wordAt_val (q : ℕ) (hq : q < 24 * slen) :
    ((wordAt q 0).val, (wordAt q 1).val, (wordAt q 2).val, (wordAt q 3).val) = wd q := by
  unfold wordAt wd slen at *
  simp [Fin.val_ofNat]
  omega

/-- Words ≃ positions. -/
def posEquiv : (Fin 4 → Fin 24) ≃ Fin (24 * slen) where
  toFun w := ⟨posW w, posW_lt w⟩
  invFun q := wordAt q
  left_inv w := wordAt_posW w
  right_inv q := Fin.ext (posW_wordAt q q.isLt)

lemma sum_words_filter (F : (Fin 4 → Fin 24) → ℚ) (P : (Fin 4 → Fin 24) → Prop) [DecidablePred P] :
    ∑ w ∈ univ.filter P, F w = ∑ q ∈ range (24 * slen), if P (wordAt q) then F (wordAt q) else 0 := by
  rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range (fun q => if P (wordAt q) then F (wordAt q) else 0)]
  exact Fintype.sum_equiv posEquiv _ _ fun w => by simp [posEquiv, wordAt_posW]


lemma famParts_rows (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : ∀ P ∈ famParts C zmul f gs zs za eqT, ∀ m, (P.S.rows m).length = 24 := by
  intro P hP m
  simp only [famParts, eqPartsF, List.mem_append, List.mem_map, List.mem_flatMap] at hP
  rcases hP with (⟨G, _, rfl⟩ | hP) | hP
  · exact localRowsF_length _ _ _
  · split_ifs at hP with hf
    · simp only [List.mem_singleton] at hP; subst hP; exact rank1Spec_rows _ _ m
    · simp at hP
  · obtain ⟨g, _, P', _, hP'⟩ := hP
    split_ifs at hP' with hf
    · simp only [List.mem_map] at hP'; obtain ⟨ol, _, rfl⟩ := hP'; exact rank1Spec_rows _ _ m
    · simp at hP'

/-- **Class sums of `Λ` vanish**, from the family check (certificate with `k = 3`, given by its fields). -/
theorem hsum_of_famCheck (d : ℕ) (types : List TypeD) (mods : List ModD) (eqs : List EqGroupD)
    (Z : List NPT.Cert.PBlock) (Lden : ℕ) (hd : 0 < d) (hL : 0 < Lden) (zmul f b : ℕ) (gs : List GrpF)
    (hG : ∀ G ∈ gs, grpOK ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ zmul G = true)
    (hperm : (gs.flatMap fun G => itemsOf G.tree).Perm (allItems ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ f))
    (zs za : Fin 24 → ℤ)
    (hzs : ∀ p, (zs p : ℚ) = 2 * Matrix.trace (VG ℚ d 0 p) - Matrix.trace (VG ℚ d 0 21 * VG ℚ d 0 p))
    (hza : ∀ p, (za p : ℚ) = Matrix.trace (VG ℚ 2 0 21 * VG ℚ 2 0 p))
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ)
    (heq : ∀ g ∈ eqs, ∀ P ∈ g.parts, ∀ l : Fin (3 + 1), ∀ p o,
      (eqT (P.specs.getD l.val default) (nfN d l.val) p o : ℚ) =
        CertD.eqLoc ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ (P.specs.getD l.val default) (nf 3 d l) p o)
    (cls : List ℕ) (t0 : AT)
    (hchk : famCheck b (famParts ⟨3, d, types, mods, eqs, Z, Lden, 2 * Lden⟩ zmul f gs zs za eqT) cls t0 = true)
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
  have hF := famCheck_sound b _ cls t0 hchk (famParts_rows C zmul f gs zs za eqT) (posW w₀) (posW_lt w₀)
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

end NPT.Cert.Ident
