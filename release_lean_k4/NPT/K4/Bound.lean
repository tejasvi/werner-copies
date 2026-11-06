/-
NPT.K4.Bound — a crude a-priori bound on the slack functional, for the CRT step of the mod-p route.

`abs_ΛS_le : |ΛS C α β nu f w| ≤ crudeS …` for every family and word, from data maxima that are cheap to check in
the kernel: `|W| ≤ BW` (all types), block sizes `≤ NB`, the DIAGONAL of every multiplier `Z_t ≤ BZ` (a PSD matrix
has `|Z_ac| ≤ (Z_aa + Z_cc)/2`, `norm_entry_le`, so no scan of the off-diagonal entries is needed), module
dimensions `≤ DM` and `max |J| ≤ BJ`.  Local maps reuse the EP_3 bounds (`Kmat_eq_kmatF`, `abs_kmatF_le`,
`eqLocF_eq`, `eqLocF_le`).  `abs_classSum_le` multiplies by the number of words `24^(k+1)`.

  `crudeS = objB + trB + typeMass · Bblk + eqMass / lamDen · EB^(k+1)`, where
  `Bblk = (DM^(k+1))² · NB² BW² BZ · (m^8 BJ²)^(k+1)` (`m = max d 2`), `EB = eqB C m`,
  `objB = ((α+β) d^8)^k 2^8 / (α^k (2d^k)^4)`, `trB = |nu| (m^4)^(k+1) / (2d^k)^4`,
  `typeMass = Σ_t nrows_t²`, `eqMass = Σ_g (Σ_P |sign_P|) · (Σ_o |λ_o|)`.
-/
import NPT.K4.SemS
import NPT.Cert.Ident.KRBound
import NPT.Cert.Ident.ObjEqF

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.Ident
open scoped ComplexOrder

namespace NPT.K4

/-! ### Generic facts -/

/-- An entry of a PSD matrix is at most the mean of the two diagonal entries. -/
lemma norm_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (hX : X.PosSemidef) (i j : ι) :
    ‖X i j‖ ≤ ((X i i).re + (X j j).re) / 2 := by
  have hH : ∀ I J, X I J = star (X J I) := fun I J => by
    rw [← Matrix.conjTranspose_apply, hX.1.eq]
  have hdi := (Complex.nonneg_iff.1 (hX.diag_nonneg (i := i))).1
  have hdj := (Complex.nonneg_iff.1 (hX.diag_nonneg (i := j))).1
  have hnorm : ‖X i j‖ = ‖X j i‖ := by rw [hH i j, norm_star]
  rw [hnorm]
  set S : ℂ := X j i with hS
  by_cases hS0 : S = 0
  · rw [hS0, norm_zero]; linarith
  set ω : ℂ := S / (‖S‖ : ℂ) with hω
  have hnS : (‖S‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hS0)
  have hq : 0 ≤ X i i - ω * X i j - star ω * X j i + ω * star ω * X j j := by
    have h := hX.dotProduct_mulVec_nonneg
      ((Pi.single i (1 : ℂ) : ι → ℂ) - ω • (Pi.single j (1 : ℂ) : ι → ℂ))
    convert h using 1
    simp only [star_sub, star_smul, Pi.star_single, star_one, Matrix.mulVec_sub, Matrix.mulVec_smul,
      sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, Matrix.mulVec_single_one,
      single_dotProduct, one_mul, smul_eq_mul, Matrix.col_apply]
    ring
  rw [hH i j, ← hS] at hq
  have hSS : S * star S = (‖S‖ : ℂ) ^ 2 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hstarn : star (‖S‖ : ℂ) = (‖S‖ : ℂ) := by rw [Complex.star_def, Complex.conj_ofReal]
  have hωω : ω * star ω = 1 := by
    rw [hω, star_div₀, hstarn, div_mul_div_comm, hSS]
    field_simp
  have hωS : ω * star S = (‖S‖ : ℂ) := by
    rw [hω, div_mul_eq_mul_div, hSS]
    field_simp
  have hSω : star ω * S = (‖S‖ : ℂ) := by
    rw [hω, star_div₀, hstarn, div_mul_eq_mul_div, mul_comm (star S) S, hSS]
    field_simp
  rw [hωω, one_mul, hωS, hSω] at hq
  have hre := (Complex.nonneg_iff.1 hq).1
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re] at hre
  linarith

lemma abs_list_sum_le {α : Type*} (L : List α) (g G : α → ℚ) (h : ∀ a ∈ L, |g a| ≤ G a) :
    |(L.map g).sum| ≤ (L.map G).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (h a (by simp)) (ih fun x hx => h x (by simp [hx])))

lemma list_sum_map_mul_right {α : Type*} (L : List α) (g : α → ℚ) (c : ℚ) :
    (L.map fun a => g a * c).sum = (L.map g).sum * c := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma abs_sub_sub_le (a b c : ℚ) : |a - b - c| ≤ |a| + |b| + |c| := by
  have h1 := abs_sub (a - b) c
  have h2 := abs_sub a b
  linarith

lemma cast_list_sum_map {α : Type*} (L : List α) (g : α → ℕ) :
    (((L.map g).sum : ℕ) : ℚ) = (L.map fun a => (g a : ℚ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]

lemma abs_ratCast_complex (q : ℚ) : ‖((q : ℚ) : ℂ)‖ = |(q : ℝ)| := by
  rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

/-! ### Local maps -/

lemma abs_VG_le (n : ℕ) (p : Fin 24) (a b : Fin 4 → Fin n) : |VG ℚ n 0 p a b| ≤ 1 := by
  rw [Ident.VG0_apply]; split_ifs <;> simp

lemma card_dig (n : ℕ) : (Fintype.card (Fin 4 → Fin n) : ℚ) = (n : ℚ) ^ 4 := by
  simp [Fintype.card_fin]

lemma abs_trace_VG_le (n : ℕ) (p : Fin 24) : |trace (VG ℚ n 0 p)| ≤ (n : ℚ) ^ 4 := by
  unfold Matrix.trace Matrix.diag
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |VG ℚ n 0 p i i| ≤ ∑ _i : Fin 4 → Fin n, (1 : ℚ) := Finset.sum_le_sum fun i _ => abs_VG_le n p i i
    _ = (n : ℚ) ^ 4 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_dig]

lemma abs_trace_VG21_le (n : ℕ) (p : Fin 24) : |trace (VG ℚ n 0 21 * VG ℚ n 0 p)| ≤ (n : ℚ) ^ 8 := by
  unfold Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |∑ j, VG ℚ n 0 21 i j * VG ℚ n 0 p j i|
      ≤ ∑ _i : Fin 4 → Fin n, ∑ _j : Fin 4 → Fin n, (1 : ℚ) := by
        refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        have h := mul_le_mul (abs_VG_le n 21 i j) (abs_VG_le n p j i) (abs_nonneg _) zero_le_one
        rwa [one_mul] at h
    _ = (n : ℚ) ^ 8 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_dig]; ring

lemma abs_Kmat_le (C : CertD) (hd : 0 < C.d) (l : Fin (C.k + 1)) (J : List (List ℤ)) (dim : ℕ)
    (kpos lpos : List ℕ) (p : Fin 24) (μ ν : Fin dim) {BJ : ℕ} (hJ : maxAbsI J ≤ BJ) :
    |Kmat (nf C.k C.d l) J dim kpos lpos p μ ν| ≤ ((max C.d 2 : ℕ) : ℚ) ^ 8 * (BJ : ℚ) ^ 2 := by
  have hn : 0 < nf C.k C.d l := by unfold nf; split_ifs <;> omega
  have hnm : nf C.k C.d l ≤ max C.d 2 := by unfold nf; split_ifs <;> omega
  haveI : NeZero (nf C.k C.d l) := ⟨hn.ne'⟩
  rw [Kmat_eq_kmatF]
  have h1 := abs_kmatF_le (nf C.k C.d l) J kpos lpos p μ ν
  have h2 : ((nf C.k C.d l) ^ 4 * (nf C.k C.d l) ^ 4 * maxAbsI J ^ 2 : ℕ) ≤ (max C.d 2) ^ 8 * BJ ^ 2 := by
    calc (nf C.k C.d l) ^ 4 * (nf C.k C.d l) ^ 4 * maxAbsI J ^ 2 = (nf C.k C.d l) ^ 8 * maxAbsI J ^ 2 := by ring
      _ ≤ (max C.d 2) ^ 8 * BJ ^ 2 := Nat.mul_le_mul (Nat.pow_le_pow_left hnm 8) (Nat.pow_le_pow_left hJ 2)
  have h3 : |(kmatF (nf C.k C.d l) J kpos lpos p μ ν : ℚ)| ≤ (((max C.d 2) ^ 8 * BJ ^ 2 : ℕ) : ℚ) := by
    have : |kmatF (nf C.k C.d l) J kpos lpos p μ ν| ≤ (((max C.d 2) ^ 8 * BJ ^ 2 : ℕ) : ℤ) :=
      h1.trans (by exact_mod_cast h2)
    exact_mod_cast this
  simpa using h3

lemma eqLoc_kind1 (C : CertD) (sp : EqSpecD) (hk : sp.kind ≠ 0) (n : ℕ) (p : Fin 24) (o : ℕ) :
    C.eqLoc sp n p o = C.eqLoc sp 2 p o := by
  unfold CertD.eqLoc
  simp only [hk, ↓reduceIte]

lemma eqB_mono (C : CertD) {n m : ℕ} (h : n ≤ m) : eqB C n ≤ eqB C m := by
  unfold eqB
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.pow_le_pow_left h 8) _)

lemma abs_eqLoc_le (C : CertD) (sp : EqSpecD) (n : ℕ) (hn : 2 ≤ n) (p : Fin 24) (o : ℕ) :
    |C.eqLoc sp n p o| ≤ (eqB C n : ℚ) := by
  by_cases hk : sp.kind = 0
  · haveI : NeZero n := ⟨by omega⟩
    rw [← eqLocF_eq C sp n p o (Or.inl hk)]
    exact_mod_cast eqLocF_le C sp n p o
  · rw [eqLoc_kind1 C sp hk n p o, ← eqLocF_eq C sp 2 p o (Or.inr rfl)]
    have h1 := eqLocF_le C sp 2 p o
    have h2 := eqB_mono C hn
    calc |(eqLocF C sp 2 p o : ℚ)| ≤ (eqB C 2 : ℚ) := by exact_mod_cast h1
      _ ≤ (eqB C n : ℚ) := by exact_mod_cast h2

/-! ### Blocks -/

section Blocks

variable (C : CertD)

lemma abs_zq_le (t : TypeD) (hpsd : ((C.blkZ t).Zmat C.Lden).PosSemidef) {BZ : ℚ}
    (hZ : ∀ a < (C.blkZ t).n, CertD.zq (C.blkZ t) C.Lden a a ≤ BZ) {a c : ℕ} (ha : a < (C.blkZ t).n)
    (hc : c < (C.blkZ t).n) : |CertD.zq (C.blkZ t) C.Lden a c| ≤ BZ := by
  have h := norm_entry_le _ hpsd ⟨a, ha⟩ ⟨c, hc⟩
  have e : ∀ x y : Fin (C.blkZ t).n, (C.blkZ t).Zmat C.Lden x y =
      ((CertD.zq (C.blkZ t) C.Lden x.val y.val : ℚ) : ℂ) := fun x y => rfl
  rw [e, e, e, abs_ratCast_complex, Complex.ratCast_re, Complex.ratCast_re] at h
  have h' : |CertD.zq (C.blkZ t) C.Lden a c| ≤
      (CertD.zq (C.blkZ t) C.Lden a a + CertD.zq (C.blkZ t) C.Lden c c) / 2 := by
    have : ((|CertD.zq (C.blkZ t) C.Lden a c| : ℚ) : ℝ) ≤
        (((CertD.zq (C.blkZ t) C.Lden a a + CertD.zq (C.blkZ t) C.Lden c c) / 2 : ℚ) : ℝ) := by
      push_cast; exact h
    exact_mod_cast this
  linarith [hZ a ha, hZ c hc]

lemma abs_Bq_le (t : TypeD) (hpsd : ((C.blkZ t).Zmat C.Lden).PosSemidef) {BW : ℕ}
    (hW : ∀ i j, |(t.W.getD i []).getD j 0| ≤ (BW : ℤ)) {BZ : ℚ}
    (hZ : ∀ a < (C.blkZ t).n, CertD.zq (C.blkZ t) C.Lden a a ≤ BZ) (r s μ ν : ℕ) :
    |C.Bq t r s μ ν| ≤ ((C.blkZ t).n : ℚ) ^ 2 * ((BW : ℚ) ^ 2 * BZ) := by
  have hW' : ∀ i j, |(((t.W.getD i []).getD j 0 : ℤ) : ℚ)| ≤ (BW : ℚ) := fun i j => by
    have := hW i j; exact_mod_cast this
  unfold CertD.Bq
  dsimp only
  change |∑ a ∈ range (C.blkZ t).n, ∑ c ∈ range (C.blkZ t).n, _| ≤ _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ a ∈ range (C.blkZ t).n, |∑ c ∈ range (C.blkZ t).n,
        ((t.W.getD (r * ∏ l, C.tdim t l + μ) []).getD a 0 : ℚ) * CertD.zq (C.blkZ t) C.Lden a c *
          ((t.W.getD (s * ∏ l, C.tdim t l + ν) []).getD c 0 : ℚ)|
      ≤ ∑ _a ∈ range (C.blkZ t).n, ∑ _c ∈ range (C.blkZ t).n, (BW : ℚ) ^ 2 * BZ := by
        refine Finset.sum_le_sum fun a ha => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun c hc => ?_)
        rw [abs_mul, abs_mul]
        have hz := abs_zq_le C t hpsd hZ (Finset.mem_range.1 ha) (Finset.mem_range.1 hc)
        calc |((t.W.getD (r * ∏ l, C.tdim t l + μ) []).getD a 0 : ℚ)| * |CertD.zq (C.blkZ t) C.Lden a c| *
              |((t.W.getD (s * ∏ l, C.tdim t l + ν) []).getD c 0 : ℚ)|
            ≤ (BW : ℚ) * BZ * BW := by
              apply mul_le_mul (mul_le_mul (hW' _ _) hz (abs_nonneg _) (by positivity)) (hW' _ _)
                (abs_nonneg _) (mul_nonneg (by positivity) ((abs_nonneg _).trans hz))
          _ = (BW : ℚ) ^ 2 * BZ := by ring
    _ = ((C.blkZ t).n : ℚ) ^ 2 * ((BW : ℚ) ^ 2 * BZ) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- The bound of one block entry. -/
noncomputable def Bblk (k d DM NB BW BJ : ℕ) (BZ : ℚ) : ℚ :=
  ((DM : ℚ) ^ (k + 1)) ^ 2 * ((NB : ℚ) ^ 2 * ((BW : ℚ) ^ 2 * BZ)) * (((max d 2 : ℕ) : ℚ) ^ 8 * (BJ : ℚ) ^ 2) ^ (k + 1)

lemma abs_blk_le (hd : 0 < C.d) (t : TypeD) (hpsd : ((C.blkZ t).Zmat C.Lden).PosSemidef) {BW : ℕ}
    (hW : ∀ i j, |(t.W.getD i []).getD j 0| ≤ (BW : ℤ)) {BZ : ℚ} (hBZ : 0 ≤ BZ)
    (hZ : ∀ a < (C.blkZ t).n, CertD.zq (C.blkZ t) C.Lden a a ≤ BZ) {NB DM BJ : ℕ} (hNB : (C.blkZ t).n ≤ NB)
    (hdim : ∀ l, C.tdim t l ≤ DM) (hJ : maxJall C ≤ BJ) (r s : ℕ) (w : Fin (C.k + 1) → Fin 24) :
    |C.blk t r s w| ≤ Bblk C.k C.d DM NB BW BJ BZ := by
  have hBq : ∀ μ ν, |C.Bq t r s μ ν| ≤ (NB : ℚ) ^ 2 * ((BW : ℚ) ^ 2 * BZ) := fun μ ν =>
    (abs_Bq_le C t hpsd hW hZ r s μ ν).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.pow_le_pow_left hNB 2) (by positivity))
  set KB : ℚ := ((max C.d 2 : ℕ) : ℚ) ^ 8 * (BJ : ℚ) ^ 2 with hKB
  have hK : ∀ μ ν : (l : Fin (C.k + 1)) → Fin (C.tdim t l),
      |∏ l, Kmat (nf C.k C.d l) (C.mods.getD (t.mods.getD l.val 0) default).J (C.tdim t l)
        ((t.rules.getD r []).getD s default).kpos ((t.rules.getD r []).getD s default).lpos (w l) (μ l) (ν l)|
        ≤ KB ^ (C.k + 1) := by
    intro μ ν
    rw [Finset.abs_prod]
    calc ∏ l, |Kmat (nf C.k C.d l) (C.mods.getD (t.mods.getD l.val 0) default).J (C.tdim t l)
          ((t.rules.getD r []).getD s default).kpos ((t.rules.getD r []).getD s default).lpos (w l) (μ l) (ν l)|
        ≤ ∏ _l : Fin (C.k + 1), KB :=
          Finset.prod_le_prod₀ (fun l _ => abs_nonneg _) fun l _ =>
            abs_Kmat_le C hd l _ _ _ _ _ _ _ ((maxAbsI_mods_le C _).trans hJ)
      _ = KB ^ (C.k + 1) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcard : (Fintype.card ((l : Fin (C.k + 1)) → Fin (C.tdim t l)) : ℚ) ≤ (DM : ℚ) ^ (C.k + 1) := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    push_cast
    calc ∏ l : Fin (C.k + 1), (C.tdim t l : ℚ) ≤ ∏ _l : Fin (C.k + 1), (DM : ℚ) :=
          Finset.prod_le_prod₀ (fun l _ => by positivity) fun l _ => by exact_mod_cast hdim l
      _ = (DM : ℚ) ^ (C.k + 1) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hKB0 : 0 ≤ KB := by positivity
  unfold CertD.blk
  dsimp only
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ μ : (l : Fin (C.k + 1)) → Fin (C.tdim t l), |∑ ν : (l : Fin (C.k + 1)) → Fin (C.tdim t l),
        C.Bq t r s (flatMI (C.tdim t) μ) (flatMI (C.tdim t) ν) *
          ∏ l, Kmat (nf C.k C.d l) (C.mods.getD (t.mods.getD l.val 0) default).J (C.tdim t l)
            ((t.rules.getD r []).getD s default).kpos ((t.rules.getD r []).getD s default).lpos (w l) (μ l) (ν l)|
      ≤ ∑ _μ : (l : Fin (C.k + 1)) → Fin (C.tdim t l), ∑ _ν : (l : Fin (C.k + 1)) → Fin (C.tdim t l),
          (NB : ℚ) ^ 2 * ((BW : ℚ) ^ 2 * BZ) * KB ^ (C.k + 1) := by
        refine Finset.sum_le_sum fun μ _ => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun ν _ => ?_)
        rw [abs_mul]
        exact mul_le_mul (hBq _ _) (hK μ ν) (abs_nonneg _) (by positivity)
    _ = (Fintype.card ((l : Fin (C.k + 1)) → Fin (C.tdim t l)) : ℚ) ^ 2 *
          ((NB : ℚ) ^ 2 * ((BW : ℚ) ^ 2 * BZ) * KB ^ (C.k + 1)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ ((DM : ℚ) ^ (C.k + 1)) ^ 2 * ((NB : ℚ) ^ 2 * ((BW : ℚ) ^ 2 * BZ) * KB ^ (C.k + 1)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcard 2) (by positivity)
    _ = Bblk C.k C.d DM NB BW BJ BZ := by unfold Bblk; rw [← hKB]; ring

end Blocks

/-! ### The functional -/

/-- `Σ_t nrows_t²`. -/
def typeMass (C : CertD) : ℕ := (C.types.map fun t => t.nrows ^ 2).sum

/-- `Σ_g (Σ_P |sign_P|) · (Σ_o |λ_o|)` (λ numerators). -/
def eqMass (C : CertD) : ℕ :=
  (C.eqs.map fun g => (g.parts.map fun P => P.sign.natAbs).sum * (g.lam.map fun ol => ol.2.natAbs).sum).sum

lemma abs_eqVal_le (C : CertD) (hd : 2 ≤ C.d) (g : EqGroupD) (P : EqPartD) (w : Fin (C.k + 1) → Fin 24) :
    |C.eqVal g P w| ≤ (((g.lam.map fun ol => ol.2.natAbs).sum : ℕ) : ℚ) / C.lamDen *
      (eqB C (max C.d 2) : ℚ) ^ (C.k + 1) := by
  set EB : ℚ := (eqB C (max C.d 2) : ℚ) with hEB
  have hloc : ∀ (ol : List ℕ × ℤ), |∏ l : Fin (C.k + 1),
      C.eqLoc (P.specs.getD l.val default) (nf C.k C.d l) (w l) (ol.1.getD l.val 0)| ≤ EB ^ (C.k + 1) := by
    intro ol
    rw [Finset.abs_prod]
    calc ∏ l : Fin (C.k + 1), |C.eqLoc (P.specs.getD l.val default) (nf C.k C.d l) (w l) (ol.1.getD l.val 0)|
        ≤ ∏ _l : Fin (C.k + 1), EB := by
          refine Finset.prod_le_prod₀ (fun l _ => abs_nonneg _) fun l _ => ?_
          have hn : 2 ≤ nf C.k C.d l := by unfold nf; split_ifs <;> omega
          have hnm : nf C.k C.d l ≤ max C.d 2 := by unfold nf; split_ifs <;> omega
          exact (abs_eqLoc_le C _ _ hn _ _).trans (by rw [hEB]; exact_mod_cast eqB_mono C hnm)
      _ = EB ^ (C.k + 1) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold CertD.eqVal
  refine (abs_list_sum_le _ _ (fun ol => (ol.2.natAbs : ℚ) / C.lamDen * EB ^ (C.k + 1)) fun ol _ => ?_).trans ?_
  · rw [abs_mul, abs_div, Nat.abs_cast]
    have h1 : |((ol.2 : ℤ) : ℚ)| = (ol.2.natAbs : ℚ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h1]
    exact mul_le_mul_of_nonneg_left (hloc ol) (by positivity)
  · rw [list_sum_map_mul_right]
    have e : (g.lam.map fun ol => (ol.2.natAbs : ℚ) / C.lamDen) =
        (g.lam.map fun ol => (ol.2.natAbs : ℚ) * (1 / C.lamDen)) := by
      congr 1; funext ol; ring
    rw [e, list_sum_map_mul_right]
    simp only [cast_list_sum_map]
    apply le_of_eq; ring

lemma abs_objT_le (C : CertD) (hd : 0 < C.d) (α β : ℕ) (w : Fin (C.k + 1) → Fin 24) :
    |objT C α β w| ≤ (((α : ℚ) + β) * (C.d : ℚ) ^ 8) ^ C.k * 2 ^ 8 / ((α : ℚ) ^ C.k * (2 * C.d ^ C.k) ^ 4) := by
  unfold objT
  rw [abs_div, abs_mul, Finset.abs_prod, abs_of_nonneg (by positivity : (0 : ℚ) ≤ (α : ℚ) ^ C.k * (2 * C.d ^ C.k) ^ 4)]
  have hd1 : (1 : ℚ) ≤ C.d := by exact_mod_cast hd
  have hsite : ∀ l : Fin C.k, |(α : ℚ) * trace (VG ℚ C.d 0 (w l.castSucc)) -
      (β : ℚ) * trace (VG ℚ C.d 0 21 * VG ℚ C.d 0 (w l.castSucc))| ≤ ((α : ℚ) + β) * (C.d : ℚ) ^ 8 := by
    intro l
    have h1 := abs_trace_VG_le C.d (w l.castSucc)
    have h2 := abs_trace_VG21_le C.d (w l.castSucc)
    have h48 : (C.d : ℚ) ^ 4 ≤ (C.d : ℚ) ^ 8 := pow_le_pow_right₀ hd1 (by norm_num)
    calc |(α : ℚ) * trace (VG ℚ C.d 0 (w l.castSucc)) - (β : ℚ) * trace (VG ℚ C.d 0 21 * VG ℚ C.d 0 (w l.castSucc))|
        ≤ |(α : ℚ) * trace (VG ℚ C.d 0 (w l.castSucc))| +
            |(β : ℚ) * trace (VG ℚ C.d 0 21 * VG ℚ C.d 0 (w l.castSucc))| := abs_sub _ _
      _ ≤ (α : ℚ) * (C.d : ℚ) ^ 8 + (β : ℚ) * (C.d : ℚ) ^ 8 := by
          rw [abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]
          exact add_le_add (mul_le_mul_of_nonneg_left (h1.trans h48) (by positivity))
            (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = ((α : ℚ) + β) * (C.d : ℚ) ^ 8 := by ring
  have hprod : ∏ l : Fin C.k, |(α : ℚ) * trace (VG ℚ C.d 0 (w l.castSucc)) -
      (β : ℚ) * trace (VG ℚ C.d 0 21 * VG ℚ C.d 0 (w l.castSucc))| ≤ (((α : ℚ) + β) * (C.d : ℚ) ^ 8) ^ C.k := by
    calc _ ≤ ∏ _l : Fin C.k, ((α : ℚ) + β) * (C.d : ℚ) ^ 8 :=
          Finset.prod_le_prod₀ (fun l _ => abs_nonneg _) fun l _ => hsite l
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have haux := abs_trace_VG21_le 2 (w (Fin.last C.k))
  have haux' : |trace (VG ℚ 2 0 21 * VG ℚ 2 0 (w (Fin.last C.k)))| ≤ 2 ^ 8 := by simpa using haux
  gcongr

lemma abs_trW_le (C : CertD) (w : Fin (C.k + 1) → Fin 24) :
    |trW C w| ≤ (((max C.d 2 : ℕ) : ℚ) ^ 4) ^ (C.k + 1) := by
  unfold trW
  rw [Finset.abs_prod]
  calc ∏ l : Fin (C.k + 1), |trace (VG ℚ (nf C.k C.d l) 0 (w l))| ≤ ∏ _l : Fin (C.k + 1), ((max C.d 2 : ℕ) : ℚ) ^ 4 := by
        refine Finset.prod_le_prod₀ (fun l _ => abs_nonneg _) fun l _ => (abs_trace_VG_le _ _).trans ?_
        have hnm : nf C.k C.d l ≤ max C.d 2 := by unfold nf; split_ifs <;> omega
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hnm) 4
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The crude bound** on the slack functional. -/
noncomputable def crudeS (C : CertD) (α β : ℕ) (nu : ℚ) (DM NB BW BJ : ℕ) (BZ : ℚ) : ℚ :=
  (((α : ℚ) + β) * (C.d : ℚ) ^ 8) ^ C.k * 2 ^ 8 / ((α : ℚ) ^ C.k * (2 * C.d ^ C.k) ^ 4)
  + |nu| * (((max C.d 2 : ℕ) : ℚ) ^ 4) ^ (C.k + 1) / (2 * C.d ^ C.k) ^ 4
  + (typeMass C : ℚ) * Bblk C.k C.d DM NB BW BJ BZ
  + (eqMass C : ℚ) / C.lamDen * (eqB C (max C.d 2) : ℚ) ^ (C.k + 1)

theorem abs_ΛS_le (C : CertD) (hd : 2 ≤ C.d) (α β : ℕ) (nu : ℚ)
    (hpsd : ∀ t ∈ C.types, ((C.blkZ t).Zmat C.Lden).PosSemidef)
    {BW : ℕ} (hW : ∀ t ∈ C.types, ∀ i j, |(t.W.getD i []).getD j 0| ≤ (BW : ℤ))
    {BZ : ℚ} (hBZ : 0 ≤ BZ) (hZ : ∀ t ∈ C.types, ∀ a < (C.blkZ t).n, CertD.zq (C.blkZ t) C.Lden a a ≤ BZ)
    {NB DM BJ : ℕ} (hNB : ∀ t ∈ C.types, (C.blkZ t).n ≤ NB) (hDM : ∀ t ∈ C.types, ∀ l, C.tdim t l ≤ DM)
    (hJ : maxJall C ≤ BJ) (f : ℕ) (w : Fin (C.k + 1) → Fin 24) :
    |ΛS C α β nu f w| ≤ crudeS C α β nu DM NB BW BJ BZ := by
  have hd0 : 0 < C.d := by omega
  have hL : (0 : ℚ) < (2 * C.d ^ C.k) ^ 4 := by positivity
  -- objective and trace term
  have hobj : |(if f = 0 then objT C α β w - nu * trW C w / (2 * C.d ^ C.k) ^ 4 else 0)| ≤
      (((α : ℚ) + β) * (C.d : ℚ) ^ 8) ^ C.k * 2 ^ 8 / ((α : ℚ) ^ C.k * (2 * C.d ^ C.k) ^ 4)
      + |nu| * (((max C.d 2 : ℕ) : ℚ) ^ 4) ^ (C.k + 1) / (2 * C.d ^ C.k) ^ 4 := by
    have h0 : 0 ≤ (((α : ℚ) + β) * (C.d : ℚ) ^ 8) ^ C.k * 2 ^ 8 / ((α : ℚ) ^ C.k * (2 * C.d ^ C.k) ^ 4) :=
      by positivity
    have h1 : 0 ≤ |nu| * (((max C.d 2 : ℕ) : ℚ) ^ 4) ^ (C.k + 1) / (2 * C.d ^ C.k) ^ 4 := by positivity
    split_ifs
    · refine (abs_sub _ _).trans (add_le_add (abs_objT_le C hd0 α β w) ?_)
      rw [abs_div, abs_mul, abs_of_pos hL]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (abs_trW_le C w) (abs_nonneg _)) hL.le
    · rw [abs_zero]; linarith
  -- blocks
  have hblk : |(C.types.map fun t => ∑ r ∈ range t.nrows, ∑ s ∈ range t.nrows,
      if ((t.rules.getD r []).getD s default).fam = f then C.blk t r s w else 0).sum| ≤
      (typeMass C : ℚ) * Bblk C.k C.d DM NB BW BJ BZ := by
    refine (abs_list_sum_le _ _ (fun t => (t.nrows : ℚ) ^ 2 * Bblk C.k C.d DM NB BW BJ BZ) fun t ht => ?_).trans ?_
    · have hb : ∀ r s, |(if ((t.rules.getD r []).getD s default).fam = f then C.blk t r s w else 0)| ≤
          Bblk C.k C.d DM NB BW BJ BZ := by
        intro r s
        have hB0 : 0 ≤ Bblk C.k C.d DM NB BW BJ BZ := (abs_nonneg _).trans
          (abs_blk_le C hd0 t (hpsd t ht) (hW t ht) hBZ (hZ t ht) (hNB t ht) (hDM t ht) hJ r s w)
        split_ifs
        · exact abs_blk_le C hd0 t (hpsd t ht) (hW t ht) hBZ (hZ t ht) (hNB t ht) (hDM t ht) hJ r s w
        · rw [abs_zero]; exact hB0
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ r ∈ range t.nrows, |∑ s ∈ range t.nrows,
            (if ((t.rules.getD r []).getD s default).fam = f then C.blk t r s w else 0)|
          ≤ ∑ _r ∈ range t.nrows, ∑ _s ∈ range t.nrows, Bblk C.k C.d DM NB BW BJ BZ :=
            Finset.sum_le_sum fun r _ => (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun s _ => hb r s)
        _ = (t.nrows : ℚ) ^ 2 * Bblk C.k C.d DM NB BW BJ BZ := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    · rw [list_sum_map_mul_right]
      unfold typeMass
      simp only [cast_list_sum_map, Nat.cast_pow]
      exact le_refl _
  -- equalities
  have heq : |(C.eqs.map fun g => (g.parts.map fun P =>
      if P.fam = f then (P.sign : ℚ) * C.eqVal g P w else 0).sum).sum| ≤
      (eqMass C : ℚ) / C.lamDen * (eqB C (max C.d 2) : ℚ) ^ (C.k + 1) := by
    set EBk : ℚ := (eqB C (max C.d 2) : ℚ) ^ (C.k + 1) with hEBk
    have hEBk0 : 0 ≤ EBk := by rw [hEBk]; positivity
    have hinner : ∀ g : EqGroupD, |(g.parts.map fun P =>
        if P.fam = f then (P.sign : ℚ) * C.eqVal g P w else 0).sum| ≤
        (((g.parts.map fun P => P.sign.natAbs).sum * (g.lam.map fun ol => ol.2.natAbs).sum : ℕ) : ℚ) *
          (EBk / C.lamDen) := by
      intro g
      refine (abs_list_sum_le g.parts (fun P => if P.fam = f then (P.sign : ℚ) * C.eqVal g P w else 0)
        (fun P => (P.sign.natAbs : ℚ) *
        ((((g.lam.map fun ol => ol.2.natAbs).sum : ℕ) : ℚ) / C.lamDen * EBk)) fun P _ => ?_).trans ?_
      · have hv := abs_eqVal_le C hd g P w
        split_ifs
        · rw [abs_mul]
          have h1 : |((P.sign : ℤ) : ℚ)| = (P.sign.natAbs : ℚ) := by rw [Nat.cast_natAbs, Int.cast_abs]
          rw [h1]
          exact mul_le_mul_of_nonneg_left hv (by positivity)
        · rw [abs_zero]; exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hEBk0)
      · rw [list_sum_map_mul_right, Nat.cast_mul]
        simp only [cast_list_sum_map]
        apply le_of_eq; ring
    refine (abs_list_sum_le C.eqs
      (fun g => (g.parts.map fun P => if P.fam = f then (P.sign : ℚ) * C.eqVal g P w else 0).sum)
      (fun g => (((g.parts.map fun P => P.sign.natAbs).sum *
      (g.lam.map fun ol => ol.2.natAbs).sum : ℕ) : ℚ) * (EBk / C.lamDen)) fun g _ => hinner g).trans ?_
    rw [list_sum_map_mul_right]
    unfold eqMass
    rw [cast_list_sum_map]
    apply le_of_eq; ring
  unfold ΛS
  refine (abs_sub_sub_le _ _ _).trans ?_
  have e : crudeS C α β nu DM NB BW BJ BZ =
      ((((α : ℚ) + β) * (C.d : ℚ) ^ 8) ^ C.k * 2 ^ 8 / ((α : ℚ) ^ C.k * (2 * C.d ^ C.k) ^ 4)
        + |nu| * (((max C.d 2 : ℕ) : ℚ) ^ 4) ^ (C.k + 1) / (2 * C.d ^ C.k) ^ 4)
      + (typeMass C : ℚ) * Bblk C.k C.d DM NB BW BJ BZ
      + (eqMass C : ℚ) / C.lamDen * (eqB C (max C.d 2) : ℚ) ^ (C.k + 1) := by
    unfold crudeS; ring
  rw [e]
  exact add_le_add (add_le_add hobj hblk) heq

/-- Class sums are at most `24^(k+1)` times the word bound. -/
theorem abs_classSum_le (C : CertD) (α β : ℕ) (nu : ℚ) (B : ℚ) (hB : ∀ f w, |ΛS C α β nu f w| ≤ B)
    (cls : (Fin (C.k + 1) → Fin 24) → ℕ) (f : ℕ) (j : ℕ) :
    |∑ w ∈ univ.filter (fun w => cls w = j), ΛS C α β nu f w| ≤ 24 ^ (C.k + 1) * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB f fun _ => 0)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ w ∈ univ.filter (fun w => cls w = j), |ΛS C α β nu f w|
      ≤ ∑ _w ∈ univ.filter (fun w => cls w = j), B := Finset.sum_le_sum fun w _ => hB f w
    _ = ((univ.filter (fun w => cls w = j)).card : ℚ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card (Fin (C.k + 1) → Fin 24) : ℚ) * B := by
        refine mul_le_mul_of_nonneg_right ?_ hB0
        exact_mod_cast Finset.card_le_univ _
    _ = 24 ^ (C.k + 1) * B := by simp [Fintype.card_fin]

end NPT.K4

#print axioms NPT.K4.abs_ΛS_le
#print axioms NPT.K4.abs_classSum_le
