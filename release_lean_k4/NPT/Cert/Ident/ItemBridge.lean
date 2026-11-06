/-
NPT.Cert.Ident.ItemBridge — the box form of one rule-group item equals `coef · 2Lden · blk`.
-/
import NPT.Cert.Ident.ItemF
import NPT.Cert.Ident.Paths

open BigOperators Finset NPT.Cert.Sem

namespace NPT.Cert.Ident

/-- Per-leg pairing `(μ_l, ν_l) ↦ μ_l·d_l + ν_l`. -/
def pairEquiv4 (d : Fin 4 → ℕ) :
    (((l : Fin 4) → Fin (d l)) × ((l : Fin 4) → Fin (d l))) ≃ ((l : Fin 4) → Fin (d l * d l)) where
  toFun p := fun l => finProdFinEquiv (p.1 l, p.2 l)
  invFun i := (fun l => (finProdFinEquiv.symm (i l)).1, fun l => (finProdFinEquiv.symm (i l)).2)
  left_inv p := by
    rcases p with ⟨μ, ν⟩
    simp only [Equiv.symm_apply_apply]
  right_inv i := by
    funext l
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

lemma sum_pi_pair4 {R : Type*} [AddCommMonoid R] (d : Fin 4 → ℕ)
    (F : ((l : Fin 4) → Fin (d l)) → ((l : Fin 4) → Fin (d l)) → R) :
    ∑ μ, ∑ ν, F μ ν = ∑ i : ((l : Fin 4) → Fin (d l * d l)),
      F (fun l => (finProdFinEquiv.symm (i l)).1) (fun l => (finProdFinEquiv.symm (i l)).2) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (pairEquiv4 d) _ _ fun p => by
    simp only [pairEquiv4, Equiv.coe_fn_mk, Equiv.symm_apply_apply]

lemma finProd_symm_val (m n : ℕ) (i : Fin (m * n)) :
    (finProdFinEquiv.symm i).1.val = i.val / n ∧ (finProdFinEquiv.symm i).2.val = i.val % n := by
  simp [finProdFinEquiv, Fin.divNat, Fin.modNat]


/-- Native rule-group spec (index-based local rows and item tensors). -/
def ruleSpecF (C : CertD) (zmul : ℕ) (coef : Int) (kpos lpos : List ℕ) : Spec where
  rows m := localRowsF (C.mods.getD m default) kpos lpos
  dimsq m := mdim C m * mdim C m
  leaf m1 m2 m3 lf := (lf.items.map (itemTF C zmul coef (mdim C lf.m0) (mdim C m1) (mdim C m2) (mdim C m3))).foldr addL []

lemma mr4_lt (d0 d1 d2 d3 a b c e : ℕ) (ha : a < d0) (hb : b < d1) (hc : c < d2) (he : e < d3) :
    mr4 d0 d1 d2 d3 a b c e < d0 * d1 * d2 * d3 := by
  unfold mr4
  exact idx_lt _ _ _ _ (idx_lt _ _ _ _ (idx_lt _ _ _ _ ha hb) hc) he

lemma flatMI_four (d : Fin (3 + 1) → ℕ) (μ : (l : Fin (3 + 1)) → Fin (d l)) :
    flatMI d μ = mr4 (d 0) (d 1) (d 2) (d 3) (μ 0) (μ 1) (μ 2) (μ 3) := by
  simp [flatMI, mr4, Fin.sum_univ_four, Fin.prod_univ_four]
  ring


/-- Sums over `(l : Fin (3+1)) → Fin (n l)` as four nested range sums of a function of the values. -/
lemma sum_pi_range4 {R : Type*} [AddCommMonoid R] (n : Fin (3 + 1) → ℕ) (F : ℕ → ℕ → ℕ → ℕ → R)
    (G : ((l : Fin (3 + 1)) → Fin (n l)) → R)
    (hG : ∀ i, G i = F (i 0) (i 1) (i 2) (i 3)) :
    ∑ i, G i = ∑ a ∈ range (n 0), ∑ b ∈ range (n 1), ∑ c ∈ range (n 2), ∑ e ∈ range (n 3), F a b c e := by
  rw [sum_pi_four n G]
  simp only [hG, Fin.cons_zero, Fin.cons_succ]
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range (n 1), ∑ c ∈ range (n 2), ∑ e ∈ range (n 3), F a b c e)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun b => ∑ c ∈ range (n 2), ∑ e ∈ range (n 3), F a b c e)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun c => ∑ e ∈ range (n 3), F a b c e)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun e => F a b c e)]
  rfl


lemma itemE_eq (C : CertD) (zmul : ℕ) (coef : ℤ) (d0 d1 d2 d3 ti r s i0 i1 i2 i3 : ℕ)
    (h0 : i0 < d0 * d0) (h1 : i1 < d1 * d1) (h2 : i2 < d2 * d2) (h3 : i3 < d3 * d3)
    (hz : 2 * C.Lden = zmul * 2 ^ (C.Z.getD (C.types.getD ti default).zi default).E) (hL : 0 < C.Lden) :
    (itemE C zmul coef d0 d1 d2 d3 (ti, r, s) (itemY C zmul d0 d1 d2 d3 (ti, r, s)) i0 i1 i2 i3 : ℚ) =
      coef * (2 * C.Lden) * ∑ a ∈ range (C.Z.getD (C.types.getD ti default).zi default).n,
        ∑ c ∈ range (C.Z.getD (C.types.getD ti default).zi default).n,
        (((C.types.getD ti default).W.getD (r * (d0 * d1 * d2 * d3) +
            mr4 d0 d1 d2 d3 (i0 / d0) (i1 / d1) (i2 / d2) (i3 / d3)) []).getD a 0 : ℚ) *
          CertD.zq (C.Z.getD (C.types.getD ti default).zi default) C.Lden a c *
          (((C.types.getD ti default).W.getD (s * (d0 * d1 * d2 * d3) +
            mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3)) []).getD c 0 : ℚ) := by
  have hpos : ∀ x y : ℕ, x < y * y → 0 < y := fun x y h => by
    rcases Nat.eq_zero_or_pos y with hy | hy
    · rw [hy] at h; simp at h
    · exact hy
  have hfn : mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3) < d0 * d1 * d2 * d3 :=
    mr4_lt _ _ _ _ _ _ _ _ (Nat.mod_lt _ (hpos _ _ h0)) (Nat.mod_lt _ (hpos _ _ h1)) (Nat.mod_lt _ (hpos _ _ h2))
      (Nat.mod_lt _ (hpos _ _ h3))
  unfold itemE itemY
  simp only
  rw [getD_range_map _ _ _ _ hfn]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [getD_range_map _ _ _ _ (Finset.mem_range.1 ha)]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [zqI_eq _ _ _ hz hL]
  ring

/-- The box form of one item (path `m3 → m2 → m1 → m0`, one item) at word `(w0, w1, w2, w3)`. -/
def boxItem (C : CertD) (zmul : ℕ) (coef : Int) (kpos lpos : List ℕ) (m0 m1 m2 m3 : ℕ) (it : ℕ × ℕ × ℕ)
    (w0 w1 w2 w3 : Fin 24) : Int :=
  ∑ i0 ∈ range (mdim C m0 * mdim C m0), ∑ i1 ∈ range (mdim C m1 * mdim C m1),
  ∑ i2 ∈ range (mdim C m2 * mdim C m2), ∑ i3 ∈ range (mdim C m3 * mdim C m3),
    aval (localRowsF (C.mods.getD m0 default) kpos lpos) w0.val i0 *
    aval (localRowsF (C.mods.getD m1 default) kpos lpos) w1.val i1 *
    aval (localRowsF (C.mods.getD m2 default) kpos lpos) w2.val i2 *
    aval (localRowsF (C.mods.getD m3 default) kpos lpos) w3.val i3 *
    itemE C zmul coef (mdim C m0) (mdim C m1) (mdim C m2) (mdim C m3) it
      (itemY C zmul (mdim C m0) (mdim C m1) (mdim C m2) (mdim C m3) it) i0 i1 i2 i3

theorem item_bridge (C : CertD) (hk : C.k = 3) (zmul : ℕ) (coef : ℤ) (ti r s m0 m1 m2 m3 : ℕ)
    (kpos lpos : List ℕ)
    (hmods : (C.types.getD ti default).mods = [m0, m1, m2, m3])
    (hkp : (((C.types.getD ti default).rules.getD r []).getD s default).kpos = kpos)
    (hlp : (((C.types.getD ti default).rules.getD r []).getD s default).lpos = lpos)
    (hn0 : (C.mods.getD m0 default).n = C.d) (hn1 : (C.mods.getD m1 default).n = C.d)
    (hn2 : (C.mods.getD m2 default).n = C.d) (hn3 : (C.mods.getD m3 default).n = 2) (hd : 0 < C.d)
    (hz : 2 * C.Lden = zmul * 2 ^ (C.Z.getD (C.types.getD ti default).zi default).E) (hL : 0 < C.Lden)
    (w : Fin (C.k + 1) → Fin 24) :
    ((boxItem C zmul coef kpos lpos m0 m1 m2 m3 (ti, r, s) (w 0) (w 1) (w 2) (w 3) : ℤ) : ℚ) =
      coef * (2 * C.Lden) * C.blk (C.types.getD ti default) r s w := by
  obtain ⟨k, d, types, mods, eqs, Z, Lden, lamDen⟩ := C
  simp only at hk
  subst hk
  set t := types.getD ti default with ht
  let C : CertD := ⟨3, d, types, mods, eqs, Z, Lden, lamDen⟩
  have hdim : ∀ l : Fin (3 + 1), C.tdim t l = mdim C (t.mods.getD l.val 0) := fun l => rfl
  have hm0 : t.mods.getD 0 0 = m0 := by rw [hmods]; rfl
  have hm1 : t.mods.getD 1 0 = m1 := by rw [hmods]; rfl
  have hm2 : t.mods.getD 2 0 = m2 := by rw [hmods]; rfl
  have hm3 : t.mods.getD 3 0 = m3 := by rw [hmods]; rfl
  unfold CertD.blk
  simp only [hkp, hlp]
  rw [sum_pi_pair4, Finset.mul_sum]
  set d0 := mdim C m0; set d1 := mdim C m1; set d2 := mdim C m2; set d3 := mdim C m3
  have hn : ∀ l : Fin (3 + 1), (C.mods.getD (t.mods.getD l.val 0) default).n = nf 3 d l := by
    intro l; fin_cases l
    · simp only [hm0]; exact hn0
    · simp only [hm1]; exact hn1
    · simp only [hm2]; exact hn2
    · simp only [hm3]; exact hn3
  have hd' : 0 < d := hd
  have hnz : ∀ l : Fin (3 + 1), NeZero (nf 3 d l) := by
    intro l; constructor; unfold nf; split_ifs <;> omega
  -- the summand as a function of the four pair indices
  let T := fun l : Fin (3 + 1) => C.tdim t l
  let J := fun l : Fin (3 + 1) => (C.mods.getD (t.mods.getD l.val 0) default).J
  let F : ℕ → ℕ → ℕ → ℕ → ℚ := fun a b c e =>
    (coef : ℚ) * (2 * Lden) * (C.Bq t r s (mr4 (T 0) (T 1) (T 2) (T 3) (a / T 0) (b / T 1) (c / T 2) (e / T 3))
      (mr4 (T 0) (T 1) (T 2) (T 3) (a % T 0) (b % T 1) (c % T 2) (e % T 3)) *
      ((kmatF (nf 3 d 0) (J 0) kpos lpos (w 0) (a / T 0) (a % T 0) : ℚ) *
       ((kmatF (nf 3 d 1) (J 1) kpos lpos (w 1) (b / T 1) (b % T 1) : ℚ) *
       ((kmatF (nf 3 d 2) (J 2) kpos lpos (w 2) (c / T 2) (c % T 2) : ℚ) *
       (kmatF (nf 3 d 3) (J 3) kpos lpos (w 3) (e / T 3) (e % T 3) : ℚ)))))
  rw [sum_pi_range4 (fun l => C.tdim t l * C.tdim t l) F]
  · have hT0 : C.tdim t 0 = d0 := by show mdim C (t.mods.getD 0 0) = d0; rw [hm0]
    have hT1 : C.tdim t 1 = d1 := by show mdim C (t.mods.getD 1 0) = d1; rw [hm1]
    have hT2 : C.tdim t 2 = d2 := by show mdim C (t.mods.getD 2 0) = d2; rw [hm2]
    have hT3 : C.tdim t 3 = d3 := by show mdim C (t.mods.getD 3 0) = d3; rw [hm3]
    simp only [hT0, hT1, hT2, hT3]
    unfold boxItem
    push_cast
    refine Finset.sum_congr rfl fun i0 hi0 => Finset.sum_congr rfl fun i1 hi1 =>
      Finset.sum_congr rfl fun i2 hi2 => Finset.sum_congr rfl fun i3 hi3 => ?_
    have h0 := Finset.mem_range.1 hi0; have h1 := Finset.mem_range.1 hi1
    have h2 := Finset.mem_range.1 hi2; have h3 := Finset.mem_range.1 hi3
    rw [aval_localRowsF' _ _ _ _ _ h0, aval_localRowsF' _ _ _ _ _ h1, aval_localRowsF' _ _ _ _ _ h2,
      aval_localRowsF' _ _ _ _ _ h3]
    have e0 : (mods.getD m0 default).n = nf 3 d 0 := hn0
    have e1 : (mods.getD m1 default).n = nf 3 d 1 := hn1
    have e2 : (mods.getD m2 default).n = nf 3 d 2 := hn2
    have e3 : (mods.getD m3 default).n = nf 3 d 3 := hn3
    have j0 : (mods.getD m0 default).J = J 0 := by show _ = (mods.getD (t.mods.getD 0 0) default).J; rw [hm0]
    have j1 : (mods.getD m1 default).J = J 1 := by show _ = (mods.getD (t.mods.getD 1 0) default).J; rw [hm1]
    have j2 : (mods.getD m2 default).J = J 2 := by show _ = (mods.getD (t.mods.getD 2 0) default).J; rw [hm2]
    have j3 : (mods.getD m3 default).J = J 3 := by show _ = (mods.getD (t.mods.getD 3 0) default).J; rw [hm3]
    have t0 : (mods.getD m0 default).dim = T 0 := hT0.symm
    have t1 : (mods.getD m1 default).dim = T 1 := hT1.symm
    have t2 : (mods.getD m2 default).dim = T 2 := hT2.symm
    have t3 : (mods.getD m3 default).dim = T 3 := hT3.symm
    rw [e0, e1, e2, e3, j0, j1, j2, j3, t0, t1, t2, t3]
    rw [itemE_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 hz hL]
    have hnn : (∏ l : Fin (3 + 1), C.tdim t l) = d0 * d1 * d2 * d3 := by
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_one]
      show C.tdim t 0 * (C.tdim t 1 * (C.tdim t 2 * C.tdim t 3)) = _
      rw [hT0, hT1, hT2, hT3]; ring
    have u0 : (mods.getD m0 default).dim = d0 := rfl
    have u1 : (mods.getD m1 default).dim = d1 := rfl
    have u2 : (mods.getD m2 default).dim = d2 := rfl
    have u3 : (mods.getD m3 default).dim = d3 := rfl
    have hBq : ∀ μ ν : ℕ, C.Bq t r s μ ν = ∑ a ∈ range (Z.getD t.zi default).n, ∑ c ∈ range (Z.getD t.zi default).n,
        ((t.W.getD (r * (d0 * d1 * d2 * d3) + μ) []).getD a 0 : ℚ) * CertD.zq (Z.getD t.zi default) Lden a c *
          ((t.W.getD (s * (d0 * d1 * d2 * d3) + ν) []).getD c 0 : ℚ) := by
      intro μ ν
      show (∑ a ∈ range (Z.getD t.zi default).n, ∑ c ∈ range (Z.getD t.zi default).n,
        ((t.W.getD (r * (∏ l, C.tdim t l) + μ) []).getD a 0 : ℚ) * CertD.zq (Z.getD t.zi default) Lden a c *
          ((t.W.getD (s * (∏ l, C.tdim t l) + ν) []).getD c 0 : ℚ)) = _
      rw [hnn]
    simp only [F, T, hT0, hT1, hT2, hT3, u0, u1, u2, u3, hBq]
    rw [ht]
    ring
  · intro i
    simp only [F, flatMI_four]
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_one]
    haveI := hnz 0; haveI := hnz 1; haveI := hnz 2; haveI := hnz 3
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    rw [Kmat_eq_kmatF, Kmat_eq_kmatF, Kmat_eq_kmatF, Kmat_eq_kmatF]
    simp only [(finProd_symm_val _ _ _).1, (finProd_symm_val _ _ _).2]
    rfl

end NPT.Cert.Ident
