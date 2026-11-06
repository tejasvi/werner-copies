/-
NPT.K4.Route.Item5 — entries of the leg-4-contracted item tensors, and the bridge to `Sem.CertD.blk` at k = 4:
the box form of one item on the aux slice `w 4` is `coef · 2^E · blk t r s w`.
-/
import NPT.K4.Route.Slice

namespace NPT.K4.Route

open BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident

/-! ### Five-leg index helpers -/

lemma flatMI_five (d : Fin (4 + 1) → ℕ) (μ : (l : Fin (4 + 1)) → Fin (d l)) :
    flatMI d μ = mr4 (d 0) (d 1) (d 2) (d 3) (μ 0) (μ 1) (μ 2) (μ 3) * d 4 + μ 4 := by
  simp [flatMI, mr4, Fin.sum_univ_five, Fin.prod_univ_five]
  ring

/-- Per-leg pairing `(μ_l, ν_l) ↦ μ_l·d_l + ν_l` over five legs. -/
def pairEquiv5 (d : Fin 5 → ℕ) :
    (((l : Fin 5) → Fin (d l)) × ((l : Fin 5) → Fin (d l))) ≃ ((l : Fin 5) → Fin (d l * d l)) where
  toFun p := fun l => finProdFinEquiv (p.1 l, p.2 l)
  invFun i := (fun l => (finProdFinEquiv.symm (i l)).1, fun l => (finProdFinEquiv.symm (i l)).2)
  left_inv p := by
    rcases p with ⟨μ, ν⟩
    simp only [Equiv.symm_apply_apply]
  right_inv i := by
    funext l
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]

lemma sum_pi_pair5 {R : Type*} [AddCommMonoid R] (d : Fin 5 → ℕ)
    (F : ((l : Fin 5) → Fin (d l)) → ((l : Fin 5) → Fin (d l)) → R) :
    ∑ μ, ∑ ν, F μ ν = ∑ i : ((l : Fin 5) → Fin (d l * d l)),
      F (fun l => (finProdFinEquiv.symm (i l)).1) (fun l => (finProdFinEquiv.symm (i l)).2) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (pairEquiv5 d) _ _ fun p => by
    simp only [pairEquiv5, Equiv.coe_fn_mk, Equiv.symm_apply_apply]

/-- Sums over dependent 5-tuples as five nested sums. -/
lemma sum_pi_five {R : Type*} [AddCommMonoid R] (d : Fin 5 → ℕ) (F : ((l : Fin 5) → Fin (d l)) → R) :
    ∑ x, F x = ∑ a : Fin (d 0), ∑ b : Fin (d 1), ∑ c : Fin (d 2), ∑ e : Fin (d 3), ∑ g : Fin (d 4),
      F (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons e (Fin.cons g (fun i => i.elim0)))))) := by
  rw [NPT.Cert.Ident.sum_cons]; refine Finset.sum_congr rfl fun a _ => ?_
  rw [NPT.Cert.Ident.sum_cons]; refine Finset.sum_congr rfl fun b _ => ?_
  rw [NPT.Cert.Ident.sum_cons]; refine Finset.sum_congr rfl fun c _ => ?_
  rw [NPT.Cert.Ident.sum_cons]; refine Finset.sum_congr rfl fun e _ => ?_
  rw [NPT.Cert.Ident.sum_cons]; refine Finset.sum_congr rfl fun g _ => ?_
  rw [NPT.Cert.Ident.sum_fin_zero]

/-- Sums over `(l : Fin (4+1)) → Fin (n l)` as five nested range sums of a function of the values. -/
lemma sum_pi_range5 {R : Type*} [AddCommMonoid R] (n : Fin (4 + 1) → ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → R)
    (G : ((l : Fin (4 + 1)) → Fin (n l)) → R)
    (hG : ∀ i, G i = F (i 0) (i 1) (i 2) (i 3) (i 4)) :
    ∑ i, G i = ∑ a ∈ range (n 0), ∑ b ∈ range (n 1), ∑ c ∈ range (n 2), ∑ e ∈ range (n 3),
      ∑ g ∈ range (n 4), F a b c e g := by
  rw [sum_pi_five n G]
  simp only [hG, Fin.cons_zero, Fin.cons_succ]
  rw [← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range (n 1), ∑ c ∈ range (n 2), ∑ e ∈ range (n 3),
    ∑ g ∈ range (n 4), F a b c e g)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun b => ∑ c ∈ range (n 2), ∑ e ∈ range (n 3), ∑ g ∈ range (n 4), F a b c e g)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun c => ∑ e ∈ range (n 3), ∑ g ∈ range (n 4), F a b c e g)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun e => ∑ g ∈ range (n 4), F a b c e g)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun g => F a b c e g)]
  rfl

/-! ### Entries of the contracted item tensor -/

/-- The item's `W_r` rows. -/
def itemWr (C : CertD) (nn : ℕ) (it : ℕ × ℕ × ℕ) : List (List Int) :=
  (List.range nn).map fun x => (C.types.getD it.1 default).W.getD (it.2.1 * nn + x) []

/-- One entry of the leg-4-contracted item tensor, from the `W_r` rows and `Yw`. -/
def itemE5c (coef : Int) (d0 d1 d2 d3 d4 : ℕ) (Wr : List (List Int)) (Yw : List (List (List Int)))
    (i0 i1 i2 i3 : ℕ) : Int :=
  coef * ∑ μ4 ∈ range d4, dotI (Wr.getD (mr4 d0 d1 d2 d3 (i0 / d0) (i1 / d1) (i2 / d2) (i3 / d3) * d4 + μ4) [])
    ((Yw.getD μ4 []).getD (mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3)) [])

lemma itemTF5c_eq (C : CertD) (coef : Int) (d0 d1 d2 d3 d4 : ℕ) (A4 : List Int) (it : ℕ × ℕ × ℕ) :
    itemTF5c C coef d0 d1 d2 d3 d4 A4 it =
      (List.range (d0 * d0)).flatMap fun i0 => (List.range (d1 * d1)).flatMap fun i1 =>
        (List.range (d2 * d2)).flatMap fun i2 => (List.range (d3 * d3)).map fun i3 =>
          SInt.ofInt (itemE5c coef d0 d1 d2 d3 d4 (itemWr C (d0 * d1 * d2 * d3 * d4) it)
            (itemYw d4 (d0 * d1 * d2 * d3) (C.Z.getD (C.types.getD it.1 default).zi default).n A4
              (itemY5 C (d0 * d1 * d2 * d3 * d4) it)) i0 i1 i2 i3) := rfl

lemma itemTF5c_gv (C : CertD) (coef : Int) (d0 d1 d2 d3 d4 : ℕ) (A4 : List Int) (it : ℕ × ℕ × ℕ)
    (i0 i1 i2 i3 : ℕ) (h0 : i0 < d0 * d0) (h1 : i1 < d1 * d1) (h2 : i2 < d2 * d2) (h3 : i3 < d3 * d3) :
    gv (itemTF5c C coef d0 d1 d2 d3 d4 A4 it)
      (i0 * (d1 * d1 * (d2 * d2) * (d3 * d3)) + (i1 * (d2 * d2 * (d3 * d3)) + (i2 * (d3 * d3) + i3))) =
      itemE5c coef d0 d1 d2 d3 d4 (itemWr C (d0 * d1 * d2 * d3 * d4) it)
        (itemYw d4 (d0 * d1 * d2 * d3) (C.Z.getD (C.types.getD it.1 default).zi default).n A4
          (itemY5 C (d0 * d1 * d2 * d3 * d4) it)) i0 i1 i2 i3 := by
  rw [itemTF5c_eq]
  unfold gv
  set E := itemE5c coef d0 d1 d2 d3 d4 (itemWr C (d0 * d1 * d2 * d3 * d4) it)
    (itemYw d4 (d0 * d1 * d2 * d3) (C.Z.getD (C.types.getD it.1 default).zi default).n A4
      (itemY5 C (d0 * d1 * d2 * d3 * d4) it)) with hE
  have L3 : ∀ (i0 i1 i2 : ℕ), ((List.range (d3 * d3)).map fun i3 => SInt.ofInt (E i0 i1 i2 i3)).length = d3 * d3 := by
    intros; simp
  have L2 : ∀ (i0 i1 : ℕ), ((List.range (d2 * d2)).flatMap fun i2 => (List.range (d3 * d3)).map fun i3 =>
      SInt.ofInt (E i0 i1 i2 i3)).length = d2 * d2 * (d3 * d3) := by
    intros; rw [List.length_flatMap]; simp only [L3, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  have L1 : ∀ (i0 : ℕ), ((List.range (d1 * d1)).flatMap fun i1 => (List.range (d2 * d2)).flatMap fun i2 =>
      (List.range (d3 * d3)).map fun i3 => SInt.ofInt (E i0 i1 i2 i3)).length = d1 * d1 * (d2 * d2 * (d3 * d3)) := by
    intros; rw [List.length_flatMap]; simp only [L2, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  rw [show i0 * (d1 * d1 * (d2 * d2) * (d3 * d3)) = i0 * (d1 * d1 * (d2 * d2 * (d3 * d3))) by ring]
  have hB2 : i2 * (d3 * d3) + i3 < d2 * d2 * (d3 * d3) := idx_lt _ _ _ _ h2 h3
  have hB1 : i1 * (d2 * d2 * (d3 * d3)) + (i2 * (d3 * d3) + i3) < d1 * d1 * (d2 * d2 * (d3 * d3)) :=
    idx_lt _ _ _ _ h1 hB2
  rw [flatMap_getD _ (d1 * d1 * (d2 * d2 * (d3 * d3))) L1 _ _ 0 i0 _ (by simpa using h0) hB1]
  rw [range_getD _ _ h0]
  rw [flatMap_getD _ (d2 * d2 * (d3 * d3)) (L2 i0) _ _ 0 i1 _ (by simpa using h1) hB2]
  rw [range_getD _ _ h1]
  rw [flatMap_getD _ (d3 * d3) (L3 i0 i1) _ _ 0 i2 _ (by simpa using h2) h3]
  rw [range_getD _ _ h2]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h3]
  simp [SInt.val_ofInt]

/-! ### Expansion of an entry -/

/-- `dotI` as a sum over a range covering the second list. -/
lemma dotI_eq_sum : ∀ (x y : List Int) (n : ℕ), y.length ≤ n →
    dotI x y = ∑ a ∈ range n, x.getD a 0 * y.getD a 0
  | [], y, n, _ => by simp [dotI]
  | x :: xs, [], n, _ => by simp [dotI]
  | x :: xs, y :: ys, n, h => by
    cases n with
    | zero => simp at h
    | succ n =>
      rw [dotI, dotI_eq_sum xs ys n (by simpa using h), Finset.sum_range_succ']
      simp [add_comm]

/-- An entry of the contracted item tensor as an explicit sum over `μ4, ν4, a, c`. -/
lemma itemE5c_expand (C : CertD) (coef : Int) (d0 d1 d2 d3 d4 : ℕ) (A4 : List Int) (ti r s : ℕ)
    (i0 i1 i2 i3 : ℕ) (h0 : i0 < d0 * d0) (h1 : i1 < d1 * d1) (h2 : i2 < d2 * d2) (h3 : i3 < d3 * d3) :
    itemE5c coef d0 d1 d2 d3 d4 (itemWr C (d0 * d1 * d2 * d3 * d4) (ti, r, s))
        (itemYw d4 (d0 * d1 * d2 * d3) (C.Z.getD (C.types.getD ti default).zi default).n A4
          (itemY5 C (d0 * d1 * d2 * d3 * d4) (ti, r, s))) i0 i1 i2 i3 =
      coef * ∑ μ4 ∈ range d4, ∑ ν4 ∈ range d4,
        ∑ a ∈ range (C.Z.getD (C.types.getD ti default).zi default).n,
        ∑ c ∈ range (C.Z.getD (C.types.getD ti default).zi default).n,
          ((C.types.getD ti default).W.getD (r * (d0 * d1 * d2 * d3 * d4) +
              (mr4 d0 d1 d2 d3 (i0 / d0) (i1 / d1) (i2 / d2) (i3 / d3) * d4 + μ4)) []).getD a 0 *
            (A4.getD (μ4 * d4 + ν4) 0 * ((C.Z.getD (C.types.getD ti default).zi default).zget a c *
              ((C.types.getD ti default).W.getD (s * (d0 * d1 * d2 * d3 * d4) +
                (mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3) * d4 + ν4)) []).getD c 0)) := by
  set t := C.types.getD ti default with ht
  set b := C.Z.getD t.zi default with hb
  set R := b.n
  set n' := d0 * d1 * d2 * d3
  set nn := d0 * d1 * d2 * d3 * d4
  set μ' := mr4 d0 d1 d2 d3 (i0 / d0) (i1 / d1) (i2 / d2) (i3 / d3)
  set ν' := mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3)
  have hpos : ∀ x y : ℕ, x < y * y → 0 < y := fun x y h => by
    rcases Nat.eq_zero_or_pos y with hy | hy
    · rw [hy] at h; simp at h
    · exact hy
  have hμ' : μ' < n' := mr4_lt _ _ _ _ _ _ _ _ (Nat.div_lt_of_lt_mul h0) (Nat.div_lt_of_lt_mul h1)
    (Nat.div_lt_of_lt_mul h2) (Nat.div_lt_of_lt_mul h3)
  have hν' : ν' < n' := mr4_lt _ _ _ _ _ _ _ _ (Nat.mod_lt _ (hpos _ _ h0)) (Nat.mod_lt _ (hpos _ _ h1))
    (Nat.mod_lt _ (hpos _ _ h2)) (Nat.mod_lt _ (hpos _ _ h3))
  have hnn : nn = n' * d4 := rfl
  unfold itemE5c
  congr 1
  refine Finset.sum_congr rfl fun μ4 hμ4 => ?_
  have hμ4' := Finset.mem_range.1 hμ4
  -- the W_r row
  have hWr : (itemWr C nn (ti, r, s)).getD (μ' * d4 + μ4) [] = t.W.getD (r * nn + (μ' * d4 + μ4)) [] := by
    unfold itemWr
    rw [getD_range_map _ _ _ _ (by rw [hnn]; exact idx_lt _ _ _ _ hμ' hμ4')]
  -- the Yw row
  have hYw : ((itemYw d4 n' R A4 (itemY5 C nn (ti, r, s))).getD μ4 []).getD ν' [] =
      (List.range R).map fun a => ∑ ν4 ∈ range d4, A4.getD (μ4 * d4 + ν4) 0 *
        ((itemY5 C nn (ti, r, s)).getD (ν' * d4 + ν4) []).getD a 0 := by
    unfold itemYw
    rw [getD_range_map _ _ _ _ hμ4', getD_range_map _ _ _ _ hν']
  -- the Y entries
  have hY : ∀ ν4 < d4, ∀ a < R, ((itemY5 C nn (ti, r, s)).getD (ν' * d4 + ν4) []).getD a 0 =
      ∑ c ∈ range R, b.zget a c * (t.W.getD (s * nn + (ν' * d4 + ν4)) []).getD c 0 := by
    intro ν4 hν4' a ha'
    unfold itemY5
    simp only
    rw [getD_range_map _ _ _ _ (by rw [hnn]; exact idx_lt _ _ _ _ hν' hν4'), getD_range_map _ _ _ _ ha']
  rw [hWr, hYw, dotI_eq_sum _ _ R (by simp)]
  have step1 : ∀ a ∈ range R, (t.W.getD (r * nn + (μ' * d4 + μ4)) []).getD a 0 *
      ((List.range R).map fun a => ∑ ν4 ∈ range d4, A4.getD (μ4 * d4 + ν4) 0 *
        ((itemY5 C nn (ti, r, s)).getD (ν' * d4 + ν4) []).getD a 0).getD a 0 =
      ∑ ν4 ∈ range d4, ∑ c ∈ range R, (t.W.getD (r * nn + (μ' * d4 + μ4)) []).getD a 0 *
        (A4.getD (μ4 * d4 + ν4) 0 * (b.zget a c * (t.W.getD (s * nn + (ν' * d4 + ν4)) []).getD c 0)) := by
    intro a ha
    have ha' := Finset.mem_range.1 ha
    rw [getD_range_map _ _ _ _ ha', Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν4 hν4 => ?_
    rw [hY ν4 (Finset.mem_range.1 hν4) a ha', Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]

/-! ### The bridge to `Sem.CertD.blk` -/

lemma getD_map_val : ∀ (l : List SInt) (i : ℕ), (l.map SInt.val).getD i 0 = (l.getD i SInt.zero).val
  | [], i => by simp
  | x :: l, 0 => by simp
  | x :: l, i + 1 => by rw [List.map_cons, List.getD_cons_succ, List.getD_cons_succ]; exact getD_map_val l i

lemma zq_of_uent_nil (b : PBlock) (Lden : ℕ) (h : b.uent = []) (a c : ℕ) :
    CertD.zq b Lden a c = (b.zget a c : ℚ) / 2 ^ b.E := by
  simp [CertD.zq, PBlock.uval, PBlock.ufind, h]

/-- The box form of one item on the aux slice `w4`, at word `(w0, w1, w2, w3)`. -/
def boxItem5 (C : CertD) (coef : Int) (kpos lpos : List ℕ) (m0 m1 m2 m3 m4 : ℕ) (it : ℕ × ℕ × ℕ)
    (w0 w1 w2 w3 w4 : Fin 24) : Int :=
  ∑ i0 ∈ range (mdim C m0 * mdim C m0), ∑ i1 ∈ range (mdim C m1 * mdim C m1),
  ∑ i2 ∈ range (mdim C m2 * mdim C m2), ∑ i3 ∈ range (mdim C m3 * mdim C m3),
    aval (localRowsF (C.mods.getD m0 default) kpos lpos) w0.val i0 *
    aval (localRowsF (C.mods.getD m1 default) kpos lpos) w1.val i1 *
    aval (localRowsF (C.mods.getD m2 default) kpos lpos) w2.val i2 *
    aval (localRowsF (C.mods.getD m3 default) kpos lpos) w3.val i3 *
    itemE5c coef (mdim C m0) (mdim C m1) (mdim C m2) (mdim C m3) (mdim C m4)
      (itemWr C (mdim C m0 * mdim C m1 * mdim C m2 * mdim C m3 * mdim C m4) it)
      (itemYw (mdim C m4) (mdim C m0 * mdim C m1 * mdim C m2 * mdim C m3)
        (C.Z.getD (C.types.getD it.1 default).zi default).n
        (((localRowsF (C.mods.getD m4 default) kpos lpos).getD w4.val []).map SInt.val)
        (itemY5 C (mdim C m0 * mdim C m1 * mdim C m2 * mdim C m3 * mdim C m4) it)) i0 i1 i2 i3

/-- One summand of the bridge: the four leg rows times the contracted entry is the sum over the leg-4 pair index `g`
of `coef · 2^E · Bq · Π_l kmatF`. -/
lemma entry_bridge (C : CertD) (coef : ℤ) (ti r s m0 m1 m2 m3 m4 : ℕ) (kpos lpos : List ℕ)
    (w0 w1 w2 w3 w4 : Fin 24) (hu : (C.Z.getD (C.types.getD ti default).zi default).uent = [])
    (hnn : (∏ l : Fin (C.k + 1), C.tdim (C.types.getD ti default) l) =
      mdim C m0 * mdim C m1 * mdim C m2 * mdim C m3 * mdim C m4)
    (i0 i1 i2 i3 : ℕ) (h0 : i0 < mdim C m0 * mdim C m0) (h1 : i1 < mdim C m1 * mdim C m1)
    (h2 : i2 < mdim C m2 * mdim C m2) (h3 : i3 < mdim C m3 * mdim C m3) :
    (kmatF (C.mods.getD m0 default).n (C.mods.getD m0 default).J kpos lpos w0 (i0 / mdim C m0) (i0 % mdim C m0) : ℚ) *
      (kmatF (C.mods.getD m1 default).n (C.mods.getD m1 default).J kpos lpos w1 (i1 / mdim C m1) (i1 % mdim C m1) : ℚ) *
      (kmatF (C.mods.getD m2 default).n (C.mods.getD m2 default).J kpos lpos w2 (i2 / mdim C m2) (i2 % mdim C m2) : ℚ) *
      (kmatF (C.mods.getD m3 default).n (C.mods.getD m3 default).J kpos lpos w3 (i3 / mdim C m3) (i3 % mdim C m3) : ℚ) *
      (itemE5c coef (mdim C m0) (mdim C m1) (mdim C m2) (mdim C m3) (mdim C m4)
        (itemWr C (mdim C m0 * mdim C m1 * mdim C m2 * mdim C m3 * mdim C m4) (ti, r, s))
        (itemYw (mdim C m4) (mdim C m0 * mdim C m1 * mdim C m2 * mdim C m3)
          (C.Z.getD (C.types.getD ti default).zi default).n
          (((localRowsF (C.mods.getD m4 default) kpos lpos).getD w4.val []).map SInt.val)
          (itemY5 C (mdim C m0 * mdim C m1 * mdim C m2 * mdim C m3 * mdim C m4) (ti, r, s))) i0 i1 i2 i3 : ℚ) =
    ∑ g ∈ range (mdim C m4 * mdim C m4),
      (coef : ℚ) * 2 ^ (C.Z.getD (C.types.getD ti default).zi default).E *
        (C.Bq (C.types.getD ti default) r s
          (mr4 (mdim C m0) (mdim C m1) (mdim C m2) (mdim C m3) (i0 / mdim C m0) (i1 / mdim C m1) (i2 / mdim C m2)
            (i3 / mdim C m3) * mdim C m4 + g / mdim C m4)
          (mr4 (mdim C m0) (mdim C m1) (mdim C m2) (mdim C m3) (i0 % mdim C m0) (i1 % mdim C m1) (i2 % mdim C m2)
            (i3 % mdim C m3) * mdim C m4 + g % mdim C m4) *
        ((kmatF (C.mods.getD m0 default).n (C.mods.getD m0 default).J kpos lpos w0 (i0 / mdim C m0) (i0 % mdim C m0) : ℚ) *
         (kmatF (C.mods.getD m1 default).n (C.mods.getD m1 default).J kpos lpos w1 (i1 / mdim C m1) (i1 % mdim C m1) : ℚ) *
         (kmatF (C.mods.getD m2 default).n (C.mods.getD m2 default).J kpos lpos w2 (i2 / mdim C m2) (i2 % mdim C m2) : ℚ) *
         (kmatF (C.mods.getD m3 default).n (C.mods.getD m3 default).J kpos lpos w3 (i3 / mdim C m3) (i3 % mdim C m3) : ℚ) *
         (kmatF (C.mods.getD m4 default).n (C.mods.getD m4 default).J kpos lpos w4 (g / mdim C m4) (g % mdim C m4) : ℚ))) := by
  set t := C.types.getD ti default with ht
  set b := C.Z.getD t.zi default with hb
  set d0 := mdim C m0; set d1 := mdim C m1; set d2 := mdim C m2; set d3 := mdim C m3; set d4 := mdim C m4
  set K0 := (kmatF (C.mods.getD m0 default).n (C.mods.getD m0 default).J kpos lpos w0 (i0 / d0) (i0 % d0) : ℚ)
  set K1 := (kmatF (C.mods.getD m1 default).n (C.mods.getD m1 default).J kpos lpos w1 (i1 / d1) (i1 % d1) : ℚ)
  set K2 := (kmatF (C.mods.getD m2 default).n (C.mods.getD m2 default).J kpos lpos w2 (i2 / d2) (i2 % d2) : ℚ)
  set K3 := (kmatF (C.mods.getD m3 default).n (C.mods.getD m3 default).J kpos lpos w3 (i3 / d3) (i3 % d3) : ℚ)
  set μ' := mr4 d0 d1 d2 d3 (i0 / d0) (i1 / d1) (i2 / d2) (i3 / d3)
  set ν' := mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3)
  set nn := d0 * d1 * d2 * d3 * d4
  rw [itemE5c_expand C coef d0 d1 d2 d3 d4 _ ti r s i0 i1 i2 i3 h0 h1 h2 h3]
  -- the leg-4 row entries
  have hA4 : ∀ μ4 < d4, ∀ ν4 < d4,
      ((((localRowsF (C.mods.getD m4 default) kpos lpos).getD w4.val []).map SInt.val).getD (μ4 * d4 + ν4) 0 : ℚ) =
        (kmatF (C.mods.getD m4 default).n (C.mods.getD m4 default).J kpos lpos w4 μ4 ν4 : ℚ) := by
    intro μ4 hμ4 ν4 hν4
    have := aval_localRowsF (C.mods.getD m4 default) kpos lpos w4 μ4 ν4 hμ4 hν4
    unfold aval at this
    rw [getD_map_val]
    exact_mod_cast this
  -- Bq on the slice indices
  have hBq : ∀ μ ν, C.Bq t r s μ ν = ∑ a ∈ range b.n, ∑ c ∈ range b.n,
      ((t.W.getD (r * nn + μ) []).getD a 0 : ℚ) * ((b.zget a c : ℚ) / 2 ^ b.E) *
        ((t.W.getD (s * nn + ν) []).getD c 0 : ℚ) := by
    intro μ ν
    unfold CertD.Bq
    simp only
    rw [hnn]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [zq_of_uent_nil _ _ hu]
  push_cast
  simp only [Finset.mul_sum]
  rw [NPT.Cert.Ident.sum_pair]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' := Finset.mem_range.1 hg
  have hd4 : 0 < d4 := by
    rcases Nat.eq_zero_or_pos d4 with h | h
    · rw [h] at hg'; simp at hg'
    · exact h
  have hq : g / d4 < d4 := Nat.div_lt_of_lt_mul hg'
  have hr : g % d4 < d4 := Nat.mod_lt _ hd4
  rw [hBq]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [hA4 _ hq _ hr]
  have h2E : (2 : ℚ) ^ b.E ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
  ring

/-- **Item bridge (k = 4).** The box form of one item on the aux slice `w 4` is `coef · 2^E · blk t r s w`. -/
theorem item5_bridge (C : CertD) (hk : C.k = 4) (coef : ℤ) (ti r s m0 m1 m2 m3 m4 : ℕ) (kpos lpos : List ℕ)
    (hmods : (C.types.getD ti default).mods = [m0, m1, m2, m3, m4])
    (hkp : (((C.types.getD ti default).rules.getD r []).getD s default).kpos = kpos)
    (hlp : (((C.types.getD ti default).rules.getD r []).getD s default).lpos = lpos)
    (hn0 : (C.mods.getD m0 default).n = C.d) (hn1 : (C.mods.getD m1 default).n = C.d)
    (hn2 : (C.mods.getD m2 default).n = C.d) (hn3 : (C.mods.getD m3 default).n = C.d)
    (hn4 : (C.mods.getD m4 default).n = 2) (hd : 0 < C.d)
    (hu : (C.Z.getD (C.types.getD ti default).zi default).uent = [])
    (w : Fin (C.k + 1) → Fin 24) :
    ((boxItem5 C coef kpos lpos m0 m1 m2 m3 m4 (ti, r, s) (w 0) (w 1) (w 2) (w 3) (w 4) : ℤ) : ℚ) =
      coef * 2 ^ (C.Z.getD (C.types.getD ti default).zi default).E * C.blk (C.types.getD ti default) r s w := by
  obtain ⟨k, d, types, mods, eqs, Z, Lden, lamDen⟩ := C
  simp only at hk
  subst hk
  set t := types.getD ti default with ht
  let C : CertD := ⟨4, d, types, mods, eqs, Z, Lden, lamDen⟩
  set b := Z.getD t.zi default with hb
  have hm0 : t.mods.getD 0 0 = m0 := by rw [hmods]; rfl
  have hm1 : t.mods.getD 1 0 = m1 := by rw [hmods]; rfl
  have hm2 : t.mods.getD 2 0 = m2 := by rw [hmods]; rfl
  have hm3 : t.mods.getD 3 0 = m3 := by rw [hmods]; rfl
  have hm4 : t.mods.getD 4 0 = m4 := by rw [hmods]; rfl
  unfold CertD.blk
  simp only [hkp, hlp]
  rw [sum_pi_pair5, Finset.mul_sum]
  set d0 := mdim C m0; set d1 := mdim C m1; set d2 := mdim C m2; set d3 := mdim C m3; set d4 := mdim C m4
  have hd' : 0 < d := hd
  have hnz : ∀ l : Fin (4 + 1), NeZero (nf 4 d l) := by
    intro l; constructor; unfold nf; split_ifs <;> omega
  let T := fun l : Fin (4 + 1) => C.tdim t l
  let J := fun l : Fin (4 + 1) => (C.mods.getD (t.mods.getD l.val 0) default).J
  let F : ℕ → ℕ → ℕ → ℕ → ℕ → ℚ := fun a b' c e g =>
    (coef : ℚ) * 2 ^ b.E * (C.Bq t r s
      (mr4 (T 0) (T 1) (T 2) (T 3) (a / T 0) (b' / T 1) (c / T 2) (e / T 3) * T 4 + g / T 4)
      (mr4 (T 0) (T 1) (T 2) (T 3) (a % T 0) (b' % T 1) (c % T 2) (e % T 3) * T 4 + g % T 4) *
      ((kmatF (nf 4 d 0) (J 0) kpos lpos (w 0) (a / T 0) (a % T 0) : ℚ) *
       (kmatF (nf 4 d 1) (J 1) kpos lpos (w 1) (b' / T 1) (b' % T 1) : ℚ) *
       (kmatF (nf 4 d 2) (J 2) kpos lpos (w 2) (c / T 2) (c % T 2) : ℚ) *
       (kmatF (nf 4 d 3) (J 3) kpos lpos (w 3) (e / T 3) (e % T 3) : ℚ) *
       (kmatF (nf 4 d 4) (J 4) kpos lpos (w 4) (g / T 4) (g % T 4) : ℚ)))
  rw [sum_pi_range5 (fun l => C.tdim t l * C.tdim t l) F]
  · have hT0 : C.tdim t 0 = d0 := by show mdim C (t.mods.getD 0 0) = d0; rw [hm0]
    have hT1 : C.tdim t 1 = d1 := by show mdim C (t.mods.getD 1 0) = d1; rw [hm1]
    have hT2 : C.tdim t 2 = d2 := by show mdim C (t.mods.getD 2 0) = d2; rw [hm2]
    have hT3 : C.tdim t 3 = d3 := by show mdim C (t.mods.getD 3 0) = d3; rw [hm3]
    have hT4 : C.tdim t 4 = d4 := by show mdim C (t.mods.getD 4 0) = d4; rw [hm4]
    simp only [hT0, hT1, hT2, hT3, hT4]
    unfold boxItem5
    push_cast
    refine Finset.sum_congr rfl fun i0 hi0 => Finset.sum_congr rfl fun i1 hi1 =>
      Finset.sum_congr rfl fun i2 hi2 => Finset.sum_congr rfl fun i3 hi3 => ?_
    have h0 := Finset.mem_range.1 hi0; have h1 := Finset.mem_range.1 hi1
    have h2 := Finset.mem_range.1 hi2; have h3 := Finset.mem_range.1 hi3
    rw [aval_localRowsF' _ _ _ _ _ h0, aval_localRowsF' _ _ _ _ _ h1, aval_localRowsF' _ _ _ _ _ h2,
      aval_localRowsF' _ _ _ _ _ h3]
    have e0 : nf 4 d 0 = (C.mods.getD m0 default).n := hn0.symm
    have e1 : nf 4 d 1 = (C.mods.getD m1 default).n := hn1.symm
    have e2 : nf 4 d 2 = (C.mods.getD m2 default).n := hn2.symm
    have e3 : nf 4 d 3 = (C.mods.getD m3 default).n := hn3.symm
    have e4 : nf 4 d 4 = (C.mods.getD m4 default).n := hn4.symm
    have j0 : J 0 = (C.mods.getD m0 default).J := by
      show (C.mods.getD (t.mods.getD 0 0) default).J = _; rw [hm0]
    have j1 : J 1 = (C.mods.getD m1 default).J := by
      show (C.mods.getD (t.mods.getD 1 0) default).J = _; rw [hm1]
    have j2 : J 2 = (C.mods.getD m2 default).J := by
      show (C.mods.getD (t.mods.getD 2 0) default).J = _; rw [hm2]
    have j3 : J 3 = (C.mods.getD m3 default).J := by
      show (C.mods.getD (t.mods.getD 3 0) default).J = _; rw [hm3]
    have j4 : J 4 = (C.mods.getD m4 default).J := by
      show (C.mods.getD (t.mods.getD 4 0) default).J = _; rw [hm4]
    have hnn' : (∏ l : Fin (C.k + 1), C.tdim (C.types.getD ti default) l) = d0 * d1 * d2 * d3 * d4 := by
      rw [Fin.prod_univ_five]
      show C.tdim t 0 * C.tdim t 1 * C.tdim t 2 * C.tdim t 3 * C.tdim t 4 = _
      rw [hT0, hT1, hT2, hT3, hT4]
    simp only [F, T, hT0, hT1, hT2, hT3, hT4, e0, e1, e2, e3, e4, j0, j1, j2, j3, j4]
    exact entry_bridge C coef ti r s m0 m1 m2 m3 m4 kpos lpos (w 0) (w 1) (w 2) (w 3) (w 4) hu hnn'
      i0 i1 i2 i3 h0 h1 h2 h3
  · intro i
    simp only [F, flatMI_five]
    rw [Fin.prod_univ_five]
    have := hnz 0; have := hnz 1; have := hnz 2; have := hnz 3; have := hnz 4
    rw [Kmat_eq_kmatF, Kmat_eq_kmatF, Kmat_eq_kmatF, Kmat_eq_kmatF, Kmat_eq_kmatF]
    simp only [(finProd_symm_val _ _ _).1, (finProd_symm_val _ _ _).2]
    rfl

end NPT.K4.Route
