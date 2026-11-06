/-
NPT.Cert.Ident.ModP — the certificate data reduced mod `p`, and the congruence of the word values.
`certMod p zmul C` replaces every block's `Zq` by `zqI mod p` (corrections folded in, `uent = []`, used with
`zmul = 1`) and every equality-multiplier numerator by its residue; `famPartsMod` also reduces the objective
coefficient.  Then `partsF (famParts C zmul f …) ≡ partsF (famPartsMod p zmul C f …) [ZMOD p]` at every word
(`partsF_mod`).
-/
import NPT.Cert.Ident.Perturb
import Mathlib.Algebra.BigOperators.ModEq

open BigOperators Finset NPT.Cert.Sem

namespace NPT.Cert.Ident

/-- `Zq` of a block reduced mod `p`, as an `n × n` table. -/
def redRows (p zmul : ℕ) (b : NPT.Cert.PBlock) : List (List Int) :=
  (List.range b.n).map fun a => (List.range b.n).map fun c => (zqI b zmul a c) % (p : Int)

def redBlock (p zmul : ℕ) (b : NPT.Cert.PBlock) : NPT.Cert.PBlock := { b with zrows := redRows p zmul b, uent := [] }

def modEqs (p : ℕ) (eqs : List EqGroupD) : List EqGroupD :=
  eqs.map fun g => { g with lam := g.lam.map fun ol => (ol.1, ol.2 % (p : Int)) }

/-- The certificate with blocks and equality multipliers reduced mod `p`. -/
def certMod (p zmul : ℕ) (C : CertD) : CertD := { C with Z := C.Z.map (redBlock p zmul), eqs := modEqs p C.eqs }

lemma zqI_red (p zmul : ℕ) (b : NPT.Cert.PBlock) (a c : ℕ) (ha : a < b.n) (hc : c < b.n) :
    zqI (redBlock p zmul b) 1 a c = (zqI b zmul a c) % (p : Int) := by
  have hz : (redBlock p zmul b).zget a c = (zqI b zmul a c) % (p : Int) :=
    getD_range_map2 b.n (fun a c => (zqI b zmul a c) % (p : Int)) a c ha hc
  have hu : (redBlock p zmul b).ufind a c = none := rfl
  have h1 : zqI (redBlock p zmul b) 1 a c = (redBlock p zmul b).zget a c := by unfold zqI; rw [hu]; simp
  rw [h1, hz]

/-- **Item entries are congruent mod `p`.** -/
lemma itemE_mod (C : CertD) (p zmul : ℕ) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) (i0 i1 i2 i3 : ℕ)
    (h0 : i0 < d0 * d0) (h1 : i1 < d1 * d1) (h2 : i2 < d2 * d2) (h3 : i3 < d3 * d3) :
    itemE C zmul coef d0 d1 d2 d3 it (itemY C zmul d0 d1 d2 d3 it) i0 i1 i2 i3 ≡
      itemE (certMod p zmul C) 1 coef d0 d1 d2 d3 it (itemY (certMod p zmul C) 1 d0 d1 d2 d3 it) i0 i1 i2 i3
        [ZMOD p] := by
  have pos : ∀ {i d : ℕ}, i < d * d → 0 < d := fun {i d} h => Nat.pos_of_ne_zero fun hd => by simp [hd] at h
  have hv : mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3) < d0 * d1 * d2 * d3 :=
    mr4_lt _ _ _ _ _ _ _ _ (Nat.mod_lt _ (pos h0)) (Nat.mod_lt _ (pos h1)) (Nat.mod_lt _ (pos h2))
      (Nat.mod_lt _ (pos h3))
  have htM : (certMod p zmul C).types = C.types := rfl
  have hZM : (certMod p zmul C).Z = C.Z.map (redBlock p zmul) := rfl
  set t := C.types.getD it.1 default with ht
  rcases Nat.lt_or_ge t.zi C.Z.length with hz | hz
  · have hbM : (certMod p zmul C).Z.getD ((certMod p zmul C).types.getD it.1 default).zi default =
        redBlock p zmul (C.Z.getD t.zi default) := by rw [htM, hZM, getD_map_block _ _ _ hz]
    set b := C.Z.getD t.zi default with hb
    unfold itemE
    simp only
    rw [htM, hZM, getD_map_block _ _ _ hz]
    rw [← hb]
    have hnM : (redBlock p zmul b).n = b.n := rfl
    rw [hnM]
    set nn := d0 * d1 * d2 * d3 with hnn
    set v := mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3) with hvdef
    have eC : ∀ a ∈ range b.n, ((itemY C zmul d0 d1 d2 d3 it).getD v []).getD a 0 =
        ∑ c ∈ range b.n, zqI b zmul a c * (t.W.getD (it.2.2 * nn + v) []).getD c 0 :=
      fun a ha => itemY_entry C zmul d0 d1 d2 d3 it v a hv (Finset.mem_range.1 ha)
    have eM : ∀ a ∈ range b.n, ((itemY (certMod p zmul C) 1 d0 d1 d2 d3 it).getD v []).getD a 0 =
        ∑ c ∈ range b.n, (zqI b zmul a c) % (p : Int) * (t.W.getD (it.2.2 * nn + v) []).getD c 0 := by
      intro a ha
      have ha' := Finset.mem_range.1 ha
      rw [itemY_entry (certMod p zmul C) 1 d0 d1 d2 d3 it v a hv (by rw [hbM]; exact ha'), hbM, htM, hnM]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [zqI_red p zmul b a c ha' (Finset.mem_range.1 hc)]
    refine Int.ModEq.mul_left _ (Int.ModEq.sum fun a ha => Int.ModEq.mul_left _ ?_)
    rw [eC a ha, eM a ha]
    exact Int.ModEq.sum fun c _ => Int.ModEq.mul_right _ (Int.mod_modEq _ _).symm
  · have hM0 : (certMod p zmul C).Z.getD ((certMod p zmul C).types.getD it.1 default).zi default = default := by
      rw [htM, hZM]; exact (getD_map_block_out C.Z (redBlock p zmul) t.zi hz).1
    have hB0 : C.Z.getD t.zi default = default := (getD_map_block_out C.Z (redBlock p zmul) t.zi hz).2
    unfold itemE
    simp only
    rw [hM0, ← ht, hB0]
    have : (default : NPT.Cert.PBlock).n = 0 := rfl
    simp [this]

/-- **Item tensors are congruent mod `p`, entrywise.** -/
lemma itemTF_mod (C : CertD) (p zmul : ℕ) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) (k : ℕ) :
    gv (itemTF C zmul coef d0 d1 d2 d3 it) k ≡ gv (itemTF (certMod p zmul C) 1 coef d0 d1 d2 d3 it) k [ZMOD p] := by
  rcases Nat.lt_or_ge k (d0 * d0 * (d1 * d1 * (d2 * d2 * (d3 * d3)))) with hk | hk
  · have hM1pos : 0 < d1 * d1 * (d2 * d2 * (d3 * d3)) :=
      Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hk; exact Nat.not_lt_zero _ hk
    have hM2pos : 0 < d2 * d2 * (d3 * d3) :=
      Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hM1pos; exact lt_irrefl _ hM1pos
    have hM3pos : 0 < d3 * d3 :=
      Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hM2pos; exact lt_irrefl _ hM2pos
    obtain ⟨i0, r0, hr0, e0⟩ : ∃ i0 r0, r0 < d1 * d1 * (d2 * d2 * (d3 * d3)) ∧
        k = i0 * (d1 * d1 * (d2 * d2 * (d3 * d3))) + r0 :=
      ⟨k / _, k % _, Nat.mod_lt _ hM1pos, by rw [Nat.mul_comm]; exact (Nat.div_add_mod k _).symm⟩
    obtain ⟨i1, r1, hr1, e1⟩ : ∃ i1 r1, r1 < d2 * d2 * (d3 * d3) ∧ r0 = i1 * (d2 * d2 * (d3 * d3)) + r1 :=
      ⟨r0 / _, r0 % _, Nat.mod_lt _ hM2pos, by rw [Nat.mul_comm]; exact (Nat.div_add_mod r0 _).symm⟩
    obtain ⟨i2, i3, h3, e2⟩ : ∃ i2 i3, i3 < d3 * d3 ∧ r1 = i2 * (d3 * d3) + i3 :=
      ⟨r1 / _, r1 % _, Nat.mod_lt _ hM3pos, by rw [Nat.mul_comm]; exact (Nat.div_add_mod r1 _).symm⟩
    have h0 : i0 < d0 * d0 :=
      Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt (Nat.le_add_right _ r0) (e0 ▸ hk))
    have h1 : i1 < d1 * d1 :=
      Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt (Nat.le_add_right _ r1) (e1 ▸ hr0))
    have h2 : i2 < d2 * d2 :=
      Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt (Nat.le_add_right _ i3) (e2 ▸ hr1))
    have hk' : k = i0 * (d1 * d1 * (d2 * d2) * (d3 * d3)) + (i1 * (d2 * d2 * (d3 * d3)) + (i2 * (d3 * d3) + i3)) := by
      rw [show d1 * d1 * (d2 * d2) * (d3 * d3) = d1 * d1 * (d2 * d2 * (d3 * d3)) by ring, e0, e1, e2]
    rw [hk', itemTF_gv _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3, itemTF_gv _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3]
    exact itemE_mod C p zmul coef d0 d1 d2 d3 it i0 i1 i2 i3 h0 h1 h2 h3
  · rw [gv_eq_zero_of_le _ _ (by rw [itemTF_length]; exact hk), gv_eq_zero_of_le _ _ (by rw [itemTF_length]; exact hk)]

/-! ### Box trees respect congruence of the leaf tensors -/

section Cong

variable (p : ℕ) (S S' : Spec) (hR : S'.rows = S.rows) (hD : S'.dimsq = S.dimsq)
  (hL : ∀ m1 m2 m3 lf k, gv (S.leaf m1 m2 m3 lf) k ≡ gv (S'.leaf m1 m2 m3 lf) k [ZMOD p])
include hR hD hL

lemma sL_mod (m1 m2 m3 : ℕ) (lf : Leaf) (w0 j : ℕ) :
    sL S m1 m2 m3 lf w0 j ≡ sL S' m1 m2 m3 lf w0 j [ZMOD p] := by
  unfold sL
  rw [hR, hD]
  exact Int.ModEq.sum fun i0 _ => Int.ModEq.mul_left _ (hL _ _ _ _ _)

lemma sN1_mod (m2 m3 : ℕ) (nd : Nd1) (w0 w1 j : ℕ) :
    sN1 S m2 m3 nd w0 w1 j ≡ sN1 S' m2 m3 nd w0 w1 j [ZMOD p] := by
  unfold sN1
  rw [hR, hD]
  exact Int.ModEq.sum fun i1 _ => Int.ModEq.mul_left _
    (Int.ModEq.listSum_map fun lf _ => sL_mod p S S' hR hD hL _ _ _ lf _ _)

lemma sN2_mod (m3 : ℕ) (nd : Nd2) (w0 w1 w2 j : ℕ) :
    sN2 S m3 nd w0 w1 w2 j ≡ sN2 S' m3 nd w0 w1 w2 j [ZMOD p] := by
  unfold sN2
  rw [hR, hD]
  exact Int.ModEq.sum fun i2 _ => Int.ModEq.mul_left _
    (Int.ModEq.listSum_map fun n1 _ => sN1_mod p S S' hR hD hL _ _ n1 _ _ _)

lemma sN3_mod (nd : Nd3) (w0 w1 w2 w3 : ℕ) :
    sN3 S nd w0 w1 w2 w3 ≡ sN3 S' nd w0 w1 w2 w3 [ZMOD p] := by
  unfold sN3
  rw [hR, hD]
  exact Int.ModEq.sum fun i3 _ => Int.ModEq.mul_left _
    (Int.ModEq.listSum_map fun n2 _ => sN2_mod p S S' hR hD hL _ n2 _ _ _ _)

lemma specTree_mod (tree : List Nd3) (w0 w1 w2 w3 : ℕ) :
    specTree S tree w0 w1 w2 w3 ≡ specTree S' tree w0 w1 w2 w3 [ZMOD p] := by
  unfold specTree
  exact Int.ModEq.listSum_map fun nd _ => sN3_mod p S S' hR hD hL nd _ _ _ _

end Cong

/-! ### The parts reduced mod `p` -/

/-- The parts of family `f` with the data reduced mod `p` (blocks, equality numerators, objective coefficient). -/
def famPartsMod (p zmul : ℕ) (C : CertD) (f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : List Part :=
  gs.map (fun G => ⟨ruleSpecF (certMod p zmul C) 1 (-(den3 C.d : ℤ)) G.kpos G.lpos, G.tree⟩) ++
    (if f = 0 then [rank1Part (objE zs za) ((2 * C.Lden : ℤ) % (p : ℤ))] else []) ++ eqPartsF (certMod p zmul C) f eqT

lemma rank1_mod (p : ℕ) (E : ℕ → Fin 24 → ℤ) (c c' : ℤ) (h : c ≡ c' [ZMOD p]) (w0 w1 w2 w3 : ℕ) :
    specTree (rank1Spec E c) rank1Tree w0 w1 w2 w3 ≡ specTree (rank1Spec E c') rank1Tree w0 w1 w2 w3 [ZMOD p] := by
  refine specTree_mod p (rank1Spec E c) (rank1Spec E c') rfl rfl ?_ rank1Tree w0 w1 w2 w3
  intro m1 m2 m3 lf k
  cases k with
  | zero => simp [rank1Spec, gv, SInt.val_ofInt]; exact h
  | succ k => simp [rank1Spec, gv, List.getD_eq_getElem?_getD]

lemma ruleSpecF_leaf_mod (C : CertD) (p zmul : ℕ) (coef : Int) (kpos lpos : List ℕ) (m1 m2 m3 : ℕ) (lf : Leaf)
    (k : ℕ) : gv ((ruleSpecF C zmul coef kpos lpos).leaf m1 m2 m3 lf) k ≡
      gv ((ruleSpecF (certMod p zmul C) 1 coef kpos lpos).leaf m1 m2 m3 lf) k [ZMOD p] := by
  simp only [ruleSpecF]
  rw [gv_foldr_map, gv_foldr_map]
  exact Int.ModEq.listSum_map fun it _ => itemTF_mod C p zmul coef _ _ _ _ it k

lemma ruleSpecF_rows_mod (C : CertD) (p zmul : ℕ) (coef : Int) (kpos lpos : List ℕ) :
    (ruleSpecF (certMod p zmul C) 1 coef kpos lpos).rows = (ruleSpecF C zmul coef kpos lpos).rows := rfl

lemma ruleSpecF_dimsq_mod (C : CertD) (p zmul : ℕ) (coef : Int) (kpos lpos : List ℕ) :
    (ruleSpecF (certMod p zmul C) 1 coef kpos lpos).dimsq = (ruleSpecF C zmul coef kpos lpos).dimsq := rfl

lemma partsF_cons' (P : Part) (ps : List Part) (w0 w1 w2 w3 : ℕ) :
    partsF (P :: ps) w0 w1 w2 w3 = specTree P.S P.tree w0 w1 w2 w3 + partsF ps w0 w1 w2 w3 := by
  simp [partsF]

lemma partsF_map (L : List α) (g : α → Part) (w0 w1 w2 w3 : ℕ) :
    partsF (L.map g) w0 w1 w2 w3 = (L.map fun x => specTree (g x).S (g x).tree w0 w1 w2 w3).sum := by
  simp [partsF, List.map_map]; rfl

/-- **Word values of the reduced parts are congruent mod `p`.** -/
theorem partsF_mod (p zmul : ℕ) (C : CertD) (f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (w0 w1 w2 w3 : ℕ) :
    partsF (famParts C zmul f gs zs za eqT) w0 w1 w2 w3 ≡
      partsF (famPartsMod p zmul C f gs zs za eqT) w0 w1 w2 w3 [ZMOD p] := by
  unfold famParts famPartsMod
  rw [partsF_append, partsF_append, partsF_append, partsF_append]
  refine Int.ModEq.add (Int.ModEq.add ?_ ?_) ?_
  · rw [partsF_map, partsF_map]
    exact Int.ModEq.listSum_map fun G _ => specTree_mod p (ruleSpecF C zmul (-(den3 C.d : ℤ)) G.kpos G.lpos)
      (ruleSpecF (certMod p zmul C) 1 (-(den3 C.d : ℤ)) G.kpos G.lpos)
      (ruleSpecF_rows_mod C p zmul _ G.kpos G.lpos) (ruleSpecF_dimsq_mod C p zmul _ G.kpos G.lpos)
      (fun m1 m2 m3 lf k => ruleSpecF_leaf_mod C p zmul _ G.kpos G.lpos m1 m2 m3 lf k) G.tree _ _ _ _
  · split_ifs
    · rw [partsF_cons', partsF_cons']
      exact Int.ModEq.add (rank1_mod p _ _ _ (Int.mod_modEq _ _).symm _ _ _ _) Int.ModEq.rfl
    · exact Int.ModEq.rfl
  · unfold eqPartsF
    have hd : (certMod p zmul C).d = C.d := rfl
    have he : (certMod p zmul C).eqs = modEqs p C.eqs := rfl
    rw [hd, he, partsF_flatMap, modEqs, List.flatMap_map, partsF_flatMap]
    refine Int.ModEq.listSum_map fun g _ => ?_
    simp only
    rw [partsF_flatMap, partsF_flatMap]
    refine Int.ModEq.listSum_map fun P _ => ?_
    split_ifs
    · rw [List.map_map, partsF_map, partsF_map]
      exact Int.ModEq.listSum_map fun ol _ => rank1_mod p _ _ _
        (Int.ModEq.mul_left _ (Int.mod_modEq _ _).symm) _ _ _ _
    · exact Int.ModEq.rfl

end NPT.Cert.Ident
