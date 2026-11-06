/-
NPT.Cert.Ident.Perturb — splitting the rule-group leaf tensors for kernel evaluation.
Lean hashes a natural-number literal by its low 64 bits, and most `Zq` entries are multiples of `2^64`
(`zget` is a multiple of `2^75`), so the kernel's caches degenerate on them.  We evaluate instead with
`pertCert C` (`zget + 1`, i.e. `Zq + zmul·J`) and subtract the all-ones part `onesCert C` (`Zq = J`, with
`zmul = 1` and coefficient `−coef·zmul`): leaf tensors add up entrywise (`itemTF_split`), so the word values of the
parts are unchanged (`specTree_split`).
-/
import NPT.Cert.Ident.ChunkSpec

open BigOperators Finset NPT.Cert.Sem

namespace NPT.Cert.Ident

/-- `zget + 1` on the `n × n` grid. -/
def pertBlock (b : NPT.Cert.PBlock) : NPT.Cert.PBlock :=
  { b with zrows := (List.range b.n).map fun a => (List.range b.n).map fun c => b.zget a c + 1 }

/-- All-ones `zget`, no corrections. -/
def onesBlock (b : NPT.Cert.PBlock) : NPT.Cert.PBlock :=
  { b with zrows := (List.range b.n).map fun _ => (List.range b.n).map fun _ => (1 : Int), uent := [] }

def pertCert (C : CertD) : CertD := { C with Z := C.Z.map pertBlock }
def onesCert (C : CertD) : CertD := { C with Z := C.Z.map onesBlock }

lemma getD_range_map2 (n : ℕ) (g : ℕ → ℕ → Int) (a c : ℕ) (ha : a < n) (hc : c < n) :
    (((List.range n).map fun a => (List.range n).map fun c => g a c).getD a []).getD c 0 = g a c := by
  rw [getD_range_map _ _ _ _ ha, getD_range_map _ _ _ _ hc]

lemma zqI_pert (b : NPT.Cert.PBlock) (zmul a c : ℕ) (ha : a < b.n) (hc : c < b.n) :
    zqI (pertBlock b) zmul a c = zqI b zmul a c + zmul := by
  have hz : (pertBlock b).zget a c = b.zget a c + 1 := getD_range_map2 b.n (fun a c => b.zget a c + 1) a c ha hc
  have hu : (pertBlock b).ufind a c = b.ufind a c := rfl
  unfold zqI; rw [hz, hu]; ring

lemma zqI_ones (b : NPT.Cert.PBlock) (a c : ℕ) (ha : a < b.n) (hc : c < b.n) : zqI (onesBlock b) 1 a c = 1 := by
  have hz : (onesBlock b).zget a c = 1 := getD_range_map2 b.n (fun _ _ => (1 : Int)) a c ha hc
  have hu : (onesBlock b).ufind a c = none := rfl
  unfold zqI; rw [hz, hu]; simp

lemma getD_map_block (L : List NPT.Cert.PBlock) (g : NPT.Cert.PBlock → NPT.Cert.PBlock) (i : ℕ) (h : i < L.length) :
    (L.map g).getD i default = g (L.getD i default) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]; rfl

lemma getD_map_block_out (L : List NPT.Cert.PBlock) (g : NPT.Cert.PBlock → NPT.Cert.PBlock) (i : ℕ)
    (h : L.length ≤ i) : (L.map g).getD i default = default ∧ L.getD i default = default := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h),
    List.getElem?_eq_none h]
  exact ⟨rfl, rfl⟩

/-- Entry `(v, a)` of `itemY`. -/
lemma itemY_entry (C : CertD) (zmul : ℕ) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) (v a : ℕ)
    (hv : v < d0 * d1 * d2 * d3) (ha : a < (C.Z.getD (C.types.getD it.1 default).zi default).n) :
    ((itemY C zmul d0 d1 d2 d3 it).getD v []).getD a 0 =
      ∑ c ∈ range (C.Z.getD (C.types.getD it.1 default).zi default).n,
        zqI (C.Z.getD (C.types.getD it.1 default).zi default) zmul a c *
          ((C.types.getD it.1 default).W.getD (it.2.2 * (d0 * d1 * d2 * d3) + v) []).getD c 0 := by
  unfold itemY
  simp only
  rw [getD_range_map _ _ _ _ hv, getD_range_map _ _ _ _ ha]

lemma sum_split (n : ℕ) (Wr YC YP YO : ℕ → Int) (coef z S : Int) (hP : ∀ a < n, YP a = YC a + z * S)
    (hO : ∀ a < n, YO a = S) :
    coef * ∑ a ∈ range n, Wr a * YC a = coef * ∑ a ∈ range n, Wr a * YP a + (-coef * z) * ∑ a ∈ range n, Wr a * YO a := by
  have h1 : ∑ a ∈ range n, Wr a * YP a = ∑ a ∈ range n, Wr a * (YC a + z * S) :=
    Finset.sum_congr rfl fun a ha => by rw [hP a (Finset.mem_range.1 ha)]
  have h2 : ∑ a ∈ range n, Wr a * YO a = ∑ a ∈ range n, Wr a * S :=
    Finset.sum_congr rfl fun a ha => by rw [hO a (Finset.mem_range.1 ha)]
  rw [h1, h2]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- **Item split.** `itemE C = itemE (pertCert C) + itemE (onesCert C)` (the latter with `zmul = 1`, coefficient
`−coef·zmul`), at every index. -/
lemma itemE_split (C : CertD) (zmul : ℕ) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) (i0 i1 i2 i3 : ℕ)
    (h0 : i0 < d0 * d0) (h1 : i1 < d1 * d1) (h2 : i2 < d2 * d2) (h3 : i3 < d3 * d3) :
    itemE C zmul coef d0 d1 d2 d3 it (itemY C zmul d0 d1 d2 d3 it) i0 i1 i2 i3 =
      itemE (pertCert C) zmul coef d0 d1 d2 d3 it (itemY (pertCert C) zmul d0 d1 d2 d3 it) i0 i1 i2 i3 +
      itemE (onesCert C) 1 (-coef * zmul) d0 d1 d2 d3 it (itemY (onesCert C) 1 d0 d1 d2 d3 it) i0 i1 i2 i3 := by
  have pos : ∀ {i d : ℕ}, i < d * d → 0 < d := fun {i d} h => Nat.pos_of_ne_zero fun hd => by simp [hd] at h
  have hv : mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3) < d0 * d1 * d2 * d3 :=
    mr4_lt _ _ _ _ _ _ _ _ (Nat.mod_lt _ (pos h0)) (Nat.mod_lt _ (pos h1)) (Nat.mod_lt _ (pos h2))
      (Nat.mod_lt _ (pos h3))
  have htP : (pertCert C).types = C.types := rfl
  have htO : (onesCert C).types = C.types := rfl
  have hZP : (pertCert C).Z = C.Z.map pertBlock := rfl
  have hZO : (onesCert C).Z = C.Z.map onesBlock := rfl
  set t := C.types.getD it.1 default with ht
  rcases Nat.lt_or_ge t.zi C.Z.length with hz | hz
  · have hbP : (pertCert C).Z.getD ((pertCert C).types.getD it.1 default).zi default =
        pertBlock (C.Z.getD t.zi default) := by rw [htP, hZP, getD_map_block _ _ _ hz]
    have hbO : (onesCert C).Z.getD ((onesCert C).types.getD it.1 default).zi default =
        onesBlock (C.Z.getD t.zi default) := by rw [htO, hZO, getD_map_block _ _ _ hz]
    set b := C.Z.getD t.zi default with hb
    unfold itemE
    simp only
    rw [htP, htO, hZP, hZO, getD_map_block _ _ _ hz, getD_map_block _ _ _ hz]
    rw [← hb]
    have hnP : (pertBlock b).n = b.n := rfl
    have hnO : (onesBlock b).n = b.n := rfl
    rw [hnP, hnO]
    set nn := d0 * d1 * d2 * d3 with hnn
    set v := mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3) with hvdef
    set μ := mr4 d0 d1 d2 d3 (i0 / d0) (i1 / d1) (i2 / d2) (i3 / d3) with hμ
    have eC : ∀ a ∈ range b.n, ((itemY C zmul d0 d1 d2 d3 it).getD v []).getD a 0 =
        ∑ c ∈ range b.n, zqI b zmul a c * (t.W.getD (it.2.2 * nn + v) []).getD c 0 :=
      fun a ha => itemY_entry C zmul d0 d1 d2 d3 it v a hv (Finset.mem_range.1 ha)
    have eP : ∀ a ∈ range b.n, ((itemY (pertCert C) zmul d0 d1 d2 d3 it).getD v []).getD a 0 =
        (∑ c ∈ range b.n, zqI b zmul a c * (t.W.getD (it.2.2 * nn + v) []).getD c 0) +
          zmul * ∑ c ∈ range b.n, (t.W.getD (it.2.2 * nn + v) []).getD c 0 := by
      intro a ha
      have ha' := Finset.mem_range.1 ha
      rw [itemY_entry (pertCert C) zmul d0 d1 d2 d3 it v a hv (by rw [hbP]; exact ha'), hbP, htP, hnP,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [zqI_pert b zmul a c ha' (Finset.mem_range.1 hc)]; ring
    have eO : ∀ a ∈ range b.n, ((itemY (onesCert C) 1 d0 d1 d2 d3 it).getD v []).getD a 0 =
        ∑ c ∈ range b.n, (t.W.getD (it.2.2 * nn + v) []).getD c 0 := by
      intro a ha
      have ha' := Finset.mem_range.1 ha
      rw [itemY_entry (onesCert C) 1 d0 d1 d2 d3 it v a hv (by rw [hbO]; exact ha'), hbO, htO, hnO]
      refine Finset.sum_congr rfl fun c hc => ?_
      rw [zqI_ones b a c ha' (Finset.mem_range.1 hc)]; ring
    exact sum_split b.n _ _ _ _ coef zmul _
      (fun a ha => by rw [eC a (Finset.mem_range.2 ha), eP a (Finset.mem_range.2 ha)])
      (fun a ha => eO a (Finset.mem_range.2 ha))
  · have hP0 : (pertCert C).Z.getD ((pertCert C).types.getD it.1 default).zi default = default := by
      rw [htP, hZP]; exact (getD_map_block_out C.Z pertBlock t.zi hz).1
    have hO0 : (onesCert C).Z.getD ((onesCert C).types.getD it.1 default).zi default = default := by
      rw [htO, hZO]; exact (getD_map_block_out C.Z onesBlock t.zi hz).1
    have hB0 : C.Z.getD t.zi default = default := (getD_map_block_out C.Z pertBlock t.zi hz).2
    unfold itemE
    simp only
    rw [hP0, hO0, ← ht, hB0]
    have : (default : NPT.Cert.PBlock).n = 0 := rfl
    simp [this]

lemma itemTF_length (C : CertD) (zmul : ℕ) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) :
    (itemTF C zmul coef d0 d1 d2 d3 it).length = d0 * d0 * (d1 * d1 * (d2 * d2 * (d3 * d3))) := by
  unfold itemTF
  simp only [List.length_flatMap, List.length_map, List.length_range, List.map_const', List.sum_replicate,
    smul_eq_mul]

/-- **Leaf split, per item**: entrywise values add up. -/
lemma itemTF_split (C : CertD) (zmul : ℕ) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) (k : ℕ) :
    gv (itemTF C zmul coef d0 d1 d2 d3 it) k =
      gv (itemTF (pertCert C) zmul coef d0 d1 d2 d3 it) k + gv (itemTF (onesCert C) 1 (-coef * zmul) d0 d1 d2 d3 it) k := by
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
    rw [hk', itemTF_gv _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3, itemTF_gv _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3,
      itemTF_gv _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3]
    exact itemE_split C zmul coef d0 d1 d2 d3 it i0 i1 i2 i3 h0 h1 h2 h3
  · rw [gv_eq_zero_of_le _ _ (by rw [itemTF_length]; exact hk), gv_eq_zero_of_le _ _ (by rw [itemTF_length]; exact hk),
      gv_eq_zero_of_le _ _ (by rw [itemTF_length]; exact hk)]
    simp

/-! ### Box trees are linear in the leaf tensors -/

section Lin

variable (S S1 S2 : Spec) (hR1 : S1.rows = S.rows) (hR2 : S2.rows = S.rows) (hD1 : S1.dimsq = S.dimsq)
  (hD2 : S2.dimsq = S.dimsq)
  (hL : ∀ m1 m2 m3 lf k, gv (S.leaf m1 m2 m3 lf) k = gv (S1.leaf m1 m2 m3 lf) k + gv (S2.leaf m1 m2 m3 lf) k)
include hR1 hR2 hD1 hD2 hL

lemma sL_split (m1 m2 m3 : ℕ) (lf : Leaf) (w0 j : ℕ) :
    sL S m1 m2 m3 lf w0 j = sL S1 m1 m2 m3 lf w0 j + sL S2 m1 m2 m3 lf w0 j := by
  unfold sL
  rw [hR1, hR2, hD1, hD2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i0 _ => ?_
  rw [hL]; ring

lemma sN1_split (m2 m3 : ℕ) (nd : Nd1) (w0 w1 j : ℕ) :
    sN1 S m2 m3 nd w0 w1 j = sN1 S1 m2 m3 nd w0 w1 j + sN1 S2 m2 m3 nd w0 w1 j := by
  unfold sN1
  rw [hR1, hR2, hD1, hD2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i1 _ => ?_
  rw [← mul_add, ← List.sum_map_add]
  congr 2
  refine List.map_congr_left fun lf _ => ?_
  exact sL_split S S1 S2 hR1 hR2 hD1 hD2 hL _ _ _ lf _ _

lemma sN2_split (m3 : ℕ) (nd : Nd2) (w0 w1 w2 j : ℕ) :
    sN2 S m3 nd w0 w1 w2 j = sN2 S1 m3 nd w0 w1 w2 j + sN2 S2 m3 nd w0 w1 w2 j := by
  unfold sN2
  rw [hR1, hR2, hD1, hD2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i2 _ => ?_
  rw [← mul_add, ← List.sum_map_add]
  congr 2
  refine List.map_congr_left fun n1 _ => ?_
  exact sN1_split S S1 S2 hR1 hR2 hD1 hD2 hL _ _ n1 _ _ _

lemma sN3_split (nd : Nd3) (w0 w1 w2 w3 : ℕ) :
    sN3 S nd w0 w1 w2 w3 = sN3 S1 nd w0 w1 w2 w3 + sN3 S2 nd w0 w1 w2 w3 := by
  unfold sN3
  rw [hR1, hR2, hD1, hD2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i3 _ => ?_
  rw [← mul_add, ← List.sum_map_add]
  congr 2
  refine List.map_congr_left fun n2 _ => ?_
  exact sN2_split S S1 S2 hR1 hR2 hD1 hD2 hL _ n2 _ _ _ _

lemma specTree_split (tree : List Nd3) (w0 w1 w2 w3 : ℕ) :
    specTree S tree w0 w1 w2 w3 = specTree S1 tree w0 w1 w2 w3 + specTree S2 tree w0 w1 w2 w3 := by
  unfold specTree
  rw [← List.sum_map_add]
  congr 1
  exact List.map_congr_left fun nd _ => sN3_split S S1 S2 hR1 hR2 hD1 hD2 hL nd _ _ _ _

end Lin

/-! ### Perturbed parts -/

/-- Rule groups as pairs of parts (perturbed certificate, all-ones correction); objective and equality parts as before. -/
def famPartsP (C : CertD) (zmul f : ℕ) (gs : List GrpF) (tabs : List (List (List (List SInt))))
    (itemFn : CertD → ℕ → Int → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ → List SInt)
    (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : List Part :=
  (gs.zip tabs).flatMap (fun Gt =>
    [⟨ruleSpecTI (pertCert C) zmul (-(den3 C.d : ℤ)) Gt.1.kpos Gt.1.lpos Gt.2 itemFn, Gt.1.tree⟩,
     ⟨ruleSpecTI (onesCert C) 1 (-(-(den3 C.d : ℤ)) * zmul) Gt.1.kpos Gt.1.lpos Gt.2 itemFn, Gt.1.tree⟩]) ++
    (if f = 0 then [rank1Part (objE zs za) (2 * C.Lden)] else []) ++ eqPartsF C f eqT

lemma partsF_cons (P : Part) (ps : List Part) (w0 w1 w2 w3 : ℕ) :
    partsF (P :: ps) w0 w1 w2 w3 = specTree P.S P.tree w0 w1 w2 w3 + partsF ps w0 w1 w2 w3 := by
  simp [partsF]

lemma ruleSpecTI_leaf_split (C : CertD) (zmul : ℕ) (coef : Int) (kpos lpos : List ℕ) (tab : List (List (List SInt)))
    (m1 m2 m3 : ℕ) (lf : Leaf) (k : ℕ) :
    gv ((ruleSpecTI C zmul coef kpos lpos tab itemTF).leaf m1 m2 m3 lf) k =
      gv ((ruleSpecTI (pertCert C) zmul coef kpos lpos tab itemTF).leaf m1 m2 m3 lf) k +
      gv ((ruleSpecTI (onesCert C) 1 (-coef * zmul) kpos lpos tab itemTF).leaf m1 m2 m3 lf) k := by
  simp only [ruleSpecTI]
  rw [gv_foldr_map, gv_foldr_map, gv_foldr_map, ← List.sum_map_add]
  congr 1
  refine List.map_congr_left fun it _ => ?_
  exact itemTF_split C zmul coef _ _ _ _ it k

/-- **The perturbed parts have the same word values.** -/
theorem partsF_famPartsP (C : CertD) (zmul f : ℕ) (gs : List GrpF) (tabs : List (List (List (List SInt))))
    (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) (w0 w1 w2 w3 : ℕ) :
    partsF (famPartsP C zmul f gs tabs itemTF zs za eqT) w0 w1 w2 w3 =
      partsF (famPartsKI C zmul f gs tabs itemTF zs za eqT) w0 w1 w2 w3 := by
  unfold famPartsP famPartsKI
  rw [partsF_append, partsF_append, partsF_append, partsF_append]
  congr 2
  induction gs generalizing tabs with
  | nil => simp [partsF]
  | cons G gs ih =>
    cases tabs with
    | nil => simp [partsF]
    | cons tab tabs =>
      simp only [List.zip_cons_cons, List.flatMap_cons, List.map_cons, List.cons_append, List.nil_append]
      rw [partsF_cons, partsF_cons, partsF_cons, ← ih tabs]
      simp only
      rw [specTree_split (ruleSpecTI C zmul (-(den3 C.d : ℤ)) G.kpos G.lpos tab itemTF)
        (ruleSpecTI (pertCert C) zmul (-(den3 C.d : ℤ)) G.kpos G.lpos tab itemTF)
        (ruleSpecTI (onesCert C) 1 (-(-(den3 C.d : ℤ)) * zmul) G.kpos G.lpos tab itemTF) rfl rfl rfl rfl
        (ruleSpecTI_leaf_split C zmul _ G.kpos G.lpos tab)]
      ring

end NPT.Cert.Ident
