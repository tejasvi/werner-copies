/-
NPT.Cert.Ident.ItemF — index-based leaf tensors of rule-group items.
Entry `(i0,i1,i2,i3)` (`i_l = μ_l·d_l + ν_l`) of `itemTF` is `coef · Σ_a W[r·nn+flat μ][a] · Y[flat ν][a]` with
`Y[v][a] = Σ_c Zq[a][c] · W[s·nn+v][c]` and `Zq = 2·Lden·Z` an integer matrix.
-/
import NPT.Cert.Ident.KmatF
import NPT.Cert.Ident.Family
import NPT.Cert.Ident.PiSum

open BigOperators Finset NPT.Cert.Sem

namespace NPT.Cert.Ident

/-- `2·Lden·Z_t[a][c]` as an integer: `zget·zmul + 2·num` (`num` from the correction entries, as `uval`). -/
def zqI (b : NPT.Cert.PBlock) (zmul : ℕ) (a c : ℕ) : Int :=
  b.zget a c * zmul + (match b.ufind a c with | some e => 2 * e.2.2 | none => 0)

lemma zqI_eq (b : NPT.Cert.PBlock) (Lden zmul : ℕ) (hz : 2 * Lden = zmul * 2 ^ b.E) (hL : 0 < Lden) (a c : ℕ) :
    (zqI b zmul a c : ℚ) = 2 * Lden * CertD.zq b Lden a c := by
  have hL' : (Lden : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  have hz' : (2 * Lden : ℚ) = zmul * 2 ^ b.E := by exact_mod_cast hz
  have h2 : (2 : ℚ) ^ b.E ≠ 0 := pow_ne_zero _ two_ne_zero
  have h1 : (2 * Lden : ℚ) * ((b.zget a c : ℚ) / 2 ^ b.E) = (b.zget a c : ℚ) * zmul := by
    rw [hz']; field_simp
  unfold zqI CertD.zq NPT.Cert.PBlock.uval
  cases b.ufind a c with
  | none =>
    simp only [add_zero]
    push_cast
    rw [← h1]
  | some e =>
    have h3 : (2 * Lden : ℚ) * ((e.2.2 : ℚ) / Lden) = 2 * e.2.2 := by field_simp
    push_cast
    rw [mul_add, h1, h3]

/-- `flat μ` (mixed radix, `μ0` most significant) from the four digits. -/
def mr4 (d0 d1 d2 d3 a b c e : ℕ) : ℕ := ((a * d1 + b) * d2 + c) * d3 + e

/-- One entry of an item tensor. -/
def itemE (C : CertD) (zmul : ℕ) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) (Y : List (List Int))
    (i0 i1 i2 i3 : ℕ) : Int :=
  let t := C.types.getD it.1 default
  let b := C.Z.getD t.zi default
  let nn := d0 * d1 * d2 * d3
  coef * ∑ a ∈ range b.n, (t.W.getD (it.2.1 * nn + mr4 d0 d1 d2 d3 (i0 / d0) (i1 / d1) (i2 / d2) (i3 / d3)) []).getD a 0 *
    (Y.getD (mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3)) []).getD a 0

/-- `Y[v][a] = Σ_c Zq[a][c] W[s·nn+v][c]`. -/
def itemY (C : CertD) (zmul : ℕ) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) : List (List Int) :=
  let t := C.types.getD it.1 default
  let b := C.Z.getD t.zi default
  let nn := d0 * d1 * d2 * d3
  (List.range nn).map fun v => (List.range b.n).map fun a =>
    ∑ c ∈ range b.n, zqI b zmul a c * (t.W.getD (it.2.2 * nn + v) []).getD c 0

/-- The leaf tensor of one item `(t, r, s)`, nested over `i0, i1, i2, i3` (`i_l < d_l²`). -/
def itemTF (C : CertD) (zmul : ℕ) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) : List SInt :=
  let Y := itemY C zmul d0 d1 d2 d3 it
  (List.range (d0 * d0)).flatMap fun i0 => (List.range (d1 * d1)).flatMap fun i1 =>
    (List.range (d2 * d2)).flatMap fun i2 => (List.range (d3 * d3)).map fun i3 =>
      SInt.ofInt (itemE C zmul coef d0 d1 d2 d3 it Y i0 i1 i2 i3)

lemma getD_range_map {β : Type} (n : ℕ) (f : ℕ → β) (d : β) (i : ℕ) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

lemma range_getD (n i : ℕ) (hi : i < n) : (List.range n).getD i 0 = i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_range hi]; rfl

lemma idx_lt (a b A B : ℕ) (ha : a < A) (hb : b < B) : a * B + b < A * B := by
  calc a * B + b < a * B + B := by omega
    _ = (a + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right _ ha

lemma itemTF_gv (C : CertD) (zmul : ℕ) (coef : Int) (d0 d1 d2 d3 : ℕ) (it : ℕ × ℕ × ℕ) (i0 i1 i2 i3 : ℕ)
    (h0 : i0 < d0 * d0) (h1 : i1 < d1 * d1) (h2 : i2 < d2 * d2) (h3 : i3 < d3 * d3) :
    gv (itemTF C zmul coef d0 d1 d2 d3 it)
      (i0 * (d1 * d1 * (d2 * d2) * (d3 * d3)) + (i1 * (d2 * d2 * (d3 * d3)) + (i2 * (d3 * d3) + i3))) =
      itemE C zmul coef d0 d1 d2 d3 it (itemY C zmul d0 d1 d2 d3 it) i0 i1 i2 i3 := by
  unfold itemTF gv
  simp only
  have L3 : ∀ (i0 i1 i2 : ℕ), ((List.range (d3 * d3)).map fun i3 =>
      SInt.ofInt (itemE C zmul coef d0 d1 d2 d3 it (itemY C zmul d0 d1 d2 d3 it) i0 i1 i2 i3)).length = d3 * d3 := by
    intros; simp
  have L2 : ∀ (i0 i1 : ℕ), ((List.range (d2 * d2)).flatMap fun i2 => (List.range (d3 * d3)).map fun i3 =>
      SInt.ofInt (itemE C zmul coef d0 d1 d2 d3 it (itemY C zmul d0 d1 d2 d3 it) i0 i1 i2 i3)).length =
      d2 * d2 * (d3 * d3) := by
    intros; rw [List.length_flatMap]; simp only [L3, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  have L1 : ∀ (i0 : ℕ), ((List.range (d1 * d1)).flatMap fun i1 => (List.range (d2 * d2)).flatMap fun i2 =>
      (List.range (d3 * d3)).map fun i3 =>
      SInt.ofInt (itemE C zmul coef d0 d1 d2 d3 it (itemY C zmul d0 d1 d2 d3 it) i0 i1 i2 i3)).length =
      d1 * d1 * (d2 * d2 * (d3 * d3)) := by
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
  rw [getD_range_map _ _ _ _ h3, SInt.val_ofInt]

end NPT.Cert.Ident
