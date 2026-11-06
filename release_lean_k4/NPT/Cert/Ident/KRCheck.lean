/-
NPT.Cert.Ident.KRCheck — the mod-`p` class-sum check: digit fields of packed slices by recursors
(`fieldsK`), routed with counts (`KRRoute`), checked mod `p` (`checkKR`).  Soundness (`checkKR_sound`): if the
slices pack `F` with `|F| < 2^(b-1)`, every class sum of `F` is `≡ 0 (mod p)`.
-/
import NPT.Cert.Ident.KRRoute
import NPT.Cert.Ident.KRLibEq
import NPT.Cert.Ident.Family

open BigOperators Finset NPT.Cert.Sem NPT.Cert.Ident

namespace NPT.Cert.KR

/-- Digit fields of the 24 slices, slice by slice (recursors; `List.range 24` and `getD` only 24 times). -/
noncomputable def fieldsK (b L off : ℕ) (slices : List SInt) : List ℕ :=
  foldrR (fun w3 acc => extLR b 15 L (fieldR off (slices.getD w3 SInt.zero)) acc) [] (List.range 24)

/-- **The check**: route the fields by class and test every class mod `p` (offset `h = 2^(b-1)`). -/
noncomputable def checkKR (p b : ℕ) (slices : List SInt) (cls : List ℕ) (t0 : AT) : Bool :=
  RT.okMod p (Nat.shiftLeft 1 (Nat.sub b 1)) (routeR (fieldsK b slen (offL b slen) slices) cls (toRT t0))

theorem extL_acc (b : ℕ) : ∀ (fuel L N : ℕ) (acc : List ℕ), extL b fuel L N acc = extL b fuel L N [] ++ acc
  | 0, _, _, _ => rfl
  | fuel + 1, L, N, acc => by
    unfold extL
    split_ifs
    · rfl
    · rw [extL_acc b fuel (L - L / 2) _ acc, extL_acc b fuel (L / 2) _ (extL b fuel (L - L / 2) _ [] ++ acc),
        extL_acc b fuel (L / 2) _ (extL b fuel (L - L / 2) _ []), List.append_assoc]

theorem fieldsK_eq (b L off : ℕ) (slices : List SInt) :
    fieldsK b L off slices = (List.range 24).flatMap fun w3 => extL b 15 L (fieldNat off (slices.getD w3 SInt.zero)) [] := by
  unfold fieldsK
  rw [foldrR_eq]
  induction (List.range 24) with
  | nil => rfl
  | cons w3 ws ih =>
    rw [List.foldr_cons, ih, List.flatMap_cons, extLR_eq, fieldR_eq, extL_acc]

theorem fieldsK_length (b : ℕ) (slices : List SInt) : (fieldsK b slen (offL b slen) slices).length = 24 * slen := by
  rw [fieldsK_eq, List.length_flatMap]
  simp only [extL_length b 15 slen _ [] (by decide) (by decide), List.length_nil, add_zero]
  simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]

/-- **Fields of packed slices.** -/
theorem fieldsK_val (b : ℕ) (hb : 0 < b) (slices : List SInt) (F : ℕ → ℕ → ℕ → ℕ → ℤ)
    (hS : ∀ w3 < 24, gv slices w3 = ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24,
      F w0 w1 w2 w3 * 2 ^ (b * w0)) * 2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2))
    (hF : ∀ q < 24 * slen, |F (wd q).1 (wd q).2.1 (wd q).2.2.1 (wd q).2.2.2| < 2 ^ (b - 1))
    (q : ℕ) (hq : q < 24 * slen) :
    (fieldsK b slen (offL b slen) slices).getD q 0 = fld b (F (wd q).1 (wd q).2.1 (wd q).2.2.1 (wd q).2.2.2) := by
  set w3 := q / slen with hw3
  set p := q % slen with hp
  have hq' : q = w3 * slen + p := by rw [hw3, hp]; exact (Nat.div_add_mod' q slen).symm
  have hw3l : w3 < 24 := by rw [hw3]; exact Nat.div_lt_of_lt_mul (by simpa [mul_comm] using hq)
  have hpl : p < slen := Nat.mod_lt _ (by decide)
  have hlen : ∀ w : ℕ, (extL b 15 slen (fieldNat (offL b slen) (slices.getD w SInt.zero)) []).length = slen := by
    intro w; rw [extL_length b 15 slen _ [] (by decide) (by decide)]; rfl
  rw [fieldsK_eq, hq', flatMap_getD _ slen hlen 0 (List.range 24) 0 w3 p (by simpa using hw3l) hpl]
  rw [show (List.range 24).getD w3 0 = w3 by rw [List.getD_eq_getElem?_getD, List.getElem?_range hw3l]; rfl]
  set d : ℕ → ℤ := fun p => F (p % 24) (p / 24 % 24) (p / 576) w3 with hd
  have hdb : ∀ p' < slen, |d p'| < 2 ^ (b - 1) := by
    intro p' hp'
    have := hF (w3 * slen + p') (by unfold slen at hp' ⊢; omega)
    have e0 : (w3 * slen + p') % 24 = p' % 24 := by unfold slen; omega
    have e1 : (w3 * slen + p') / 24 % 24 = p' / 24 % 24 := by unfold slen; omega
    have e2 : (w3 * slen + p') / 576 % 24 = p' / 576 := by unfold slen at hp' ⊢; omega
    have e3 : (w3 * slen + p') / 13824 = w3 := by unfold slen at hp' ⊢; omega
    simpa [wd, e0, e1, e2, e3, hd] using this
  have hsv : (slices.getD w3 SInt.zero).val = ∑ p' ∈ range slen, d p' * 2 ^ (b * p') := by
    have := hS w3 hw3l
    rw [pack3] at this
    exact this
  rw [fieldNat_eq b slen hb _ d hdb hsv,
    extL_eq b 15 slen _ [] (fun p => fld b (d p)) (by decide) (by decide) (fun p' hp' => fld_lt b hb _ (hdb p' hp')) rfl,
    List.append_nil, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hpl]
  simp only [Option.map_some, Option.getD_some]
  have e0 : (w3 * slen + p) % 24 = p % 24 := by unfold slen; omega
  have e1 : (w3 * slen + p) / 24 % 24 = p / 24 % 24 := by unfold slen; omega
  have e2 : (w3 * slen + p) / 576 % 24 = p / 576 := by unfold slen at hpl ⊢; omega
  have e3 : (w3 * slen + p) / 13824 = w3 := by unfold slen at hpl ⊢; omega
  simp only [wd, e0, e1, e2, e3, hd]

/-- **Soundness of the mod-`p` check.** -/
theorem checkKR_sound (p b : ℕ) (hb : 0 < b) (slices : List SInt) (cls : List ℕ) (t0 : AT)
    (h : checkKR p b slices cls t0 = true) (F : ℕ → ℕ → ℕ → ℕ → ℤ)
    (hS : ∀ w3 < 24, gv slices w3 = ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24,
      F w0 w1 w2 w3 * 2 ^ (b * w0)) * 2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2))
    (hF : ∀ q < 24 * slen, |F (wd q).1 (wd q).2.1 (wd q).2.2.1 (wd q).2.2.2| < 2 ^ (b - 1))
    (hcls : cls.length = 24 * slen) (q : ℕ) (hq : q < 24 * slen) :
    (∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
      F (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0)) ≡ 0 [ZMOD p] := by
  set vs := fieldsK b slen (offL b slen) slices with hvs
  have hvl : vs.length = 24 * slen := fieldsK_length b slices
  have hlen : vs.length = cls.length := by rw [hvl, hcls]
  have hsound := okMod_sound p (Nat.shiftLeft 1 (Nat.sub b 1)) vs cls t0 h hlen q (by rw [hvl]; exact hq)
  rw [hvl] at hsound
  set H : ℕ := Nat.shiftLeft 1 (Nat.sub b 1) with hH
  have hH0 : H = 2 ^ (b - 1) := by
    rw [hH, show Nat.shiftLeft 1 (Nat.sub b 1) = 1 <<< (b - 1) from rfl, Nat.one_shiftLeft]
  have hH' : (H : ℤ) = 2 ^ (b - 1) := by rw [hH0]; push_cast; ring
  -- fields as integers: F + H
  have hval : ∀ q' ∈ range (24 * slen), ((vs.getD q' 0 : ℕ) : ℤ) =
      F (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 + 2 ^ (b - 1) := by
    intro q' hq'
    have hq'' := Finset.mem_range.1 hq'
    rw [hvs, fieldsK_val b hb slices F hS hF q' hq'']
    unfold fld
    have := abs_lt.1 (hF q' hq'')
    rw [Int.toNat_of_nonneg (by linarith)]
  -- the sum of fields over the class = class sum of F + count · H
  set S := ∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then
    F (wd q').1 (wd q').2.1 (wd q').2.2.1 (wd q').2.2.2 else 0) with hSdef
  set cnt := ((range (24 * slen)).filter fun q' => cls.getD q' 0 = cls.getD q 0).card with hcnt
  have hsum : ((∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then vs.getD q' 0 else 0) : ℕ) : ℤ) =
      S + cnt * 2 ^ (b - 1) := by
    push_cast
    rw [hSdef, hcnt, Finset.card_filter, Nat.cast_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q' hq' => ?_
    split_ifs with hc
    · rw [hval q' hq']; push_cast; ring
    · push_cast; ring
  have hmod : ((∑ q' ∈ range (24 * slen), (if cls.getD q' 0 = cls.getD q 0 then vs.getD q' 0 else 0) : ℕ) : ℤ) ≡
      ((cnt * H : ℕ) : ℤ) [ZMOD p] := by
    rw [Int.ModEq]; exact_mod_cast congrArg (fun x : ℕ => (x : ℤ)) hsound
  rw [hsum] at hmod
  push_cast at hmod
  rw [hH'] at hmod
  have hmod' : S + (cnt : ℤ) * 2 ^ (b - 1) ≡ 0 + (cnt : ℤ) * 2 ^ (b - 1) [ZMOD p] := by rw [zero_add]; exact hmod
  exact Int.ModEq.add_right_cancel' _ hmod'

end NPT.Cert.KR
