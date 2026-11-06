/-
NPT.Cert.Ident.Extract — correctness of the digit extraction: if a packed slice has signed digits
`|d p| < 2^(b-1)`, then `extL` on the offset field returns the digits `d p + 2^(b-1)`, and `unfield` recovers `d p`.
-/
import NPT.Cert.Ident.Lemmas

open BigOperators Finset

namespace NPT.Cert.Ident

/-- The number with base-`B` digits `f 0, …, f (L-1)`. -/
def digNum (B : Nat) (f : Nat → Nat) (L : Nat) : Nat := ∑ p ∈ range L, f p * B ^ p

lemma digNum_succ (B : Nat) (f : Nat → Nat) (L : Nat) : digNum B f (L + 1) = digNum B f L + f L * B ^ L := by
  simp [digNum, Finset.sum_range_succ]

lemma digNum_lt {B : Nat} {f : Nat → Nat} (hB : 0 < B) : ∀ L, (∀ p < L, f p < B) → digNum B f L < B ^ L
  | 0, _ => by simp [digNum]
  | L + 1, hf => by
    rw [digNum_succ, pow_succ]
    have h1 := digNum_lt hB L fun p hp => hf p (by omega)
    have h2 : f L ≤ B - 1 := Nat.le_sub_one_of_lt (hf L (by omega))
    have h3 : f L * B ^ L ≤ (B - 1) * B ^ L := Nat.mul_le_mul_right _ h2
    have h4 : (B - 1) * B ^ L + B ^ L = B ^ L * B := by
      rw [Nat.sub_one_mul, mul_comm (B ^ L) B]
      have : B ^ L ≤ B * B ^ L := Nat.le_mul_of_pos_left _ hB
      omega
    omega

lemma digNum_add (B : Nat) (f : Nat → Nat) (L1 L2 : Nat) :
    digNum B f (L1 + L2) = digNum B f L1 + B ^ L1 * digNum B (fun p => f (L1 + p)) L2 := by
  simp only [digNum, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [pow_add]; ring

lemma digNum_mod_div {B : Nat} {f : Nat → Nat} (hB : 0 < B) (L1 L2 : Nat) (hf : ∀ p < L1, f p < B) :
    digNum B f (L1 + L2) % B ^ L1 = digNum B f L1 ∧
      digNum B f (L1 + L2) / B ^ L1 = digNum B (fun p => f (L1 + p)) L2 := by
  have hlt := digNum_lt hB L1 hf
  have hpos : 0 < B ^ L1 := Nat.pow_pos hB
  rw [digNum_add]
  constructor
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, zero_add]

lemma extL_eq (b : Nat) : ∀ (fuel L N : Nat) (acc : List Nat) (f : Nat → Nat), 0 < L → L ≤ 2 ^ fuel →
    (∀ p < L, f p < 2 ^ b) → N = digNum (2 ^ b) f L → extL b fuel L N acc = (List.range L).map f ++ acc
  | 0, L, N, acc, f, hL, hL2, hf, hN => by
    have : L = 1 := by simp at hL2; omega
    subst this
    simp [extL, hN, digNum]
  | fuel + 1, L, N, acc, f, hL, hL2, hf, hN => by
    unfold extL
    split_ifs with h1
    · have : L = 1 := by omega
      subst this
      simp [hN, digNum]
    · set L1 := L / 2 with hL1
      have hB : 0 < 2 ^ b := Nat.pow_pos (by norm_num)
      have hsplit : L = L1 + (L - L1) := by omega
      have hpow : (2 : Nat) ^ (b * L1) = (2 ^ b) ^ L1 := by rw [pow_mul]
      have hmd := digNum_mod_div hB L1 (L - L1) (f := f) fun p hp => hf p (by omega)
      rw [← hsplit] at hmd
      have hlow : N &&& ((1 <<< (b * L1)) - 1) = digNum (2 ^ b) f L1 := by
        rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, hpow, hN, hmd.1]
      have hhigh : N >>> (b * L1) = digNum (2 ^ b) (fun p => f (L1 + p)) (L - L1) := by
        rw [Nat.shiftRight_eq_div_pow, hpow, hN, hmd.2]
      rw [hlow, hhigh,
        extL_eq b fuel (L - L1) _ acc (fun p => f (L1 + p)) (by omega)
          (by rw [pow_succ] at hL2; omega) (fun p hp => hf _ (by omega)) rfl,
        extL_eq b fuel L1 _ _ f (by omega) (by rw [pow_succ] at hL2; omega) (fun p hp => hf p (by omega)) rfl,
        ← List.append_assoc]
      congr 1
      conv_rhs => rw [hsplit, List.range_add, List.map_append, List.map_map]
      rfl

lemma extL_length (b : Nat) : ∀ (fuel L N : Nat) (acc : List Nat), 0 < L → L ≤ 2 ^ fuel →
    (extL b fuel L N acc).length = L + acc.length
  | 0, L, N, acc, hL, hL2 => by
    have : L = 1 := by simp at hL2; omega
    subst this; simp [extL]; omega
  | fuel + 1, L, N, acc, hL, hL2 => by
    unfold extL
    split_ifs with h1
    · simp; omega
    · rw [extL_length b fuel (L / 2) _ _ (by omega) (by rw [pow_succ] at hL2; omega),
        extL_length b fuel (L - L / 2) _ _ (by omega) (by rw [pow_succ] at hL2; omega)]
      omega

/-! ### Offsets and fields -/

lemma geom_sum_nat (B L : Nat) (hB : 1 ≤ B) : (B - 1) * ∑ p ∈ range L, B ^ p = B ^ L - 1 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih, pow_succ]
    have hX : 1 ≤ B ^ L := Nat.one_le_pow _ _ hB
    have hXB : 1 ≤ B ^ L * B := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    zify [hX, hB, hXB]
    ring

lemma offL_eq (b L : Nat) (hb : 0 < b) : offL b L = digNum (2 ^ b) (fun _ => 2 ^ (b - 1)) L := by
  unfold offL digNum
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.one_shiftLeft]
  have hB : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hpos : 0 < 2 ^ b - 1 := by have := Nat.one_lt_two_pow (n := b) (by omega); omega
  have hS : (2 ^ (b * L) - 1) / (2 ^ b - 1) = ∑ p ∈ range L, (2 ^ b) ^ p := by
    rw [pow_mul, ← geom_sum_nat (2 ^ b) L hB, Nat.mul_div_cancel_left _ hpos]
  rw [hS, Finset.mul_sum]

/-- The field of a digit `d` (offset `h = 2^(b-1)`). -/
def fld (b : Nat) (d : Int) : Nat := (d + 2 ^ (b - 1)).toNat

lemma fld_lt (b : Nat) (hb : 0 < b) (d : Int) (hd : |d| < 2 ^ (b - 1)) : fld b d < 2 ^ b := by
  have h2 : (2 : Int) ^ b = 2 * 2 ^ (b - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hd' := abs_lt.1 hd
  have h0 : 0 ≤ d + 2 ^ (b - 1) := by linarith
  have : ((fld b d : Nat) : Int) < 2 ^ b := by
    unfold fld; rw [Int.toNat_of_nonneg h0, h2]; linarith
  exact_mod_cast this

lemma unfield_fld (b : Nat) (d : Int) (hd : |d| < 2 ^ (b - 1)) : (unfield (1 <<< (b - 1)) (fld b d)).val = d := by
  have := abs_lt.1 hd
  unfold unfield fld
  rw [Nat.one_shiftLeft]
  have hnn : 0 ≤ d + 2 ^ (b - 1) := by omega
  split_ifs with h
  · simp only [SInt.val, ite_false, Bool.false_eq_true]
    push_cast [h]
    rw [Int.toNat_of_nonneg hnn]; ring
  · simp only [SInt.val, ite_true]
    push Not at h
    have h' : ((d + 2 ^ (b - 1)).toNat : Int) < 2 ^ (b - 1) := by exact_mod_cast h
    rw [Int.toNat_of_nonneg hnn] at h'
    rw [Nat.cast_sub (le_of_lt h), Int.toNat_of_nonneg hnn]; push_cast; ring

lemma fieldNat_eq (b L : Nat) (hb : 0 < b) (s : SInt) (d : Nat → Int) (hd : ∀ p < L, |d p| < 2 ^ (b - 1))
    (hs : s.val = ∑ p ∈ range L, d p * 2 ^ (b * p)) :
    fieldNat (offL b L) s = digNum (2 ^ b) (fun p => fld b (d p)) L := by
  rw [offL_eq b L hb]
  have key : ((digNum (2 ^ b) (fun _ => 2 ^ (b - 1)) L : Nat) : Int) + s.val =
      ((digNum (2 ^ b) (fun p => fld b (d p)) L : Nat) : Int) := by
    simp only [digNum, hs]
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have := abs_lt.1 (hd p (Finset.mem_range.1 hp))
    unfold fld
    rw [Int.toNat_of_nonneg (by omega), pow_mul]
    push_cast; ring
  unfold fieldNat
  rcases s with ⟨_ | _, m⟩
  · simp only [SInt.val, Bool.false_eq_true, ite_false] at key ⊢
    exact_mod_cast key
  · simp only [SInt.val, ite_true] at key ⊢
    have hle : m ≤ digNum (2 ^ b) (fun _ => 2 ^ (b - 1)) L := by omega
    zify [hle]; omega

end NPT.Cert.Ident
