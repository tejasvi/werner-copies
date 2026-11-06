/-
NPT.Cert.Ident.Lemmas — correctness of the arithmetic in `NPT.Cert.Ident.Core`.
-/
import NPT.Cert.Ident.Core
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open BigOperators Finset

namespace NPT.Cert.Ident

namespace SInt

@[simp] lemma val_zero : SInt.zero.val = 0 := by simp [val, zero]

@[simp] lemma val_mk_false (m : Nat) : (SInt.mk false m).val = m := by simp [val]

lemma val_ofInt (z : Int) : (ofInt z).val = z := by
  cases z with
  | ofNat m => simp [ofInt, val]
  | negSucc m => simp [ofInt, val, Int.negSucc_eq]

lemma val_add (a b : SInt) : (a.add b).val = a.val + b.val := by
  rcases a with ⟨_ | _, m⟩ <;> rcases b with ⟨_ | _, k⟩ <;> simp only [add, val] <;>
    (try split_ifs) <;> simp_all <;> omega

lemma val_mul (a b : SInt) : (a.mul b).val = a.val * b.val := by
  rcases a with ⟨_ | _, m⟩ <;> rcases b with ⟨_ | _, k⟩ <;> simp [mul, val]

lemma val_shl (a : SInt) (k : Nat) : (a.shl k).val = a.val * 2 ^ k := by
  rcases a with ⟨_ | _, m⟩ <;> simp [shl, val, Nat.shiftLeft_eq]

lemma val_neg' (a : SInt) : a.neg'.val = -a.val := by
  rcases a with ⟨_ | _, m⟩ <;> simp [neg', val]

end SInt

/-- Value of entry `j` (default `0`). -/
def gv (xs : List SInt) (j : Nat) : Int := (xs.getD j SInt.zero).val

@[simp] lemma gv_nil (j : Nat) : gv [] j = 0 := by simp [gv]
@[simp] lemma gv_cons_zero (x : SInt) (xs : List SInt) : gv (x :: xs) 0 = x.val := by simp [gv]
@[simp] lemma gv_cons_succ (x : SInt) (xs : List SInt) (j : Nat) : gv (x :: xs) (j + 1) = gv xs j := by simp [gv]

lemma gv_addL : ∀ (xs ys : List SInt) (j : Nat), gv (addL xs ys) j = gv xs j + gv ys j
  | [], ys, j => by simp [addL]
  | x :: xs, [], j => by simp [addL]
  | x :: xs, y :: ys, 0 => by simp [addL, SInt.val_add]
  | x :: xs, y :: ys, j + 1 => by simp [addL, gv_addL xs ys j]

lemma gv_mulL (c : SInt) : ∀ (xs : List SInt) (j : Nat), gv (mulL c xs) j = c.val * gv xs j
  | [], j => by simp [mulL]
  | x :: xs, 0 => by simp [mulL, SInt.val_mul]
  | x :: xs, j + 1 => by simp [mulL, gv_mulL c xs j]

lemma gv_shlL (k : Nat) : ∀ (xs : List SInt) (j : Nat), gv (shlL k xs) j = gv xs j * 2 ^ k
  | [], j => by simp [shlL]
  | x :: xs, 0 => by simp [shlL, SInt.val_shl]
  | x :: xs, j + 1 => by simp [shlL, gv_shlL k xs j]

lemma gv_foldr_addL (Ls : List (List SInt)) (j : Nat) :
    gv (Ls.foldr addL []) j = (Ls.map fun L => gv L j).sum := by
  induction Ls with
  | nil => simp
  | cons L Ls ih => simp [gv_addL, ih]

/-- `lincomb` as a sum over the common length. -/
lemma gv_lincomb : ∀ (cs : List SInt) (vs : List (List SInt)) (j : Nat),
    gv (lincomb cs vs) j = ∑ i ∈ range (min cs.length vs.length), (cs.getD i SInt.zero).val * gv (vs.getD i []) j
  | [], vs, j => by simp [lincomb]
  | c :: cs, [], j => by simp [lincomb]
  | c :: cs, v :: vs, j => by
    rw [lincomb, gv_addL, gv_mulL, gv_lincomb cs vs j]
    simp only [List.length_cons, Nat.add_min_add_right]
    rw [Finset.sum_range_succ']
    simp [add_comm]

lemma dotS_val : ∀ (cs vs : List SInt),
    (dotS cs vs).val = ∑ i ∈ range (min cs.length vs.length), (cs.getD i SInt.zero).val * (vs.getD i SInt.zero).val
  | [], vs => by simp [dotS]
  | c :: cs, [] => by simp [dotS]
  | c :: cs, v :: vs => by
    rw [dotS, SInt.val_add, SInt.val_mul, dotS_val cs vs]
    simp only [List.length_cons, Nat.add_min_add_right]
    rw [Finset.sum_range_succ']
    simp [add_comm]

lemma chunks_length (M : Nat) : ∀ (n : Nat) (xs : List SInt), (chunks M n xs).length = n
  | 0, _ => rfl
  | n + 1, xs => by simp [chunks, chunks_length M n]

lemma gv_chunks (M : Nat) : ∀ (n : Nat) (xs : List SInt) (i j : Nat), i < n → j < M →
    gv ((chunks M n xs).getD i []) j = gv xs (i * M + j)
  | 0, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, xs, 0, j, _, hj => by
    simp only [chunks, List.getD_cons_zero, zero_mul, zero_add, gv]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]
  | n + 1, xs, i + 1, j, hi, hj => by
    simp only [chunks, List.getD_cons_succ]
    rw [gv_chunks M n (xs.drop M) i j (by omega) hj, gv, gv, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2; ring

/-! ### Packing -/

lemma packH_val (s : Nat) : ∀ (as : List SInt),
    (packH s as).val = ∑ w ∈ range as.length, (as.getD w SInt.zero).val * 2 ^ (s * w)
  | [] => by simp [packH]
  | a :: as => by
    rw [packH, SInt.val_add, SInt.val_shl, packH_val s as, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, mul_zero, pow_zero, mul_one, Finset.sum_mul]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mul_assoc, ← pow_add]; congr 2

lemma colStage_gv (P : List SInt) (M : Nat) (xs : List SInt) (j : Nat) (hj : j < M) :
    gv (colStage P M xs) j = ∑ i ∈ range P.length, (P.getD i SInt.zero).val * gv xs (i * M + j) := by
  rw [colStage, gv_lincomb, chunks_length, min_self]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [gv_chunks M _ xs i j (Finset.mem_range.1 hi) hj]


/-! ### Balanced combination -/

lemma pairUp_length (s : Nat) : ∀ (Ls : List (List SInt)), (pairUp s Ls).length = (Ls.length + 1) / 2
  | [] => by simp [pairUp]
  | [a] => by simp [pairUp]
  | a :: b :: rest => by
    simp only [pairUp, List.length_cons, pairUp_length s rest]; omega

lemma gv_pairUp (s : Nat) : ∀ (Ls : List (List SInt)) (v j : Nat),
    gv ((pairUp s Ls).getD v []) j = gv (Ls.getD (2 * v) []) j + gv (Ls.getD (2 * v + 1) []) j * 2 ^ s
  | [], v, j => by simp [pairUp]
  | [a], 0, j => by simp [pairUp]
  | [a], v + 1, j => by
    simp only [pairUp, List.getD_cons_succ, List.getD_nil, gv_nil]
    rw [show 2 * (v + 1) = 2 * v + 1 + 1 by ring]; simp
  | a :: b :: rest, 0, j => by simp [pairUp, gv_addL, gv_shlL]
  | a :: b :: rest, v + 1, j => by
    rw [show 2 * (v + 1) = 2 * v + 1 + 1 by ring]
    simp only [pairUp, List.getD_cons_succ]
    exact gv_pairUp s rest v j

/-- Pairing of a range sum. -/
lemma sum_range_pairs (f : Nat → Int) (m : Nat) :
    ∑ w ∈ range (2 * m), f w = ∑ v ∈ range m, (f (2 * v) + f (2 * v + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

lemma combine_gv : ∀ (fuel s : Nat) (Ls : List (List SInt)) (j : Nat), Ls.length ≤ 2 ^ fuel →
    gv (combine fuel s Ls) j = ∑ w ∈ range Ls.length, gv (Ls.getD w []) j * 2 ^ (s * w)
  | 0, s, [], j, _ => by simp [combine]
  | fuel + 1, s, [], j, _ => by simp [combine]
  | 0, s, [a], j, _ => by simp [combine]
  | fuel + 1, s, [a], j, _ => by simp [combine]
  | 0, s, a :: b :: rest, j, h => by simp at h
  | fuel + 1, s, a :: b :: rest, j, h => by
    have hl : (pairUp s (a :: b :: rest)).length ≤ 2 ^ fuel := by
      rw [pairUp_length]; simp only [List.length_cons] at h ⊢; rw [pow_succ] at h; omega
    rw [combine, combine_gv fuel (2 * s) _ j hl, pairUp_length]
    simp only [gv_pairUp]
    set L := a :: b :: rest with hL
    set n := L.length
    -- extend to an even length with zero terms
    have hz : ∀ w, n ≤ w → gv (L.getD w []) j = 0 := by
      intro w hw; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hw]; simp
    have key : ∑ w ∈ range n, gv (L.getD w []) j * 2 ^ (s * w) =
        ∑ w ∈ range (2 * ((n + 1) / 2)), gv (L.getD w []) j * 2 ^ (s * w) := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · rw [show 2 * ((n + 1) / 2) = n by omega]
      · rw [show 2 * ((n + 1) / 2) = n + 1 by omega, Finset.sum_range_succ, hz n le_rfl]; ring
    rw [key, sum_range_pairs]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [show s * (2 * v) = 2 * s * v by ring, show s * (2 * v + 1) = s + 2 * s * v by ring, pow_add]
    ring

lemma rowStage_gv (A : List (List SInt)) (n M s : Nat) (xs : List SInt) (j : Nat) (hj : j < M)
    (hA : A.length ≤ 2 ^ 5) :
    gv (rowStage A n M s xs) j = ∑ w ∈ range A.length, (∑ i ∈ range (min (A.getD w []).length n),
      ((A.getD w []).getD i SInt.zero).val * gv xs (i * M + j)) * 2 ^ (s * w) := by
  rw [rowStage, combine_gv 5 s _ j (by simpa using hA), List.length_map]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hw' := Finset.mem_range.1 hw
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hw']
  simp only [Option.map_some, Option.getD_some]
  rw [gv_lincomb, chunks_length]
  congr 1
  refine Finset.sum_congr (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']; rfl) fun i hi => ?_
  rw [gv_chunks M n xs i j (by simp at hi; omega) hj,
    show (A.getD w []) = A[w] by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']; rfl]

lemma finalStage_val (A : List (List SInt)) (xs : List SInt) (w : Nat) (hw : w < A.length) :
    gv (finalStage A xs) w = ∑ i ∈ range (min (A.getD w []).length xs.length),
      ((A.getD w []).getD i SInt.zero).val * (xs.getD i SInt.zero).val := by
  rw [finalStage, gv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hw]
  simp only [Option.map_some, Option.getD_some]
  rw [dotS_val, show (A.getD w []) = A[w] by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw]; rfl]

end NPT.Cert.Ident
