/-
NPT.Cert.Ident.KROffs — the leaf offsets of a split mod-`p` check sum to `0 mod p`.
`offsZero p Ls` adds the offset lists `Ls` pointwise and tests every entry mod `p` (kernel-cheap, one pass);
`offsZero_sound` turns it into the `hoff` hypothesis of `hsum_of_checks_split`.
-/
namespace NPT.Cert.KR

/-- Pointwise sum of two lists (the longer tail is kept). -/
def addN : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: addN xs ys

/-- Pointwise sum of a list of lists. -/
def sumN (Ls : List (List Nat)) : List Nat := Ls.foldr addN []

/-- Every entry of the pointwise sum is `0 mod p`. -/
def offsZero (p : Nat) (Ls : List (List Nat)) : Bool := (sumN Ls).all fun x => x % p == 0

theorem addN_getD : ∀ (xs ys : List Nat) (j : Nat), (addN xs ys).getD j 0 = xs.getD j 0 + ys.getD j 0
  | [], ys, j => by
    show ys.getD j 0 = ([] : List Nat).getD j 0 + ys.getD j 0
    rw [List.getD_nil, Nat.zero_add]
  | x :: xs, [], j => by
    show (x :: xs).getD j 0 = (x :: xs).getD j 0 + ([] : List Nat).getD j 0
    rw [List.getD_nil, Nat.add_zero]
  | x :: xs, y :: ys, 0 => by
    show ((x + y) :: addN xs ys).getD 0 0 = (x :: xs).getD 0 0 + (y :: ys).getD 0 0
    rw [List.getD_cons_zero, List.getD_cons_zero, List.getD_cons_zero]
  | x :: xs, y :: ys, j + 1 => by
    show ((x + y) :: addN xs ys).getD (j + 1) 0 = (x :: xs).getD (j + 1) 0 + (y :: ys).getD (j + 1) 0
    rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, addN_getD xs ys j]

theorem sumN_getD (j : Nat) : ∀ (Ls : List (List Nat)), (sumN Ls).getD j 0 = (Ls.map fun o => o.getD j 0).sum
  | [] => by simp [sumN]
  | L :: Ls => by
    show (addN L (sumN Ls)).getD j 0 = _
    rw [addN_getD, sumN_getD j Ls, List.map_cons, List.sum_cons]

/-- **Offsets sum to `0 mod p`**, at every position. -/
theorem offsZero_sound (p : Nat) (Ls : List (List Nat)) (h : offsZero p Ls = true) :
    ∀ j, (Ls.map fun o => o.getD j 0).sum % p = 0 := by
  intro j
  rw [← sumN_getD]
  rcases Nat.lt_or_ge j (sumN Ls).length with hj | hj
  · have hall := List.all_eq_true.1 h ((sumN Ls).getD j 0)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj)
    exact beq_iff_eq.1 hall
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]
    rfl

end NPT.Cert.KR
