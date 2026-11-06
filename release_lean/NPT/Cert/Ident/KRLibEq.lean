/-
NPT.Cert.Ident.KRLibEq — the recursor-encoded stages of `KRLib` equal the checked definitions.
-/
import NPT.Cert.Ident.KRLib

open NPT.Cert.Ident

namespace NPT.Cert.KR

theorem ble_true {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := Nat.ble_eq_true_of_le h

theorem ble_false {a b : Nat} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases hb : Nat.ble a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hb) h

theorem addS_eq (a b : SInt) : addS a b = a.add b := by
  rcases a with ⟨an, am⟩
  rcases b with ⟨bn, bm⟩
  cases an <;> cases bn
  · rfl
  · show @Bool.rec (fun _ => SInt) ⟨true, Nat.sub bm am⟩ ⟨false, Nat.sub am bm⟩ (Nat.ble bm am) =
      if bm ≤ am then ⟨false, am - bm⟩ else ⟨true, bm - am⟩
    by_cases h : bm ≤ am
    · rw [ble_true h, ite_eq_left h]; rfl
    · rw [ble_false h, ite_eq_right h]; rfl
  · show @Bool.rec (fun _ => SInt) ⟨true, Nat.sub am bm⟩ ⟨false, Nat.sub bm am⟩ (Nat.ble am bm) =
      if am ≤ bm then ⟨false, bm - am⟩ else ⟨true, am - bm⟩
    by_cases h : am ≤ bm
    · rw [ble_true h, ite_eq_left h]; rfl
    · rw [ble_false h, ite_eq_right h]; rfl
  · rfl

theorem mulS_eq (a b : SInt) : mulS a b = a.mul b := by
  rcases a with ⟨an, am⟩
  rcases b with ⟨bn, bm⟩
  cases an <;> cases bn <;> rfl

theorem ofIntS_eq (z : Int) : ofIntS z = SInt.ofInt z := by
  cases z <;> rfl

theorem foldrR_eq {α β : Type} (f : α → β → β) (init : β) (l : List α) : foldrR f init l = l.foldr f init := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [foldrR, List.foldr_cons] at ih ⊢; rw [← ih]

theorem mapR_eq {α β : Type} (f : α → β) (l : List α) : mapR f l = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [mapR, List.map_cons] at ih ⊢; rw [← ih]

theorem takeR_eq {α : Type} (n : Nat) (l : List α) : takeR n l = l.take n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons a l => simp only [takeR, List.take_succ_cons] at ih ⊢; rw [← ih]

theorem dropR_eq {α : Type} (n : Nat) (l : List α) : dropR n l = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons a l => simp only [dropR, List.drop_succ_cons] at ih ⊢; rw [← ih]

theorem grpR_eq (m k : Nat) (l : List SInt) : grpR m k l = chunks m k l := by
  induction k generalizing l with
  | zero => rfl
  | succ k ih =>
    simp only [grpR, chunks] at ih ⊢
    rw [← ih, ← takeR_eq, ← dropR_eq]

theorem addLR_eq (xs ys : List SInt) : addLR xs ys = addL xs ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys => simp only [addLR, addL] at ih ⊢; rw [← ih, addS_eq]

theorem mulLR_eq (c : SInt) (l : List SInt) : mulLR c l = mulL c l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [mulLR, mapR, mulL] at ih ⊢; rw [← ih, mulS_eq]

theorem lincombR_eq (cs : List SInt) (vs : List (List SInt)) : lincombR cs vs = lincomb cs vs := by
  induction cs generalizing vs with
  | nil => cases vs <;> rfl
  | cons c cs ih =>
    cases vs with
    | nil => rfl
    | cons v vs => simp only [lincombR, lincomb] at ih ⊢; rw [← ih, ← mulLR_eq, ← addLR_eq]

theorem dotR_eq (u v : List SInt) : dotR u v = dotS u v := by
  induction u generalizing v with
  | nil => cases v <;> rfl
  | cons a u ih =>
    cases v with
    | nil => rfl
    | cons b v => simp only [dotR, dotS] at ih ⊢; rw [← ih, mulS_eq, addS_eq]

theorem shlLR_eq (k : Nat) (l : List SInt) : shlLR k l = shlL k l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [shlLR, mapR, shlL] at ih ⊢
    rw [← ih]
    rcases a with ⟨n, m⟩
    rfl

theorem pairUpA_eq (s : Nat) : ∀ (Ls : List (List SInt)),
    pairUpA s Ls none = pairUp s Ls ∧ ∀ a, pairUpA s Ls (some a) = pairUp s (a :: Ls)
  | [] => ⟨rfl, fun _ => rfl⟩
  | x :: Ls => by
    obtain ⟨h1, h2⟩ := pairUpA_eq s Ls
    refine ⟨?_, fun a => ?_⟩
    · show pairUpA s Ls (some x) = pairUp s (x :: Ls)
      exact h2 x
    · show addLR a (shlLR s x) :: pairUpA s Ls none = pairUp s (a :: x :: Ls)
      rw [h1, addLR_eq, shlLR_eq]
      rfl

theorem pairUpR_eq (s : Nat) (Ls : List (List SInt)) : pairUpR s Ls = pairUp s Ls :=
  (pairUpA_eq s Ls).1

theorem combineR_eq (fuel s : Nat) (Ls : List (List SInt)) : combineR fuel s Ls = combine fuel s Ls := by
  induction fuel generalizing s Ls with
  | zero => cases Ls <;> rfl
  | succ fuel ih =>
    rcases Ls with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rfl
    · rfl
    · show combineR fuel (Nat.mul 2 s) (pairUpR s (a :: b :: rest)) = combine fuel (2 * s) (pairUp s (a :: b :: rest))
      rw [ih, pairUpR_eq]
      rfl

theorem rowStageR_eq (A : List (List SInt)) (n M s : Nat) (xs : List SInt) :
    rowStageR A n M s xs = rowStage A n M s xs := by
  unfold rowStageR rowStage
  rw [combineR_eq, mapR_eq, grpR_eq]
  congr 1
  exact List.map_congr_left fun row _ => lincombR_eq _ _

theorem finalStageR_eq (A : List (List SInt)) (xs : List SInt) : finalStageR A xs = finalStage A xs := by
  unfold finalStageR finalStage
  rw [mapR_eq]
  exact List.map_congr_left fun row _ => dotR_eq _ _

theorem extLR_eq (b fuel L N : Nat) (acc : List Nat) : extLR b fuel L N acc = extL b fuel L N acc := by
  induction fuel generalizing L N acc with
  | zero => rfl
  | succ fuel ih =>
    simp only [extLR, extL] at ih ⊢
    by_cases h : L ≤ 1
    · rw [ble_true h, ite_eq_left h]
    · rw [ble_false h, ite_eq_right h, ih, ih]
      rfl

theorem fieldR_eq (off : Nat) (v : SInt) : fieldR off v = fieldNat off v := by
  rcases v with ⟨n, m⟩
  cases n <;> rfl

theorem colStageR_eq (P : List SInt) (M : Nat) (xs : List SInt) :
    colStageR P (grpR M P.length xs) = colStage P M xs := by
  unfold colStageR colStage
  rw [lincombR_eq, grpR_eq]

end NPT.Cert.KR
