/-
NPT.Cert.Ident.KRLib — recursor-encoded evaluation stages for kernel evaluation.
Raw recursors (List.rec, Nat.rec, Bool.rec, casesOn) instead of structural recursion / `if` / `match`, which cost
3–15× more kernel memory per step.  No lazy counters are threaded through loops.
-/
import NPT.Cert.Ident.Core

open NPT.Cert.Ident

namespace NPT.Cert.KR

/-! ### SInt -/

noncomputable def addS (a b : SInt) : SInt :=
  @SInt.casesOn (fun _ => SInt) a fun an am =>
  @SInt.casesOn (fun _ => SInt) b fun bn bm =>
  @Bool.rec (fun _ => SInt)
    (@Bool.rec (fun _ => SInt) ⟨false, Nat.add am bm⟩
      (@Bool.rec (fun _ => SInt) ⟨true, Nat.sub bm am⟩ ⟨false, Nat.sub am bm⟩ (Nat.ble bm am)) bn)
    (@Bool.rec (fun _ => SInt)
      (@Bool.rec (fun _ => SInt) ⟨true, Nat.sub am bm⟩ ⟨false, Nat.sub bm am⟩ (Nat.ble am bm))
      ⟨true, Nat.add am bm⟩ bn)
    an

noncomputable def mulS (a b : SInt) : SInt :=
  @SInt.casesOn (fun _ => SInt) a fun an am =>
  @SInt.casesOn (fun _ => SInt) b fun bn bm =>
  ⟨@Bool.rec (fun _ => Bool) bn (@Bool.rec (fun _ => Bool) true false bn) an, Nat.mul am bm⟩

noncomputable def ofIntS (z : Int) : SInt :=
  @Int.casesOn (fun _ => SInt) z (fun n => ⟨false, n⟩) (fun n => ⟨true, Nat.succ n⟩)

/-! ### Lists -/

noncomputable def foldrR {α β : Type} (f : α → β → β) (init : β) (l : List α) : β :=
  @List.rec α (fun _ => β) init (fun a _ ih => f a ih) l

noncomputable def mapR {α β : Type} (f : α → β) (l : List α) : List β :=
  @List.rec α (fun _ => List β) [] (fun a _ ih => f a :: ih) l

noncomputable def takeR {α : Type} (n : Nat) (l : List α) : List α :=
  @Nat.rec (fun _ => List α → List α) (fun _ => [])
    (fun _ ih => fun l => @List.casesOn α (fun _ => List α) l [] (fun a l' => a :: ih l')) n l

noncomputable def dropR {α : Type} (n : Nat) (l : List α) : List α :=
  @Nat.rec (fun _ => List α → List α) (fun l => l)
    (fun _ ih => fun l => @List.casesOn α (fun _ => List α) l [] (fun _ l' => ih l')) n l

/-- The first `n` elements of `l`, padded with `d`. -/
noncomputable def takePadR {α : Type} (n : Nat) (d : α) (l : List α) : List α :=
  @Nat.rec (fun _ => List α → List α) (fun _ => [])
    (fun _ ih => fun l => @List.casesOn α (fun _ => List α) l (d :: ih []) (fun a l' => a :: ih l')) n l

noncomputable def zipWithR {α β γ : Type} (f : α → β → γ) (l1 : List α) : List β → List γ :=
  @List.rec α (fun _ => List β → List γ) (fun _ => [])
    (fun a _ ih => fun l2 => @List.casesOn β (fun _ => List γ) l2 [] (fun b l2' => f a b :: ih l2')) l1

noncomputable def findR {α : Type} (pred : α → Bool) (l : List α) : Option α :=
  @List.rec α (fun _ => Option α) none (fun a _ ih => @Bool.rec (fun _ => Option α) ih (some a) (pred a)) l

noncomputable def andR (a b : Bool) : Bool := @Bool.rec (fun _ => Bool) false b a
noncomputable def orR (a b : Bool) : Bool := @Bool.rec (fun _ => Bool) b true a

/-- `k` groups of `m` consecutive elements. -/
noncomputable def grpR {α : Type} (m k : Nat) (l : List α) : List (List α) :=
  @Nat.rec (fun _ => List α → List (List α)) (fun _ => [])
    (fun _ ih => fun l => takeR m l :: ih (dropR m l)) k l

/-- Rows nested by four digits `[μ0][μ1][μ2][μ3]` (mixed radix `d0..d3`, `μ0` most significant). -/
noncomputable def nest4R {α : Type} (d0 d1 d2 d3 : Nat) (rows : List α) : List (List (List (List α))) :=
  mapR (fun g0 => mapR (fun g1 => grpR d3 d2 g1) (grpR (Nat.mul d2 d3) d1 g0)) (grpR (Nat.mul d1 (Nat.mul d2 d3)) d0 rows)

noncomputable def addLR (xs : List SInt) : List SInt → List SInt :=
  @List.rec SInt (fun _ => List SInt → List SInt) (fun ys => ys)
    (fun x xs' ih => fun ys => @List.casesOn SInt (fun _ => List SInt) ys (x :: xs') (fun y ys' => addS x y :: ih ys')) xs

noncomputable def mulLR (c : SInt) (l : List SInt) : List SInt := mapR (mulS c) l

noncomputable def lincombR (cs : List SInt) : List (List SInt) → List SInt :=
  @List.rec SInt (fun _ => List (List SInt) → List SInt) (fun _ => [])
    (fun c _ ih => fun vs => @List.casesOn (List SInt) (fun _ => List SInt) vs [] (fun v vs' => addLR (mulLR c v) (ih vs'))) cs

noncomputable def dotR (u : List SInt) : List SInt → SInt :=
  @List.rec SInt (fun _ => List SInt → SInt) (fun _ => ⟨false, 0⟩)
    (fun a _ ih => fun v => @List.casesOn SInt (fun _ => SInt) v ⟨false, 0⟩ (fun b v' => addS (mulS a b) (ih v'))) u

noncomputable def addRowsR (A : List (List SInt)) : List (List SInt) → List (List SInt) :=
  @List.rec (List SInt) (fun _ => List (List SInt) → List (List SInt)) (fun B => B)
    (fun a A' ih => fun B => @List.casesOn (List SInt) (fun _ => List (List SInt)) B (a :: A')
      (fun b B' => addLR a b :: ih B')) A

/-- `Σ_{x ∈ xs, y ∈ ys} f x y`, emitted onto `acc` (x outer, y inner). -/
noncomputable def pairsR {β γ δ : Type} (f : β → γ → List δ → List δ) (xs : List β) (ys : List γ) (acc : List δ) : List δ :=
  foldrR (fun x accX => foldrR (fun y accY => f x y accY) accX ys) acc xs

/-! ### Item tensors in row form -/

/-- Row `(μ0, ν0)` of an item tensor: entries `(i1, i2, i3)` in order, `i_l = μ_l d_l + ν_l`. -/
noncomputable def rowR (cS : SInt) (wr0 y0 : List (List (List (List SInt)))) : List SInt :=
  pairsR (fun w1 y1 acc1 => pairsR (fun w2 y2 acc2 => pairsR (fun w3 y3 acc3 => mulS cS (dotR w3 y3) :: acc3)
    w2 y2 acc2) w1 y1 acc1) wr0 y0 []

/-- All rows `i0 = μ0 d0 + ν0` of an item tensor. -/
noncomputable def itemRowsR (cS : SInt) (WrN YN : List (List (List (List (List SInt))))) : List (List SInt) :=
  foldrR (fun wr0 acc => foldrR (fun y0 acc' => rowR cS wr0 y0 :: acc') acc YN) [] WrN

/-! ### Packed stages -/

/-- Level 0 with leaf rows: `Σ_{i0} P_{i0} · row_{i0}`. -/
noncomputable def colStageR (P : List SInt) (rows : List (List SInt)) : List SInt := lincombR P rows

noncomputable def shlLR (k : Nat) (l : List SInt) : List SInt :=
  mapR (fun x => @SInt.casesOn (fun _ => SInt) x fun n m => ⟨n, Nat.shiftLeft m k⟩) l

/-- `pairUp` with a pending (even-position) element. -/
noncomputable def pairUpA (s : Nat) (Ls : List (List SInt)) : Option (List SInt) → List (List SInt) :=
  @List.rec (List SInt) (fun _ => Option (List SInt) → List (List SInt))
    (fun pend => @Option.casesOn (List SInt) (fun _ => List (List SInt)) pend [] (fun a => [a]))
    (fun x _ ih => fun pend => @Option.casesOn (List SInt) (fun _ => List (List SInt)) pend (ih (some x))
      (fun a => addLR a (shlLR s x) :: ih none)) Ls

/-- `(L0 + L1 << s), (L2 + L3 << s), …` (a trailing single list is kept). -/
noncomputable def pairUpR (s : Nat) (Ls : List (List SInt)) : List (List SInt) := pairUpA s Ls none

/-- Balanced combination `Σ_w L_w << (s w)` (`length ≤ 2^fuel`). -/
noncomputable def combineR (fuel : Nat) : Nat → List (List SInt) → List SInt :=
  @Nat.rec (fun _ => Nat → List (List SInt) → List SInt)
    (fun _ Ls => @List.casesOn (List SInt) (fun _ => List SInt) Ls [] (fun a _ => a))
    (fun _ ih => fun s Ls => @List.casesOn (List SInt) (fun _ => List SInt) Ls []
      (fun a rest => @List.casesOn (List SInt) (fun _ => List SInt) rest a
        (fun _ _ => ih (Nat.mul 2 s) (pairUpR s Ls)))) fuel

noncomputable def rowStageR (A : List (List SInt)) (n M s : Nat) (xs : List SInt) : List SInt :=
  combineR 5 s (mapR (fun row => lincombR row (grpR M n xs)) A)

noncomputable def finalStageR (A : List (List SInt)) (xs : List SInt) : List SInt :=
  mapR (fun row => dotR row xs) A

/-! ### Digit extraction (fields, no unfield) -/

noncomputable def extLR (b : Nat) : Nat → Nat → Nat → List Nat → List Nat :=
  @Nat.rec (fun _ => Nat → Nat → List Nat → List Nat)
    (fun _ N acc => N :: acc)
    (fun _ ih => fun L N acc =>
      @Bool.rec (fun _ => List Nat)
        (ih (Nat.div L 2) (Nat.land N (Nat.sub (Nat.shiftLeft 1 (Nat.mul b (Nat.div L 2))) 1))
          (ih (Nat.sub L (Nat.div L 2)) (Nat.shiftRight N (Nat.mul b (Nat.div L 2))) acc))
        (N :: acc)
        (Nat.ble L 1))

noncomputable def fieldR (off : Nat) (v : SInt) : Nat :=
  @SInt.casesOn (fun _ => Nat) v fun n m => @Bool.rec (fun _ => Nat) (Nat.add off m) (Nat.sub off m) n

/-- Fields of all digits of the slices, slice by slice. -/
noncomputable def fieldsR (b L off : Nat) (slices : List SInt) : List Nat :=
  foldrR (fun s acc => extLR b 15 L (fieldR off s) acc) [] slices

/-! ### Routing with counts -/

inductive RT where
  | leaf (key s c : Nat) (ok : Bool)
  | node (k : Nat) (l r : RT)

noncomputable def RT.frc (t : RT) (k : RT → RT) : RT :=
  @RT.casesOn (fun _ => RT) t (fun a b c d => k (RT.leaf a b c d)) (fun a l r => k (RT.node a l r))

noncomputable def RT.ins (t : RT) : Nat → Nat → RT :=
  @RT.rec (fun _ => Nat → Nat → RT)
    (fun k s c ok => fun key v => RT.leaf k (Nat.add s v) (Nat.succ c) (@Bool.rec (fun _ => Bool) false (Nat.beq k key) ok))
    (fun k l r ihl ihr => fun key v => @Bool.rec (fun _ => RT)
      (RT.frc (ihr key v) (fun r' => RT.node k l r'))
      (RT.frc (ihl key v) (fun l' => RT.node k l' r)) (Nat.blt key k))
    t

noncomputable def routeR (vs : List Nat) : List Nat → RT → RT :=
  @List.rec Nat (fun _ => List Nat → RT → RT) (fun _ t => t)
    (fun v _ ih => fun cs t => @List.casesOn Nat (fun _ => RT) cs t (fun c cs' => RT.frc (RT.ins t c v) (ih cs'))) vs

def toRT : AT → RT
  | .leaf k _ _ => .leaf k 0 0 true
  | .node k l r => .node k (toRT l) (toRT r)

/-- Every leaf: key matched, and `Σ fields ≡ count · h (mod p)`. -/
noncomputable def RT.okMod (p h : Nat) (t : RT) : Bool :=
  @RT.rec (fun _ => Bool)
    (fun _ s c ok => @Bool.rec (fun _ => Bool) false (Nat.beq (Nat.mod s p) (Nat.mod (Nat.mul c h) p)) ok)
    (fun _ _ _ a b => @Bool.rec (fun _ => Bool) false b a) t

end NPT.Cert.KR
