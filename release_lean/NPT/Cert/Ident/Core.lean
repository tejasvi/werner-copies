/-
NPT.Cert.Ident.Core — kernel-efficient arithmetic for the EP_3 identity check.

Packed (Kronecker) evaluation: a vector `v` over words is stored as integers whose base-`2^b` digits are the
entries (`Σ_p v_p 2^(b p)`), so one big-number operation processes many entries. Signed values use the
sign-magnitude type `SInt` (all big-number work on `Nat`, which the kernel evaluates with GMP).

Pieces (all structural recursion on lists, for `decide +kernel`):
* `SInt` with `add`, `mul`, `shl`;
* list operations `addL`, `mulL`, `shlL`, `lincomb`, `chunks`;
* contraction stages `colStage` (packed columns times scalars), `rowStage` (row combinations, then a balanced
  shift-combination `combine`), `finalStage` (24 slices);
* digit extraction `extL` (binary splitting of `OFF + N`, offset `2^(b-1)` per digit);
* class accumulation in a binary search tree `AT` keyed by class representatives.
-/
namespace NPT.Cert.Ident

/-- Sign-magnitude integer: value `±mag`. -/
structure SInt where
  neg : Bool
  mag : Nat
  deriving Inhabited, Repr

namespace SInt

/-- The value. -/
def val (a : SInt) : Int := if a.neg then -(a.mag : Int) else (a.mag : Int)

def zero : SInt := ⟨false, 0⟩

def ofInt : Int → SInt
  | .ofNat m => ⟨false, m⟩
  | .negSucc m => ⟨true, m + 1⟩

def add (a b : SInt) : SInt :=
  match a.neg, b.neg with
  | false, false => ⟨false, a.mag + b.mag⟩
  | true, true => ⟨true, a.mag + b.mag⟩
  | false, true => if b.mag ≤ a.mag then ⟨false, a.mag - b.mag⟩ else ⟨true, b.mag - a.mag⟩
  | true, false => if a.mag ≤ b.mag then ⟨false, b.mag - a.mag⟩ else ⟨true, a.mag - b.mag⟩

def mul (a b : SInt) : SInt := ⟨a.neg != b.neg, a.mag * b.mag⟩

def shl (a : SInt) (k : Nat) : SInt := ⟨a.neg, a.mag <<< k⟩

def neg' (a : SInt) : SInt := ⟨!a.neg, a.mag⟩

end SInt

/-! ### Lists of signed values -/

/-- Entrywise sum (the longer tail is kept). -/
def addL : List SInt → List SInt → List SInt
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => x.add y :: addL xs ys

/-- Scalar multiple. -/
def mulL (c : SInt) : List SInt → List SInt
  | [] => []
  | x :: xs => c.mul x :: mulL c xs

/-- Shift every entry by `k` bits. -/
def shlL (k : Nat) : List SInt → List SInt
  | [] => []
  | x :: xs => x.shl k :: shlL k xs

/-- `Σ_i c_i · v_i` (entrywise). -/
def lincomb : List SInt → List (List SInt) → List SInt
  | c :: cs, v :: vs => addL (mulL c v) (lincomb cs vs)
  | _, _ => []

/-- Dot product. -/
def dotS : List SInt → List SInt → SInt
  | c :: cs, v :: vs => (c.mul v).add (dotS cs vs)
  | _, _ => SInt.zero

/-- `n` consecutive chunks of length `M`. -/
def chunks (M : Nat) : Nat → List SInt → List (List SInt)
  | 0, _ => []
  | n + 1, xs => xs.take M :: chunks M n (xs.drop M)

/-! ### Contraction stages -/

/-- Horner packing `Σ_w a_w 2^(s w)` of a list of scalars. -/
def packH (s : Nat) : List SInt → SInt
  | [] => SInt.zero
  | a :: as => a.add ((packH s as).shl s)

/-- Column `i` of a row table (24 rows), as a list over rows. -/
def colOf (A : List (List SInt)) (i : Nat) : List SInt := A.map fun row => row.getD i SInt.zero

/-- Packed columns `P_i = Σ_w A[w][i] 2^(b w)`, `i < n`. -/
def packCols (b n : Nat) (A : List (List SInt)) : List SInt :=
  (List.range n).map fun i => packH b (colOf A i)

/-- Stage on scalars: `out[j] = Σ_i P_i · xs[i M + j]` (`xs` has `n` chunks of length `M`). -/
def colStage (P : List SInt) (M : Nat) (xs : List SInt) : List SInt :=
  lincomb P (chunks M P.length xs)

/-- One level of balanced combination: `(L0 + L1 << s), (L2 + L3 << s), …`. -/
def pairUp (s : Nat) : List (List SInt) → List (List SInt)
  | a :: b :: rest => addL a (shlL s b) :: pairUp s rest
  | rest => rest

/-- Balanced combination `Σ_w L_w << (s w)` (needs `length ≤ 2^fuel`). -/
def combine : Nat → Nat → List (List SInt) → List SInt
  | 0, _, Ls => Ls.headD []
  | fuel + 1, s, Ls =>
    match Ls with
    | [] => []
    | [a] => a
    | a :: b :: rest => combine fuel (2 * s) (pairUp s (a :: b :: rest))

/-- Stage on packed entries: `out[j] = Σ_w 2^(s w) Σ_i A[w][i] xs[i M + j]`. -/
def rowStage (A : List (List SInt)) (n M s : Nat) (xs : List SInt) : List SInt :=
  let cs := chunks M n xs
  combine 5 s (A.map fun row => lincomb row cs)

/-- Final stage: 24 slices `Σ_i A[w][i] xs[i]`. -/
def finalStage (A : List (List SInt)) (xs : List SInt) : List SInt :=
  A.map fun row => dotS row xs

/-! ### Digit extraction -/

/-- The digits of `N` in base `2^b` (exactly `L` digits; `N < 2^(b L)`), appended to `acc`, by binary splitting. -/
def extL (b : Nat) : Nat → Nat → Nat → List Nat → List Nat
  | 0, _, N, acc => N :: acc
  | fuel + 1, L, N, acc =>
    if L ≤ 1 then N :: acc else
      extL b fuel (L / 2) (N &&& ((1 <<< (b * (L / 2))) - 1))
        (extL b fuel (L - L / 2) (N >>> (b * (L / 2))) acc)

/-- Offset `Σ_{p < L} h 2^(b p)` with `h = 2^(b-1)`. -/
def offL (b L : Nat) : Nat := (1 <<< (b - 1)) * (((1 <<< (b * L)) - 1) / ((1 <<< b) - 1))

/-- The offset field `OFF + v` of a packed slice. -/
def fieldNat (off : Nat) (v : SInt) : Nat := if v.neg then off - v.mag else off + v.mag

/-- A field back to a signed value: `f - h`. -/
def unfield (h f : Nat) : SInt := if h ≤ f then ⟨false, f - h⟩ else ⟨true, h - f⟩

/-! ### Class accumulation -/

/-- Accumulation tree: leaves carry `(key, sum, ok)`; nodes route keys `< k` left. -/
inductive AT where
  | leaf (key : Nat) (s : SInt) (ok : Bool)
  | node (k : Nat) (l r : AT)
  deriving Inhabited

/-- `node k l r`, forcing the head of `l` (so that updates are evaluated eagerly by the kernel). -/
def AT.nodeL (k : Nat) (l r : AT) : AT :=
  match l with
  | .leaf a b c => .node k (.leaf a b c) r
  | .node a b c => .node k (.node a b c) r

/-- `node k l r`, forcing the head of `r`. -/
def AT.nodeR (k : Nat) (l r : AT) : AT :=
  match r with
  | .leaf a b c => .node k l (.leaf a b c)
  | .node a b c => .node k l (.node a b c)

/-- Add `v` to the leaf reached by `key`; the leaf's flag records that its key matched. -/
def AT.add (key : Nat) (v : SInt) : AT → AT
  | .leaf k s ok => .leaf k (s.add v) (ok && k == key)
  | .node k l r => if key < k then AT.nodeL k (l.add key v) r else AT.nodeR k l (r.add key v)

/-- Leaves in order. -/
def AT.leaves : AT → List (Nat × SInt × Bool)
  | .leaf k s ok => [(k, s, ok)]
  | .node _ l r => l.leaves ++ r.leaves

/-- Route values to their classes. -/
def routeL : List SInt → List Nat → AT → AT
  | v :: vs, c :: cs, t => routeL vs cs (t.add c v)
  | _, _, t => t

end NPT.Cert.Ident
