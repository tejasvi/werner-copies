/-
NPT.Cert.Ident.Check — the computable identity checker for EP_3 certificates in `NPT.Cert.Sem` form.

A *chunk* is a list of box trees whose packed word vectors are summed, digit-extracted and accumulated by class.
Box tree levels follow the contraction order: leaves (leg 0) → `Nd1` (leg 1) → `Nd2` (leg 2) → `Nd3` (leg 3 = aux).
A leaf holds certificate items `(t, r, s)` with the same modules; the leaf tensor is
`T[(μ0ν0),(μ1ν1),(μ2ν2),(μ3ν3)] = c · Σ_items (W_r · Zq_t · W_sᵀ)[flat μ, flat ν]`, `Zq = 2 Lden · Z`.
Local rows of a module under rule `i`: `A[p][μ·dim+ν] = Σ_x J[x∘α][μ] J[x∘β][ν]`, `(α, β) = (aSel, bSel) (cut i) (fq i p)`.
-/
import NPT.Cert.Ident.Core
import NPT.Cert.Sem
import NPT.Cert.RuleData

namespace NPT.Cert.Ident

open NPT.Cert.Sem NPT.Brauer NPT.Cert

/-! ### Local rows -/

/-- All digit strings `[d0, d1, d2, d3]` (base `n`) in lexicographic order (= flat index order). -/
def allDig (n : Nat) : List (List Nat) :=
  (List.range n).flatMap fun a => (List.range n).flatMap fun b => (List.range n).flatMap fun c =>
    (List.range n).map fun d => [a, b, c, d]

/-- Module rows nested by digits: `J4[d0][d1][d2][d3] = J[flat d]`. -/
def nestJ (n : Nat) (J : List (List Int)) : List (List (List (List (List Int)))) :=
  (List.range n).map fun a => (List.range n).map fun b => (List.range n).map fun c =>
    (List.range n).map fun d => J.getD (((a * n + b) * n + c) * n + d) []

/-- Row `J[x ∘ α]` from the nested table (`xs` = digits of `x`, `α` = 4 slots). -/
def jsel (J4 : List (List (List (List (List Int))))) (α xs : List Nat) : List Int :=
  (((J4.getD (xs.getD (α.getD 0 0) 0) []).getD (xs.getD (α.getD 1 0) 0) []).getD
    (xs.getD (α.getD 2 0) 0) []).getD (xs.getD (α.getD 3 0) 0) []

/-- Integer dot product. -/
def dotI : List Int → List Int → Int
  | a :: as, b :: bs => a * b + dotI as bs
  | _, _ => 0

/-- `aSel cut q` and `bSel cut q` as lists. -/
def aSelL (cut : Nat) (q : Fin 24) : List Nat := (List.finRange 4).map fun s => (aSel cut q s).val
def bSelL (cut : Nat) (q : Fin 24) : List Nat := (List.finRange 4).map fun s => (bSel cut q s).val

/-- A row is zero. -/
def zrow : List Int → Bool
  | [] => true
  | a :: as => a == 0 && zrow as

/-- Outer product of integer rows as signed values, row-major. -/
def outerI (u v : List Int) : List SInt := u.flatMap fun a => v.map fun b => SInt.ofInt (a * b)

/-- Local block map for one permutation: `K[μ][ν] = Σ_x J[x∘α][μ] J[x∘β][ν]` (row-major `μ·dim + ν`); terms with a
zero row are skipped. -/
def localMap (n : Nat) (J4 : List (List (List (List (List Int))))) (α β : List Nat) : List SInt :=
  (allDig n).foldr (fun xs acc =>
    let ra := jsel J4 α xs
    let rb := jsel J4 β xs
    if zrow ra || zrow rb then acc else addL (outerI ra rb) acc) []

/-- Local rows of module `md` under rule `i` (24 rows). -/
def localRows (md : ModD) (i : Nat) : List (List SInt) :=
  let J4 := nestJ md.n md.J
  (List.finRange 24).map fun p => localMap md.n J4 (aSelL (rcut i) (rfq i p)) (bSelL (rcut i) (rfq i p))

/-! ### Leaf tensors -/

/-- Integer row as signed values. -/
def sRow (r : List Int) : List SInt := r.map SInt.ofInt


/-- Exact multiplier entry times `zmul`/`2` scaling: `Zq[a][c] = zget·zmul + 2·num` (num from `uent`, as `uval`). -/
def zqEntry (b : PBlock) (zmul : Nat) (a c : Nat) : SInt :=
  let z := (SInt.ofInt (b.zget a c)).mul ⟨false, zmul⟩
  match b.ufind a c with
  | some e => z.add (SInt.ofInt (2 * e.2.2))
  | none => z

/-- Rows of `coef · Zq` (`R × R`). -/
def zqRows (b : PBlock) (zmul : Nat) (coef : SInt) : List (List SInt) :=
  (List.range b.n).map fun a => (List.range b.n).map fun c => coef.mul (zqEntry b zmul a c)

/-- `Σ_c x_c · w_c` with `w` integers. -/
def dotSI : List SInt → List Int → SInt
  | x :: xs, w :: ws => ((SInt.ofInt w).mul x).add (dotSI xs ws)
  | _, _ => SInt.zero

/-- `Σ_c x_c · y_c`. -/
def dotSS : List SInt → List SInt → SInt
  | x :: xs, y :: ys => (x.mul y).add (dotSS xs ys)
  | _, _ => SInt.zero

/-- `Σ_c x_c · w_c`, skipping zero `w_c` (integers). -/
def dotSZ : List SInt → List Int → SInt
  | x :: xs, w :: ws => if w == 0 then dotSZ xs ws else ((SInt.ofInt w).mul x).add (dotSZ xs ws)
  | _, _ => SInt.zero

/-- Split a list into consecutive chunks of length `M` (as many as needed). -/
def chunkAll (M : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | fuel + 1, xs => if xs.isEmpty then [] else xs.take M :: chunkAll M fuel (xs.drop M)

/-- Nest a list of `d0 d1 d2 d3` rows as `[μ0][μ1][μ2][μ3]`. -/
def nest4 (ds : List Nat) (rows : List α) : List (List (List (List α))) :=
  let d1 := ds.getD 1 1; let d2 := ds.getD 2 1; let d3 := ds.getD 3 1
  (chunkAll (d1 * d2 * d3) (rows.length + 1) rows).map fun a =>
    (chunkAll (d2 * d3) (a.length + 1) a).map fun b => chunkAll d3 (b.length + 1) b

/-- The leaf tensor of one item, flat over `(μ0ν0, μ1ν1, μ2ν2, μ3ν3)`, with `Zq` scaled by `coef`. -/
def itemT (C : CertD) (zmul : Nat) (coef : SInt) (ds : List Nat) (it : Nat × Nat × Nat) : List SInt :=
  let t := C.types.getD it.1 default
  let b := C.Z.getD t.zi default
  let nn := ds.foldl (· * ·) 1
  let Zr := zqRows b zmul coef
  let Wr := (List.range nn).map fun x => let w := t.W.getD (it.2.1 * nn + x) []; (zrow w, w)
  let Ys := (List.range nn).map fun y => let w := t.W.getD (it.2.2 * nn + y) [];
    (zrow w, if zrow w then [] else Zr.map fun zr => dotSZ zr w)
  let W4 := nest4 ds Wr
  let Y4 := nest4 ds Ys
  W4.flatMap fun a0 => Y4.flatMap fun b0 => a0.flatMap fun a1 => b0.flatMap fun b1 =>
    a1.flatMap fun a2 => b1.flatMap fun b2 => a2.flatMap fun a3 => b2.map fun b3 =>
      if a3.1 || b3.1 then SInt.zero else dotSZ b3.2 a3.2

/-! ### Box trees -/

structure Leaf where
  m0 : Nat
  items : List (Nat × Nat × Nat)
  deriving Inhabited

structure Nd1 where
  m1 : Nat
  kids : List Leaf
  deriving Inhabited

structure Nd2 where
  m2 : Nat
  kids : List Nd1
  deriving Inhabited

structure Nd3 where
  m3 : Nat
  kids : List Nd2
  deriving Inhabited

/-- A rule group: rule index (into `ruleTab`), family, tree. -/
structure Grp where
  rule : Nat
  fam : Nat
  tree : List Nd3
  deriving Inhabited

/-- Evaluation context: the certificate, `b` (digit width), `zmul`, leaf coefficient. -/
structure Ctx where
  C : CertD
  b : Nat
  zmul : Nat
  coef : SInt

def mdim (C : CertD) (m : Nat) : Nat := (C.mods.getD m default).dim

/-- The leaf tensor of a rule-group leaf: `Σ_items` of the item tensors. -/
def leafT (X : Ctx) (m1 m2 m3 : Nat) (lf : Leaf) : List SInt :=
  (lf.items.map (itemT X.C X.zmul X.coef [mdim X.C lf.m0, mdim X.C m1, mdim X.C m2, mdim X.C m3])).foldr addL []

/-- What a box tree needs: per node index, 24 local rows and their length; the leaf tensors. -/
structure Spec where
  rows : Nat → List (List SInt)
  dimsq : Nat → Nat
  leaf : Nat → Nat → Nat → Leaf → List SInt

/-- Leaf: leg 0 contracted, packed over `w0` (stride `b`); result has `n1 n2 n3` entries. -/
def evalLeaf (S : Spec) (b m1 m2 m3 : Nat) (lf : Leaf) : List SInt :=
  colStage (packCols b (S.dimsq lf.m0) (S.rows lf.m0)) (S.dimsq m1 * S.dimsq m2 * S.dimsq m3) (S.leaf m1 m2 m3 lf)

def evalNd1 (S : Spec) (b m2 m3 : Nat) (nd : Nd1) : List SInt :=
  rowStage (S.rows nd.m1) (S.dimsq nd.m1) (S.dimsq m2 * S.dimsq m3) (24 * b)
    ((nd.kids.map (evalLeaf S b nd.m1 m2 m3)).foldr addL [])

def evalNd2 (S : Spec) (b m3 : Nat) (nd : Nd2) : List SInt :=
  rowStage (S.rows nd.m2) (S.dimsq nd.m2) (S.dimsq m3) (576 * b) ((nd.kids.map (evalNd1 S b nd.m2 m3)).foldr addL [])

def evalNd3 (S : Spec) (b : Nat) (nd : Nd3) : List SInt :=
  finalStage (S.rows nd.m3) ((nd.kids.map (evalNd2 S b nd.m3)).foldr addL [])

/-- The 24 slices (by `w3`) of a box tree, each packed over `(w0, w1, w2)`. -/
def evalTree (S : Spec) (b : Nat) (tree : List Nd3) : List SInt := (tree.map (evalNd3 S b)).foldr addL []

/-- The spec of a rule group (rule `i`). -/
def ruleSpec (X : Ctx) (i : Nat) : Spec where
  rows m := localRows (X.C.mods.getD m default) i
  dimsq m := mdim X.C m * mdim X.C m
  leaf m1 m2 m3 lf := leafT X m1 m2 m3 lf

/-- The 24 slices of a rule group. -/
def evalGrp (X : Ctx) (G : Grp) : List SInt := evalTree (ruleSpec X G.rule) X.b G.tree

/-! ### A-priori bounds -/

/-- Largest absolute row sum of a row table. -/
def rowAbs (A : List (List SInt)) : Nat := (A.map fun row => (row.map SInt.mag).sum).foldr max 0

/-- Largest absolute entry. -/
def maxAbs (T : List SInt) : Nat := (T.map SInt.mag).foldr max 0

def boundLeaf (S : Spec) (m1 m2 m3 : Nat) (lf : Leaf) : Nat := rowAbs (S.rows lf.m0) * maxAbs (S.leaf m1 m2 m3 lf)
def boundNd1 (S : Spec) (m2 m3 : Nat) (nd : Nd1) : Nat :=
  rowAbs (S.rows nd.m1) * (nd.kids.map (boundLeaf S nd.m1 m2 m3)).sum
def boundNd2 (S : Spec) (m3 : Nat) (nd : Nd2) : Nat := rowAbs (S.rows nd.m2) * (nd.kids.map (boundNd1 S nd.m2 m3)).sum
def boundNd3 (S : Spec) (nd : Nd3) : Nat := rowAbs (S.rows nd.m3) * (nd.kids.map (boundNd2 S nd.m3)).sum
/-- A-priori bound on the absolute value of a box tree's word values. -/
def boundTree (S : Spec) (tree : List Nd3) : Nat := (tree.map (boundNd3 S)).sum

/-! ### Chunk check -/

/-- Number of digits per slice. -/
def slen : Nat := 13824

/-- All digit values of the 24 slices, in the order `(w3, w2, w1, w0)`. -/
def digitsOf (b : Nat) (slices : List SInt) : List SInt :=
  (List.range 24).flatMap fun w3 =>
    (extL b 15 slen (fieldNat (offL b slen) (slices.getD w3 SInt.zero)) []).map (unfield (1 <<< (b - 1)))

/-- A part of a family: a box tree with its spec. -/
structure Part where
  S : Spec
  tree : List Nd3

/-- The summed slices of the parts. -/
def partsSlices (b : Nat) (ps : List Part) : List SInt := (ps.map fun P => evalTree P.S b P.tree).foldr addL []

/-- The summed a-priori bounds of the parts. -/
def partsBound (ps : List Part) : Nat := (ps.map fun P => boundTree P.S P.tree).sum

/-- **The family check.** The digit width suffices, and routing the digits of the summed slices by `cls` sets every
leaf flag and leaves every leaf sum zero. -/
def famCheck (b : Nat) (ps : List Part) (cls : List Nat) (t0 : AT) : Bool :=
  decide (0 < b) && decide (partsBound ps < 2 ^ (b - 1)) && (cls.length == 24 * slen) &&
    t0.leaves.all (fun e => e.2.1.mag == 0) &&
    (routeL (digitsOf b (partsSlices b ps)) cls t0).leaves.all (fun e => e.2.2 && e.2.1.mag == 0)

end NPT.Cert.Ident
