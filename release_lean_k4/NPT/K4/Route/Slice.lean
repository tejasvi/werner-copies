/-
NPTK4.Route.Slice — the k = 4 word values on one aux-leg slice, evaluated by the EP_3 4-leg pipeline (native route).

For a fixed letter `w4` of the auxiliary leg 4, the item tensor `T[i0,i1,i2,i3,i4]` (`i_l = μ_l·d_l + ν_l`) of an item
`(t, r, s)` is contracted at leg 4 with the local row `A₄(w4)` of the item's leg-4 module:
`T'[i0,i1,i2,i3] = Σ_{i4} A₄(w4)[i4] · T[i0,i1,i2,i3,i4]`, with `T = coef · W_r · Zs_t · W_sᵀ` (`Z_t = Zs_t / 2^E`).
A rule group (`GrpF`: family, entry rule, tree m3 → m2 → m1 → m0 → items) is then an EP_3 box tree over legs 0..3
(each item's leg-4 module is that of its type), and `evalTree` packs the 24^4 word values of the slice: slice `w3`,
digit `w0 + 24 w1 + 576 w2` — the position order `(w3, w2, w1, w0)` of the class lists.
-/
import NPT.Cert.Ident.Fast

namespace NPT.K4.Route

open BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident

/-! ### Item tensors contracted at leg 4 -/

/-- `Y[v][a] = Σ_c Zs[a][c] · W[s·nn + v][c]` (`v < nn`, `a < R`). -/
def itemY5 (C : CertD) (nn : ℕ) (it : ℕ × ℕ × ℕ) : List (List Int) :=
  let t := C.types.getD it.1 default
  let b := C.Z.getD t.zi default
  (List.range nn).map fun v => let w := t.W.getD (it.2.2 * nn + v) []
    (List.range b.n).map fun a => ∑ c ∈ range b.n, b.zget a c * w.getD c 0

/-- `Yw[μ4][ν'][a] = Σ_{ν4} A₄[μ4·d4 + ν4] · Y[ν'·d4 + ν4][a]` (`ν'` flat over legs 0..3). -/
def itemYw (d4 n' R : ℕ) (A4 : List Int) (Y : List (List Int)) : List (List (List Int)) :=
  (List.range d4).map fun μ4 => (List.range n').map fun ν' => (List.range R).map fun a =>
    ∑ ν4 ∈ range d4, A4.getD (μ4 * d4 + ν4) 0 * (Y.getD (ν' * d4 + ν4) []).getD a 0

/-- The leg-4-contracted tensor of one item, flat over `(i0, i1, i2, i3)` (`i_l < d_l²`):
entry `coef · Σ_{μ4} ⟨W[r·nn + (flat μ')·d4 + μ4], Yw[μ4][flat ν']⟩`. -/
def itemTF5c (C : CertD) (coef : Int) (d0 d1 d2 d3 d4 : ℕ) (A4 : List Int) (it : ℕ × ℕ × ℕ) : List SInt :=
  let t := C.types.getD it.1 default
  let b := C.Z.getD t.zi default
  let n' := d0 * d1 * d2 * d3
  let nn := n' * d4
  let Yw := itemYw d4 n' b.n A4 (itemY5 C nn it)
  let Wr := (List.range nn).map fun x => t.W.getD (it.2.1 * nn + x) []
  (List.range (d0 * d0)).flatMap fun i0 => (List.range (d1 * d1)).flatMap fun i1 =>
    (List.range (d2 * d2)).flatMap fun i2 => (List.range (d3 * d3)).map fun i3 =>
      let μ' := mr4 d0 d1 d2 d3 (i0 / d0) (i1 / d1) (i2 / d2) (i3 / d3)
      let ν' := mr4 d0 d1 d2 d3 (i0 % d0) (i1 % d1) (i2 % d2) (i3 % d3)
      SInt.ofInt (coef * ∑ μ4 ∈ range d4, dotI (Wr.getD (μ' * d4 + μ4) []) ((Yw.getD μ4 []).getD ν' []))

/-! ### Rule-group specs on a slice -/

/-- Local-row tables of the modules a group uses (`module ↦ 24 rows` under the group's rule). -/
def rowTab (C : CertD) (kpos lpos : List ℕ) (ms : List ℕ) : List (ℕ × List (List SInt)) :=
  ms.map fun m => (m, localRowsF (C.mods.getD m default) kpos lpos)

/-- Table lookup, computing the rows of a module missing from the table. -/
def lookTab (C : CertD) (kpos lpos : List ℕ) (tab : List (ℕ × List (List SInt))) (m : ℕ) : List (List SInt) :=
  match tab.find? (fun e => e.1 == m) with
  | some e => e.2
  | none => localRowsF (C.mods.getD m default) kpos lpos

/-- Leg-4 (auxiliary) module of an item. -/
def m4Of (C : CertD) (it : ℕ × ℕ × ℕ) : ℕ := (C.types.getD it.1 default).mods.getD 4 0

/-- Spec of a rule group (entry rule `kpos lpos`) on the slice `w4`: rows from the table; a leaf is the sum of its
items' contracted tensors. -/
def sliceSpec (C : CertD) (coef : Int) (kpos lpos : List ℕ) (tab : List (ℕ × List (List SInt))) (w4 : ℕ) : Spec where
  rows m := lookTab C kpos lpos tab m
  dimsq m := mdim C m * mdim C m
  leaf m1 m2 m3 lf := (lf.items.map fun it =>
      itemTF5c C coef (mdim C lf.m0) (mdim C m1) (mdim C m2) (mdim C m3) (mdim C (m4Of C it))
        (((lookTab C kpos lpos tab (m4Of C it)).getD w4 []).map SInt.val) it).foldr addL []

/-- Modules used by a group: legs 0..3 from the tree, leg 4 from the items' types. -/
def grpMods (C : CertD) (G : GrpF) : List ℕ :=
  (G.tree.flatMap fun n3 => n3.m3 :: n3.kids.flatMap fun n2 => n2.m2 :: n2.kids.flatMap fun n1 =>
    n1.m1 :: n1.kids.flatMap fun lf => lf.m0 :: lf.items.map (m4Of C)).eraseDups

/-- The part of a rule group on the slice `w4`. -/
def slicePart (C : CertD) (coef : Int) (w4 : ℕ) (G : GrpF) : Part :=
  ⟨sliceSpec C coef G.kpos G.lpos (rowTab C G.kpos G.lpos (grpMods C G)) w4, G.tree⟩

/-! ### The slice check -/

/-- **Slice check with offsets.** The digit width suffices, the class list covers the slice, and routing the
digits of the summed slices by `cls` into `t0` (whose leaves start at the offsets) sets every leaf flag and leaves
every leaf sum zero: the slice's class sums are the negated offsets. -/
def sliceCheck (b : Nat) (ps : List Part) (cls : List Nat) (t0 : AT) : Bool :=
  decide (0 < b) && decide (partsBound ps < 2 ^ (b - 1)) && (cls.length == 24 * slen) &&
    (routeL (digitsOf b (partsSlicesA b ps)) cls t0).leaves.all (fun e => e.2.2 && e.2.1.mag == 0)

/-- The class sums of a slice (to generate offsets): the leaves of `t0` after routing. -/
def sliceSums (b : Nat) (ps : List Part) (cls : List Nat) (t0 : AT) : List (Nat × SInt × Bool) :=
  (routeL (digitsOf b (partsSlicesA b ps)) cls t0).leaves

end NPT.K4.Route
