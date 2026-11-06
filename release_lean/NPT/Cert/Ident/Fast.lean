/-
NPT.Cert.Ident.Fast — evaluation-order variants of the family check for native evaluation:
rule-group local rows from the rule supports (computed once per group) and tabulated per group, and slices
accumulated part by part.  Each variant is proved equal to the checked definition (`famCheckA_eq`).
-/
import NPT.Cert.Ident.IdFactGen

open BigOperators Finset NPT.Cert.Sem

namespace NPT.Cert.Ident

/-- Support of the entry rule at `p`: pairs of flat indices `(xi, yi)` with `condF`. -/
def supp (n : ℕ) (kpos lpos : List ℕ) (p : Fin 24) : List (ℕ × ℕ) :=
  (List.range (n ^ 4)).flatMap fun xi =>
    ((List.range (n ^ 4)).filter fun yi => condF n kpos lpos p xi yi).map fun yi => (xi, yi)

def supps (n : ℕ) (kpos lpos : List ℕ) : List (List (ℕ × ℕ)) := (List.finRange 24).map (supp n kpos lpos)

/-- Local rows from supports: entry `μ·dim + ν` of row `p` is `Σ_{(x, y) ∈ supp p} J[x][μ] J[y][ν]`. -/
def localRowsS (md : ModD) (S : List (List (ℕ × ℕ))) : List (List SInt) :=
  (List.finRange 24).map fun p => (List.range (md.dim * md.dim)).map fun k =>
    SInt.ofInt (((S.getD p.val []).map fun xy =>
      (md.J.getD xy.1 []).getD (k / md.dim) 0 * (md.J.getD xy.2 []).getD (k % md.dim) 0).sum)

lemma list_sum_flatMap_map {α β : Type*} (L : List α) (g : α → List β) (f : β → ℤ) :
    ((L.flatMap g).map f).sum = (L.map fun x => ((g x).map f).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

lemma list_sum_filter_map {β : Type*} (L : List β) (q : β → Bool) (h : β → ℤ) :
    ((L.filter q).map h).sum = (L.map fun y => if q y then h y else 0).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases hq : q a = true
    · simp [hq, ih]
    · simp [hq, ih]

lemma finset_sum_range_listZ (n : ℕ) (h : ℕ → ℤ) : ∑ r ∈ range n, h r = ((List.range n).map h).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]; simp

lemma supp_sum (n : ℕ) (J : List (List Int)) (kpos lpos : List ℕ) (p : Fin 24) (μ ν : ℕ) :
    ((supp n kpos lpos p).map fun xy => (J.getD xy.1 []).getD μ 0 * (J.getD xy.2 []).getD ν 0).sum =
      kmatF n J kpos lpos p μ ν := by
  unfold supp kmatF
  rw [list_sum_flatMap_map, finset_sum_range_listZ]
  congr 1
  refine List.map_congr_left fun xi _ => ?_
  rw [List.map_map, list_sum_filter_map, finset_sum_range_listZ]
  congr 1
  refine List.map_congr_left fun yi _ => ?_
  by_cases hc : condF n kpos lpos p xi yi = true <;> simp [hc]

lemma localRowsS_eq (md : ModD) (kpos lpos : List ℕ) :
    localRowsS md (supps md.n kpos lpos) = localRowsF md kpos lpos := by
  unfold localRowsS localRowsF
  refine List.map_congr_left fun p _ => List.map_congr_left fun k _ => ?_
  rw [supps, map_finRange_getD, supp_sum]

/-- Local rows of all modules for one entry rule (supports at `n = 2, 3` passed in). -/
def mkTab (C : CertD) (kpos lpos : List ℕ) (s2 s3 : List (List (ℕ × ℕ))) : List (List (List SInt)) :=
  C.mods.map fun md => localRowsS md (if md.n = 2 then s2 else if md.n = 3 then s3 else supps md.n kpos lpos)

lemma mkTab_eq (C : CertD) (kpos lpos : List ℕ) :
    mkTab C kpos lpos (supps 2 kpos lpos) (supps 3 kpos lpos) = C.mods.map fun md => localRowsF md kpos lpos := by
  unfold mkTab
  refine List.map_congr_left fun md _ => ?_
  split_ifs with h2 h3
  · rw [← h2, localRowsS_eq]
  · rw [← h3, localRowsS_eq]
  · rw [localRowsS_eq]

lemma getD_map' {α β : Type*} (L : List α) (g : α → β) (d : α) (m : ℕ) : (L.map g).getD m (g d) = g (L.getD m d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[m]? <;> rfl

/-- Rule-group spec with tabulated local rows. -/
def ruleSpecT (C : CertD) (zmul : ℕ) (coef : Int) (kpos lpos : List ℕ) (tab : List (List (List SInt))) : Spec where
  rows m := tab.getD m (localRowsF default kpos lpos)
  dimsq m := mdim C m * mdim C m
  leaf m1 m2 m3 lf := (lf.items.map (itemTF C zmul coef (mdim C lf.m0) (mdim C m1) (mdim C m2) (mdim C m3))).foldr addL []

lemma ruleSpecT_eq (C : CertD) (zmul : ℕ) (coef : Int) (kpos lpos : List ℕ) :
    ruleSpecT C zmul coef kpos lpos (mkTab C kpos lpos (supps 2 kpos lpos) (supps 3 kpos lpos)) =
      ruleSpecF C zmul coef kpos lpos := by
  unfold ruleSpecT ruleSpecF
  congr 1
  funext m
  rw [mkTab_eq, getD_map']

/-- The parts of family `f`, rule groups with tabulated local rows. -/
def famPartsT (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : List Part :=
  gs.map (fun G => ⟨ruleSpecT C zmul (-(den3 C.d : ℤ)) G.kpos G.lpos
      (mkTab C G.kpos G.lpos (supps 2 G.kpos G.lpos) (supps 3 G.kpos G.lpos)), G.tree⟩) ++
    (if f = 0 then [rank1Part (objE zs za) (2 * C.Lden)] else []) ++ eqPartsF C f eqT

lemma famPartsT_eq (C : CertD) (zmul f : ℕ) (gs : List GrpF) (zs za : Fin 24 → ℤ)
    (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : famPartsT C zmul f gs zs za eqT = famParts C zmul f gs zs za eqT := by
  unfold famPartsT famParts
  congr 2
  refine List.map_congr_left fun G _ => ?_
  rw [ruleSpecT_eq]

/-- Slices accumulated part by part. -/
def partsSlicesA (b : Nat) (ps : List Part) : List SInt := ps.foldr (fun P acc => addL (evalTree P.S b P.tree) acc) []

lemma partsSlicesA_eq (b : Nat) (ps : List Part) : partsSlicesA b ps = partsSlices b ps := by
  unfold partsSlicesA partsSlices
  rw [List.foldr_map]

/-- `famCheck` with accumulated slices. -/
def famCheckA (b : Nat) (ps : List Part) (cls : List Nat) (t0 : AT) : Bool :=
  decide (0 < b) && decide (partsBound ps < 2 ^ (b - 1)) && (cls.length == 24 * slen) &&
    t0.leaves.all (fun e => e.2.1.mag == 0) &&
    (routeL (digitsOf b (partsSlicesA b ps)) cls t0).leaves.all (fun e => e.2.2 && e.2.1.mag == 0)

lemma famCheckA_eq (b : Nat) (ps : List Part) (cls : List Nat) (t0 : AT) : famCheckA b ps cls t0 = famCheck b ps cls t0 := by
  unfold famCheckA famCheck
  rw [partsSlicesA_eq]

end NPT.Cert.Ident
