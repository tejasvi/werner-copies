/-
NPT.Cert.Ident.ChunkSpec — the parts of a family with precomputed tables, for kernel chunks:
rule-group local rows from per-group tables (`famPartsK`, equal to `famParts` when each table is the group's
`mkTab`), and equality maps from per-spec tables with `eqLocF` as fallback (`eqTK`, equal to `eqLocF`).
-/
import NPT.Cert.Ident.Fast

open BigOperators Finset NPT.Cert.Sem

namespace NPT.Cert.Ident

deriving instance DecidableEq for SInt

/-- The parts of family `f`, rule groups with the given row tables (one per group, in order). -/
def famPartsK (C : CertD) (zmul f : ℕ) (gs : List GrpF) (tabs : List (List (List (List SInt))))
    (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : List Part :=
  (gs.zip tabs).map (fun Gt => ⟨ruleSpecT C zmul (-(den3 C.d : ℤ)) Gt.1.kpos Gt.1.lpos Gt.2, Gt.1.tree⟩) ++
    (if f = 0 then [rank1Part (objE zs za) (2 * C.Lden)] else []) ++ eqPartsF C f eqT

lemma zip_map_tabs (C : CertD) (zmul : ℕ) (coef : ℤ) : ∀ (gs : List GrpF),
    (gs.zip (gs.map fun G => mkTab C G.kpos G.lpos (supps 2 G.kpos G.lpos) (supps 3 G.kpos G.lpos))).map
      (fun Gt => (⟨ruleSpecT C zmul coef Gt.1.kpos Gt.1.lpos Gt.2, Gt.1.tree⟩ : Part)) =
    gs.map fun G => ⟨ruleSpecF C zmul coef G.kpos G.lpos, G.tree⟩
  | [] => rfl
  | G :: gs => by
    simp only [List.map_cons, List.zip_cons_cons]
    rw [ruleSpecT_eq, zip_map_tabs C zmul coef gs]

lemma famPartsK_eq (C : CertD) (zmul f : ℕ) (gs : List GrpF) (tabs : List (List (List (List SInt))))
    (htabs : tabs = gs.map fun G => mkTab C G.kpos G.lpos (supps 2 G.kpos G.lpos) (supps 3 G.kpos G.lpos))
    (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) :
    famPartsK C zmul f gs tabs zs za eqT = famParts C zmul f gs zs za eqT := by
  subst htabs
  unfold famPartsK famParts
  rw [zip_map_tabs]

/-! ### Item tensors by a given function -/

/-- Rule-group spec with row tables and leaf tensors from `itemFn` (any function equal to `itemTF`). -/
def ruleSpecTI (C : CertD) (zmul : ℕ) (coef : Int) (kpos lpos : List ℕ) (tab : List (List (List SInt)))
    (itemFn : CertD → ℕ → Int → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ → List SInt) : Spec where
  rows m := tab.getD m (localRowsF default kpos lpos)
  dimsq m := mdim C m * mdim C m
  leaf m1 m2 m3 lf :=
    (lf.items.map (itemFn C zmul coef (mdim C lf.m0) (mdim C m1) (mdim C m2) (mdim C m3))).foldr addL []

lemma ruleSpecTI_eq (C : CertD) (zmul : ℕ) (coef : Int) (kpos lpos : List ℕ) (tab : List (List (List SInt)))
    (itemFn : CertD → ℕ → Int → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ → List SInt) (hI : itemFn = itemTF) :
    ruleSpecTI C zmul coef kpos lpos tab itemFn = ruleSpecT C zmul coef kpos lpos tab := by
  subst hI; rfl

/-- `famPartsK` with leaf tensors from `itemFn`. -/
def famPartsKI (C : CertD) (zmul f : ℕ) (gs : List GrpF) (tabs : List (List (List (List SInt))))
    (itemFn : CertD → ℕ → Int → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ → List SInt)
    (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) : List Part :=
  (gs.zip tabs).map (fun Gt => ⟨ruleSpecTI C zmul (-(den3 C.d : ℤ)) Gt.1.kpos Gt.1.lpos Gt.2 itemFn, Gt.1.tree⟩) ++
    (if f = 0 then [rank1Part (objE zs za) (2 * C.Lden)] else []) ++ eqPartsF C f eqT

lemma famPartsKI_eq (C : CertD) (zmul f : ℕ) (gs : List GrpF) (tabs : List (List (List (List SInt))))
    (itemFn : CertD → ℕ → Int → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ → List SInt) (hI : itemFn = itemTF)
    (zs za : Fin 24 → ℤ) (eqT : EqSpecD → ℕ → Fin 24 → ℕ → ℤ) :
    famPartsKI C zmul f gs tabs itemFn zs za eqT = famPartsK C zmul f gs tabs zs za eqT := by
  subst hI; rfl

/-! ### Equality tables -/

def specEq (a b : EqSpecD) : Bool :=
  a.slot == b.slot && a.order == b.order && a.kind == b.kind && a.mkeys == b.mkeys

lemma specEq_eq {a b : EqSpecD} (h : specEq a b = true) : a = b := by
  unfold specEq at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  cases a; cases b; simp_all

/-- Table of `eqLocF C sp n p o` for `p < 24`, `o < N`. -/
def eqTabOf (C : CertD) (sp : EqSpecD) (n N : ℕ) : List (List ℤ) :=
  (List.finRange 24).map fun p => (List.range N).map fun o => eqLocF C sp n p o

/-- Equality maps from tables `(spec, n, table)`; `eqLocF` outside the tables. -/
def eqTK (tabs : List (EqSpecD × ℕ × List (List ℤ))) (C : CertD) (sp : EqSpecD) (n : ℕ) (p : Fin 24) (o : ℕ) : ℤ :=
  match tabs.find? (fun e => specEq e.1 sp && e.2.1 == n) with
  | some e => if o < (e.2.2.getD p.val []).length then (e.2.2.getD p.val []).getD o 0 else eqLocF C sp n p o
  | none => eqLocF C sp n p o

lemma eqTK_eq (tabs : List (EqSpecD × ℕ × List (List ℤ))) (C : CertD)
    (htabs : ∀ e ∈ tabs, ∃ N, e.2.2 = eqTabOf C e.1 e.2.1 N) : eqTK tabs C = eqLocF C := by
  funext sp n p o
  unfold eqTK
  split
  · rename_i e he
    have hmem := List.mem_of_find?_eq_some he
    have hp := List.find?_some he
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨hs, hn⟩ := hp
    have hs' := specEq_eq hs
    obtain ⟨N, hN⟩ := htabs e hmem
    split_ifs with ho
    · rw [hN] at ho ⊢
      unfold eqTabOf at ho ⊢
      rw [map_finRange_getD] at ho ⊢
      rw [List.length_map, List.length_range] at ho
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ho]
      simp only [Option.map_some, Option.getD_some]
      rw [hs', hn]
    · rfl
  · rfl

end NPT.Cert.Ident
