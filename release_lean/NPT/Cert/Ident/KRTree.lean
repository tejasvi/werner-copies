/-
NPT.Cert.Ident.KRTree — a rule group's box tree evaluated with recursor stages, leaf tensors in row form: `evalTreeRR … = evalTree (specRows …) …` whenever the row-form leaves have the expected shape.
-/
import NPT.Cert.Ident.KRRed
import NPT.Cert.Ident.ChunkSpec

open BigOperators Finset NPT.Cert.Sem NPT.Cert.Ident

namespace NPT.Cert.KR

/-- A rule group's spec with tabulated rows, leaf tensors given in row form by `lr d0 d1 d2 d3 items`. -/
def specRows (C : CertD) (kpos lpos : List ℕ) (tab : List (List (List SInt)))
    (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) : Spec where
  rows m := tab.getD m (localRowsF default kpos lpos)
  dimsq m := mdim C m * mdim C m
  leaf m1 m2 m3 lf := (lr (mdim C lf.m0) (mdim C m1) (mdim C m2) (mdim C m3) lf.items).flatten

section Eval

variable (C : CertD) (kpos lpos : List ℕ) (tab : List (List (List SInt)))
  (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (b : ℕ)

noncomputable def evalLeafRR (m1 m2 m3 : ℕ) (lf : Leaf) : List SInt :=
  colStageR (packCols b (mdim C lf.m0 * mdim C lf.m0) (tab.getD lf.m0 (localRowsF default kpos lpos)))
    (lr (mdim C lf.m0) (mdim C m1) (mdim C m2) (mdim C m3) lf.items)

noncomputable def evalNd1RR (m2 m3 : ℕ) (nd : Nd1) : List SInt :=
  rowStageR (tab.getD nd.m1 (localRowsF default kpos lpos)) (mdim C nd.m1 * mdim C nd.m1)
    (mdim C m2 * mdim C m2 * (mdim C m3 * mdim C m3)) (24 * b)
    (foldrR (fun lf acc => addLR (evalLeafRR C kpos lpos tab lr b nd.m1 m2 m3 lf) acc) [] nd.kids)

noncomputable def evalNd2RR (m3 : ℕ) (nd : Nd2) : List SInt :=
  rowStageR (tab.getD nd.m2 (localRowsF default kpos lpos)) (mdim C nd.m2 * mdim C nd.m2)
    (mdim C m3 * mdim C m3) (576 * b)
    (foldrR (fun n1 acc => addLR (evalNd1RR C kpos lpos tab lr b nd.m2 m3 n1) acc) [] nd.kids)

noncomputable def evalNd3RR (nd : Nd3) : List SInt :=
  finalStageR (tab.getD nd.m3 (localRowsF default kpos lpos))
    (foldrR (fun n2 acc => addLR (evalNd2RR C kpos lpos tab lr b nd.m3 n2) acc) [] nd.kids)

/-- The 24 slices of a rule group, by recursor stages. -/
noncomputable def evalTreeRR (tree : List Nd3) : List SInt :=
  foldrR (fun n3 acc => addLR (evalNd3RR C kpos lpos tab lr b n3) acc) [] tree

end Eval

theorem chunks_flatten (M : ℕ) : ∀ (rows : List (List SInt)), (∀ r ∈ rows, r.length = M) →
    chunks M rows.length rows.flatten = rows
  | [], _ => rfl
  | r :: rows, h => by
    simp only [List.length_cons, chunks, List.flatten_cons]
    have hr : r.length = M := h r (by simp)
    rw [List.take_left' hr, List.drop_left' hr, chunks_flatten M rows fun x hx => h x (by simp [hx])]

theorem lincomb_nil_rows : ∀ (P : List SInt) (n : ℕ), lincomb P (List.replicate n []) = []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | c :: P, n + 1 => by
    simp only [List.replicate_succ, lincomb, lincomb_nil_rows P n]
    rfl

theorem lincomb_nil_right (P : List SInt) : lincomb P [] = [] := by cases P <;> rfl

theorem chunks_nil (M : ℕ) : ∀ n, chunks M n ([] : List SInt) = List.replicate n []
  | 0 => rfl
  | n + 1 => by simp only [chunks, List.take_nil, List.drop_nil, chunks_nil M n, List.replicate_succ]

/-- Shape of row-form leaves: `d0²` rows (or none) of length `d1² d2² d3²`. -/
def LRShape (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) : Prop :=
  ∀ d0 d1 d2 d3 items, ((lr d0 d1 d2 d3 items).length = d0 * d0 ∨ lr d0 d1 d2 d3 items = []) ∧
    ∀ r ∈ lr d0 d1 d2 d3 items, r.length = d1 * d1 * (d2 * d2) * (d3 * d3)

section EvalEq

variable (C : CertD) (kpos lpos : List ℕ) (tab : List (List (List SInt)))
  (lr : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ × ℕ) → List (List SInt)) (b : ℕ) (hlr : LRShape lr)
include hlr

theorem evalLeafRR_eq (m1 m2 m3 : ℕ) (lf : Leaf) :
    evalLeafRR C kpos lpos tab lr b m1 m2 m3 lf = evalLeaf (specRows C kpos lpos tab lr) b m1 m2 m3 lf := by
  unfold evalLeafRR evalLeaf colStageR colStage
  simp only [specRows]
  rw [lincombR_eq, packCols_length]
  obtain ⟨hlen, hrow⟩ := hlr (mdim C lf.m0) (mdim C m1) (mdim C m2) (mdim C m3) lf.items
  rcases hlen with hlen | hnil
  · rw [← hlen, chunks_flatten _ _ hrow]
  · rw [hnil, List.flatten_nil, chunks_nil, lincomb_nil_rows, lincomb_nil_right]

theorem evalNd1RR_eq (m2 m3 : ℕ) (nd : Nd1) :
    evalNd1RR C kpos lpos tab lr b m2 m3 nd = evalNd1 (specRows C kpos lpos tab lr) b m2 m3 nd := by
  unfold evalNd1RR evalNd1
  rw [rowStageR_eq, foldrR_eq, List.foldr_map]
  simp only [specRows]
  refine congrArg (fun f => rowStage _ _ _ _ (List.foldr f [] nd.kids)) (funext fun lf => funext fun acc => ?_)
  rw [addLR_eq, evalLeafRR_eq C kpos lpos tab lr b hlr]
  rfl

theorem evalNd2RR_eq (m3 : ℕ) (nd : Nd2) :
    evalNd2RR C kpos lpos tab lr b m3 nd = evalNd2 (specRows C kpos lpos tab lr) b m3 nd := by
  unfold evalNd2RR evalNd2
  rw [rowStageR_eq, foldrR_eq, List.foldr_map]
  simp only [specRows]
  refine congrArg (fun f => rowStage _ _ _ _ (List.foldr f [] nd.kids)) (funext fun n1 => funext fun acc => ?_)
  rw [addLR_eq, evalNd1RR_eq C kpos lpos tab lr b hlr]
  rfl

theorem evalNd3RR_eq (nd : Nd3) :
    evalNd3RR C kpos lpos tab lr b nd = evalNd3 (specRows C kpos lpos tab lr) b nd := by
  unfold evalNd3RR evalNd3
  rw [finalStageR_eq, foldrR_eq, List.foldr_map]
  simp only [specRows]
  refine congrArg (fun f => finalStage _ (List.foldr f [] nd.kids)) (funext fun n2 => funext fun acc => ?_)
  rw [addLR_eq, evalNd2RR_eq C kpos lpos tab lr b hlr]
  rfl

/-- **The recursor evaluation is the checked one.** -/
theorem evalTreeRR_eq (tree : List Nd3) :
    evalTreeRR C kpos lpos tab lr b tree = evalTree (specRows C kpos lpos tab lr) b tree := by
  unfold evalTreeRR evalTree
  rw [foldrR_eq, List.foldr_map]
  refine congrArg (fun f => List.foldr f [] tree) (funext fun n3 => funext fun acc => ?_)
  rw [addLR_eq, evalNd3RR_eq C kpos lpos tab lr b hlr]

end EvalEq

end NPT.Cert.KR
