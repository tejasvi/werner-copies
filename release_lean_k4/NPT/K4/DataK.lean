/-
NPT.K4.DataK — kernel-friendly forms of the route's data checks.

The data checks `grpOK5` and the item permutation read `C.types.getD t` and `C.Z.getD z` for every item; when the type
and block lists are concatenations of chunks, each such read makes the kernel unfold the concatenation, which does not
fit in memory for 5484 items.  Here:
* `getDChunks d Ls i` reads index `i` of `Ls.flatten` chunk by chunk (`getDChunks_eq`), and `itemOKL` / `grpOKL` are
  `itemOK5` / `grpOK5` with the two lookups as parameters (`grpOK5_L`, by `rfl`);
* `allItemsL` lists the multiplier entries of a family in one pass over the types (`allItems_eq_L`);
* `msortF` is a merge sort with fuel (structural, so the kernel evaluates it), a permutation of its input for any fuel
  and order (`msortF_perm`): if the sorted group items equal `allItemsL …`, the groups' items are a permutation of the
  family's entries.
-/
import NPT.K4.Route.Group5

namespace NPT.K4.Route

open NPT.Cert NPT.Cert.Sem NPT.Cert.Ident

/-! ### Chunked lookups -/

/-- Index `i` of `Ls.flatten`, read chunk by chunk. -/
def getDChunks {α : Type} (d : α) : List (List α) → ℕ → α
  | [], _ => d
  | L :: Ls, i => if i < L.length then L.getD i d else getDChunks d Ls (i - L.length)

lemma getD_append_split {α : Type} (A B : List α) (d : α) (i : ℕ) :
    (A ++ B).getD i d = if i < A.length then A.getD i d else B.getD (i - A.length) d := by
  split_ifs with h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), ← List.getD_eq_getElem?_getD]

lemma getDChunks_eq {α : Type} (d : α) : ∀ (Ls : List (List α)) (i : ℕ), getDChunks d Ls i = Ls.flatten.getD i d
  | [], i => by simp [getDChunks]
  | L :: Ls, i => by rw [getDChunks, List.flatten_cons, getD_append_split, getDChunks_eq d Ls]

/-! ### Group data checks with parametric lookups -/

/-- `itemOK5` with the type and block lookups as parameters. -/
def itemOKL (tyL : ℕ → TypeD) (zL : ℕ → NPT.Cert.PBlock) (mods : List ModD) (dd E0 fam : ℕ) (kpos lpos : List ℕ)
    (m0 m1 m2 m3 : ℕ) (it : ℕ × ℕ × ℕ) : Bool :=
  let t := tyL it.1
  let R := (t.rules.getD it.2.1 []).getD it.2.2 default
  t.mods == [m0, m1, m2, m3, t.mods.getD 4 0] && R.kpos == kpos && R.lpos == lpos && R.fam == fam &&
  (mods.getD m0 default).n == dd && (mods.getD m1 default).n == dd &&
  (mods.getD m2 default).n == dd && (mods.getD m3 default).n == dd &&
  (mods.getD (t.mods.getD 4 0) default).n == 2 &&
  (zL t.zi).uent.isEmpty && (zL t.zi).E == E0

/-- `grpOK5` with the type and block lookups as parameters. -/
def grpOKL (tyL : ℕ → TypeD) (zL : ℕ → NPT.Cert.PBlock) (mods : List ModD) (dd E0 : ℕ) (G : GrpF) : Bool :=
  G.tree.all fun n3 => n3.kids.all fun n2 => n2.kids.all fun n1 => n1.kids.all fun lf =>
    lf.items.all (itemOKL tyL zL mods dd E0 G.fam G.kpos G.lpos lf.m0 n1.m1 n2.m2 n3.m3)

lemma grpOK5_L (C : CertD) (E0 : ℕ) (G : GrpF) :
    grpOK5 C E0 G = grpOKL (fun i => C.types.getD i default) (fun i => C.Z.getD i default) C.mods C.d E0 G := rfl

/-! ### The multiplier entries of a family in one pass -/

/-- The entries `(ti, r, s)` of type `t` (index `ti`) that belong to family `f`. -/
def itemsOfType (f : ℕ) (t : TypeD) (ti : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range t.nrows).flatMap fun r => ((List.range t.nrows).filter fun s =>
    ((t.rules.getD r []).getD s default).fam == f).map fun s => (ti, r, s)

/-- The entries of family `f`, one pass over the types (indices from `ti`). -/
def allItemsL (f : ℕ) : List TypeD → ℕ → List (ℕ × ℕ × ℕ)
  | [], _ => []
  | t :: ts, ti => itemsOfType f t ti ++ allItemsL f ts (ti + 1)

lemma allItems_range' (f : ℕ) : ∀ (l : List TypeD) (s : ℕ),
    (List.range' s l.length).flatMap (fun i => itemsOfType f (l.getD (i - s) default) i) = allItemsL f l s
  | [], s => by simp [allItemsL]
  | t :: ts, s => by
    rw [List.length_cons, List.range'_succ, List.flatMap_cons, Nat.sub_self, List.getD_cons_zero, allItemsL]
    congr 1
    rw [← allItems_range' f ts (s + 1)]
    refine List.flatMap_congr fun i hi => ?_
    rw [List.mem_range'_1] at hi
    have e : i - s = (i - (s + 1)) + 1 := by omega
    rw [e, List.getD_cons_succ]

lemma allItems_eq_L (C : CertD) (f : ℕ) : allItems C f = allItemsL f C.types 0 := by
  rw [← allItems_range' f C.types 0, ← List.range_eq_range']
  rfl

/-! ### Merge sort with fuel -/

/-- Merge with fuel (a permutation of `xs ++ ys` for any fuel). -/
def mergeF {α : Type} (le : α → α → Bool) : ℕ → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | n + 1, x :: xs, y :: ys => if le x y then x :: mergeF le n xs (y :: ys) else y :: mergeF le n (x :: xs) ys

lemma mergeF_perm {α : Type} (le : α → α → Bool) : ∀ (n : ℕ) (xs ys : List α), (mergeF le n xs ys).Perm (xs ++ ys)
  | 0, xs, ys => List.Perm.refl _
  | _ + 1, [], ys => by simp [mergeF]
  | _ + 1, x :: xs, [] => by simp [mergeF]
  | n + 1, x :: xs, y :: ys => by
    unfold mergeF
    split_ifs
    · exact (mergeF_perm le n xs (y :: ys)).cons x
    · exact ((mergeF_perm le n (x :: xs) ys).cons y).trans List.perm_middle.symm

/-- Merge sort with fuel (a permutation of its input for any fuel; sorted when the fuel suffices). -/
def msortF {α : Type} (le : α → α → Bool) : ℕ → List α → List α
  | 0, l => l
  | n + 1, l => if l.length ≤ 1 then l else
      mergeF le l.length (msortF le n (l.take (l.length / 2))) (msortF le n (l.drop (l.length / 2)))

lemma msortF_perm {α : Type} (le : α → α → Bool) : ∀ (n : ℕ) (l : List α), (msortF le n l).Perm l
  | 0, l => List.Perm.refl _
  | n + 1, l => by
    unfold msortF
    split_ifs
    · exact List.Perm.refl _
    · refine (mergeF_perm le _ _ _).trans ?_
      have h := (msortF_perm le n (l.take (l.length / 2))).append (msortF_perm le n (l.drop (l.length / 2)))
      rw [List.take_append_drop] at h
      exact h

/-- Lexicographic order on entries. -/
def lexLe (a b : ℕ × ℕ × ℕ) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2 ≤ b.2.2)))

/-- **Item permutation from a sorted comparison.** -/
theorem items_perm_of_sort (C : CertD) (f : ℕ) (gs : List GrpF) (fuel : ℕ)
    (h : msortF lexLe fuel (gs.flatMap fun G => itemsOf G.tree) = allItemsL f C.types 0) :
    (gs.flatMap fun G => itemsOf G.tree).Perm (allItems C f) := by
  rw [allItems_eq_L, ← h]
  exact (msortF_perm lexLe fuel _).symm

end NPT.K4.Route

#print axioms NPT.K4.Route.items_perm_of_sort
#print axioms NPT.K4.Route.getDChunks_eq
