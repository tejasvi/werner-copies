/-
NPT.Cert.Ident.Pipe — correctness of the packed tree evaluation:
the slice `w3` of `evalGrp X G` equals `Σ_{w0,w1,w2} specGrp X G w · 2^(b (w0 + 24 w1 + 576 w2))`, where
`specGrp` is the multilinear form of the box tree (local rows × leaf tensors).
-/
import NPT.Cert.Ident.Check
import NPT.Cert.Ident.Lemmas

open BigOperators Finset NPT.Cert.Sem

namespace NPT.Cert.Ident

/-! ### Lengths -/

lemma addL_length : ∀ (xs ys : List SInt), (addL xs ys).length = max xs.length ys.length
  | [], ys => by simp [addL]
  | x :: xs, [] => by simp [addL]
  | x :: xs, y :: ys => by simp [addL, addL_length xs ys, Nat.succ_max_succ]

lemma mulL_length (c : SInt) : ∀ (xs : List SInt), (mulL c xs).length = xs.length
  | [] => rfl
  | x :: xs => by simp [mulL, mulL_length c xs]

lemma shlL_length (k : Nat) : ∀ (xs : List SInt), (shlL k xs).length = xs.length
  | [] => rfl
  | x :: xs => by simp [shlL, shlL_length k xs]

lemma lincomb_length_le (M : Nat) : ∀ (cs : List SInt) (vs : List (List SInt)),
    (∀ v ∈ vs, v.length ≤ M) → (lincomb cs vs).length ≤ M
  | [], vs, _ => by simp [lincomb]
  | c :: cs, [], _ => by simp [lincomb]
  | c :: cs, v :: vs, h => by
    simp only [lincomb, addL_length, mulL_length]
    exact max_le (h v (by simp)) (lincomb_length_le M cs vs fun u hu => h u (by simp [hu]))

lemma chunks_mem_length (M : Nat) : ∀ (n : Nat) (xs : List SInt), ∀ v ∈ chunks M n xs, v.length ≤ M
  | 0, _ => by simp [chunks]
  | n + 1, xs => by
    intro v hv
    simp only [chunks, List.mem_cons] at hv
    rcases hv with rfl | hv
    · simp
    · exact chunks_mem_length M n _ v hv

lemma foldr_addL_length_le (M : Nat) (Ls : List (List SInt)) (h : ∀ L ∈ Ls, L.length ≤ M) :
    (Ls.foldr addL []).length ≤ M := by
  induction Ls with
  | nil => simp
  | cons L Ls ih =>
    simp only [List.foldr_cons, addL_length]
    exact max_le (h L (by simp)) (ih fun L' hL' => h L' (by simp [hL']))

lemma pairUp_mem_length (s M : Nat) : ∀ (Ls : List (List SInt)), (∀ L ∈ Ls, L.length ≤ M) →
    ∀ L ∈ pairUp s Ls, L.length ≤ M
  | [], _ => by simp [pairUp]
  | [a], h => by simpa [pairUp] using h
  | a :: b :: rest, h => by
    intro L hL
    simp only [pairUp, List.mem_cons] at hL
    rcases hL with rfl | hL
    · simp only [addL_length, shlL_length]
      exact max_le (h a (by simp)) (h b (by simp))
    · exact pairUp_mem_length s M rest (fun L' hL' => h L' (by simp [hL'])) L hL

lemma combine_length_le (M : Nat) : ∀ (fuel s : Nat) (Ls : List (List SInt)), (∀ L ∈ Ls, L.length ≤ M) →
    (combine fuel s Ls).length ≤ M
  | 0, s, [], _ => by simp [combine]
  | 0, s, a :: rest, h => by simpa [combine] using h a (by simp)
  | fuel + 1, s, [], _ => by simp [combine]
  | fuel + 1, s, [a], h => by simpa [combine] using h
  | fuel + 1, s, a :: b :: rest, h => by
    simp only [combine]
    exact combine_length_le M fuel (2 * s) _ (pairUp_mem_length s M _ h)

lemma rowStage_length_le (A : List (List SInt)) (n M s : Nat) (xs : List SInt) :
    (rowStage A n M s xs).length ≤ M := by
  unfold rowStage
  refine combine_length_le M 5 s _ fun L hL => ?_
  simp only [List.mem_map] at hL
  obtain ⟨row, _, rfl⟩ := hL
  exact lincomb_length_le M row _ (chunks_mem_length M n xs)

/-! ### Packed columns and local rows -/

lemma packCols_length (b n : Nat) (A : List (List SInt)) : (packCols b n A).length = n := by
  simp [packCols]

/-- Entry `(w, k)` of a row table, as an integer. -/
def aval (A : List (List SInt)) (w k : Nat) : Int := ((A.getD w []).getD k SInt.zero).val

lemma colOf_getD (A : List (List SInt)) (i w : Nat) :
    (colOf A i).getD w SInt.zero = (A.getD w []).getD i SInt.zero := by
  unfold colOf
  rcases Nat.lt_or_ge w A.length with h | h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h,
      List.getD_eq_getElem?_getD (l := A), List.getElem?_eq_getElem h]; rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none h,
      List.getD_eq_getElem?_getD (l := A), List.getElem?_eq_none h]; simp

lemma packCols_val (b n : Nat) (A : List (List SInt)) (i : Nat) (hi : i < n) :
    ((packCols b n A).getD i SInt.zero).val = ∑ w ∈ range A.length, aval A w i * 2 ^ (b * w) := by
  unfold packCols
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  rw [packH_val]
  simp only [colOf, List.length_map]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← colOf, colOf_getD]; rfl

lemma localRows_length (md : ModD) (i : Nat) : (localRows md i).length = 24 := by
  simp [localRows]

/-- Sums over `min`: terms beyond the shorter length vanish. -/
lemma sum_range_min_eq {f : Nat → Int} {a n : Nat} (h : ∀ k, a ≤ k → f k = 0) :
    ∑ k ∈ range (min a n), f k = ∑ k ∈ range n, f k := by
  rcases le_total a n with han | hna
  · rw [min_eq_left han]
    exact Finset.sum_subset (Finset.range_mono han) fun k hk hk' => h k (by simp at hk'; omega)
  · rw [min_eq_right hna]

lemma getD_zero_of_le (xs : List SInt) (j : Nat) (h : xs.length ≤ j) : xs.getD j SInt.zero = SInt.zero := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

lemma aval_eq_zero_of_le (A : List (List SInt)) (w k : Nat) (h : (A.getD w []).length ≤ k) : aval A w k = 0 := by
  rw [aval, getD_zero_of_le _ _ h]; simp

lemma gv_eq_zero_of_le (xs : List SInt) (j : Nat) (h : xs.length ≤ j) : gv xs j = 0 := by
  rw [gv, getD_zero_of_le _ _ h]; simp

/-! ### Specification of the tree -/

variable (S : Spec) (b : Nat)

/-- Leaf level: leg 0 contracted at word `w0`; `j` = flat index over `(i1, i2, i3)`. -/
def sL (m1 m2 m3 : Nat) (lf : Leaf) (w0 j : Nat) : Int :=
  ∑ i0 ∈ range (S.dimsq lf.m0), aval (S.rows lf.m0) w0 i0 *
    gv (S.leaf m1 m2 m3 lf) (i0 * (S.dimsq m1 * S.dimsq m2 * S.dimsq m3) + j)

/-- `Nd1` level: legs 0, 1 contracted; `j` = flat index over `(i2, i3)`. -/
def sN1 (m2 m3 : Nat) (nd : Nd1) (w0 w1 j : Nat) : Int :=
  ∑ i1 ∈ range (S.dimsq nd.m1), aval (S.rows nd.m1) w1 i1 *
    (nd.kids.map fun lf => sL S nd.m1 m2 m3 lf w0 (i1 * (S.dimsq m2 * S.dimsq m3) + j)).sum

/-- `Nd2` level: legs 0, 1, 2 contracted; `j` = index `i3`. -/
def sN2 (m3 : Nat) (nd : Nd2) (w0 w1 w2 j : Nat) : Int :=
  ∑ i2 ∈ range (S.dimsq nd.m2), aval (S.rows nd.m2) w2 i2 *
    (nd.kids.map fun n1 => sN1 S nd.m2 m3 n1 w0 w1 (i2 * S.dimsq m3 + j)).sum

/-- `Nd3` level: all legs contracted. -/
def sN3 (nd : Nd3) (w0 w1 w2 w3 : Nat) : Int :=
  ∑ i3 ∈ range (S.dimsq nd.m3), aval (S.rows nd.m3) w3 i3 *
    (nd.kids.map fun n2 => sN2 S nd.m3 n2 w0 w1 w2 i3).sum

/-- The value of a box tree at a word: its multilinear form. -/
def specTree (tree : List Nd3) (w0 w1 w2 w3 : Nat) : Int :=
  (tree.map fun nd => sN3 S nd w0 w1 w2 w3).sum

/-! ### Level lemmas -/

lemma evalLeaf_length_le (m1 m2 m3 : Nat) (lf : Leaf) :
    (evalLeaf S b m1 m2 m3 lf).length ≤ S.dimsq m1 * S.dimsq m2 * S.dimsq m3 :=
  lincomb_length_le _ _ _ (chunks_mem_length _ _ _)

variable (hS : ∀ m, (S.rows m).length = 24)
include hS

lemma evalLeaf_gv (m1 m2 m3 : Nat) (lf : Leaf) (j : Nat) (hj : j < S.dimsq m1 * S.dimsq m2 * S.dimsq m3) :
    gv (evalLeaf S b m1 m2 m3 lf) j = ∑ w0 ∈ range 24, sL S m1 m2 m3 lf w0 j * 2 ^ (b * w0) := by
  unfold evalLeaf
  rw [colStage_gv _ _ _ _ hj, packCols_length]
  rw [show (∑ x ∈ range (S.dimsq lf.m0), ((packCols b (S.dimsq lf.m0) (S.rows lf.m0)).getD x SInt.zero).val *
      gv (S.leaf m1 m2 m3 lf) (x * (S.dimsq m1 * S.dimsq m2 * S.dimsq m3) + j)) =
      ∑ x ∈ range (S.dimsq lf.m0), (∑ w ∈ range 24, aval (S.rows lf.m0) w x * 2 ^ (b * w)) *
      gv (S.leaf m1 m2 m3 lf) (x * (S.dimsq m1 * S.dimsq m2 * S.dimsq m3) + j) from
    Finset.sum_congr rfl fun x hx => by rw [packCols_val _ _ _ _ (Finset.mem_range.1 hx), hS]]
  simp only [sL, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun x _ => by ring

omit hS in
lemma list_sum_map_sum {α : Type*} (L : List α) (s : Finset Nat) (f : α → Nat → Int) :
    (L.map fun x => ∑ k ∈ s, f x k).sum = ∑ k ∈ s, (L.map fun x => f x k).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, Finset.sum_add_distrib]

omit hS in
lemma list_sum_map_mul_right {α : Type*} (L : List α) (f : α → Int) (c : Int) :
    (L.map fun x => f x * c).sum = (L.map f).sum * c := by
  induction L with
  | nil => simp
  | cons a L ih => simp [ih, add_mul]

omit hS in
lemma gv_foldr_map {α : Type*} (L : List α) (g : α → List SInt) (j : Nat) :
    gv ((L.map g).foldr addL []) j = (L.map fun x => gv (g x) j).sum := by
  rw [gv_foldr_addL, List.map_map]; rfl

omit hS in
lemma rowStage_gv' (A : List (List SInt)) (hA : A.length = 24) (n M s : Nat) (xs : List SInt) (j : Nat)
    (hj : j < M) :
    gv (rowStage A n M s xs) j = ∑ w ∈ range 24, (∑ k ∈ range n, aval A w k * gv xs (k * M + j)) * 2 ^ (s * w) := by
  rw [rowStage_gv A n M s xs j hj (by rw [hA]; norm_num), hA]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  exact sum_range_min_eq fun k hk => by
    show aval A w k * gv xs (k * M + j) = 0
    rw [aval_eq_zero_of_le A w k hk, zero_mul]

omit hS in
lemma evalNd1_length_le (m2 m3 : Nat) (nd : Nd1) : (evalNd1 S b m2 m3 nd).length ≤ S.dimsq m2 * S.dimsq m3 :=
  rowStage_length_le _ _ _ _ _

lemma evalNd1_gv (m2 m3 : Nat) (nd : Nd1) (j : Nat) (hj : j < S.dimsq m2 * S.dimsq m3) :
    gv (evalNd1 S b m2 m3 nd) j =
      ∑ w1 ∈ range 24, (∑ w0 ∈ range 24, sN1 S m2 m3 nd w0 w1 j * 2 ^ (b * w0)) * 2 ^ (24 * b * w1) := by
  unfold evalNd1
  rw [rowStage_gv' _ (hS _) _ _ _ _ _ hj]
  refine Finset.sum_congr rfl fun w1 _ => ?_
  congr 1
  simp only [gv_foldr_map]
  have hidx : ∀ k ∈ range (S.dimsq nd.m1),
      (nd.kids.map fun lf => gv (evalLeaf S b nd.m1 m2 m3 lf) (k * (S.dimsq m2 * S.dimsq m3) + j)).sum =
      ∑ w0 ∈ range 24, (nd.kids.map fun lf => sL S nd.m1 m2 m3 lf w0 (k * (S.dimsq m2 * S.dimsq m3) + j)).sum *
        2 ^ (b * w0) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hlt : k * (S.dimsq m2 * S.dimsq m3) + j < S.dimsq nd.m1 * S.dimsq m2 * S.dimsq m3 := by
      have := Nat.mul_le_mul_right (S.dimsq m2 * S.dimsq m3) (Nat.succ_le_of_lt hk')
      rw [Nat.succ_mul] at this; rw [Nat.mul_assoc]; omega
    rw [show (nd.kids.map fun lf => gv (evalLeaf S b nd.m1 m2 m3 lf) (k * (S.dimsq m2 * S.dimsq m3) + j)) =
        (nd.kids.map fun lf => ∑ w0 ∈ range 24, sL S nd.m1 m2 m3 lf w0 (k * (S.dimsq m2 * S.dimsq m3) + j) *
          2 ^ (b * w0)) from List.map_congr_left fun lf _ => evalLeaf_gv S b hS _ _ _ lf _ hlt,
      list_sum_map_sum]
    exact Finset.sum_congr rfl fun w0 _ => list_sum_map_mul_right _ _ _
  rw [Finset.sum_congr rfl fun k hk => by rw [hidx k hk]]
  simp only [sN1, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w0 _ => Finset.sum_congr rfl fun k _ => by ring

omit hS in
lemma evalNd2_length_le (m3 : Nat) (nd : Nd2) : (evalNd2 S b m3 nd).length ≤ S.dimsq m3 :=
  rowStage_length_le _ _ _ _ _

lemma evalNd2_gv (m3 : Nat) (nd : Nd2) (j : Nat) (hj : j < S.dimsq m3) :
    gv (evalNd2 S b m3 nd) j = ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24,
      sN2 S m3 nd w0 w1 w2 j * 2 ^ (b * w0)) * 2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2) := by
  unfold evalNd2
  rw [rowStage_gv' _ (hS _) _ _ _ _ _ hj]
  refine Finset.sum_congr rfl fun w2 _ => ?_
  congr 1
  simp only [gv_foldr_map]
  have hidx : ∀ k ∈ range (S.dimsq nd.m2),
      (nd.kids.map fun n1 => gv (evalNd1 S b nd.m2 m3 n1) (k * S.dimsq m3 + j)).sum =
      ∑ w1 ∈ range 24, (∑ w0 ∈ range 24, (nd.kids.map fun n1 => sN1 S nd.m2 m3 n1 w0 w1 (k * S.dimsq m3 + j)).sum *
        2 ^ (b * w0)) * 2 ^ (24 * b * w1) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hlt : k * S.dimsq m3 + j < S.dimsq nd.m2 * S.dimsq m3 := by
      have := Nat.mul_le_mul_right (S.dimsq m3) (Nat.succ_le_of_lt hk')
      rw [Nat.succ_mul] at this; omega
    rw [show (nd.kids.map fun n1 => gv (evalNd1 S b nd.m2 m3 n1) (k * S.dimsq m3 + j)) =
        (nd.kids.map fun n1 => ∑ w1 ∈ range 24, (∑ w0 ∈ range 24, sN1 S nd.m2 m3 n1 w0 w1 (k * S.dimsq m3 + j) *
          2 ^ (b * w0)) * 2 ^ (24 * b * w1)) from List.map_congr_left fun n1 _ => evalNd1_gv S b hS _ _ n1 _ hlt,
      list_sum_map_sum]
    refine Finset.sum_congr rfl fun w1 _ => ?_
    rw [list_sum_map_mul_right, list_sum_map_sum]
    congr 1
    exact Finset.sum_congr rfl fun w0 _ => list_sum_map_mul_right _ _ _
  rw [Finset.sum_congr rfl fun k hk => by rw [hidx k hk]]
  simp only [sN2, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w0 _ => Finset.sum_congr rfl fun k _ => by ring

lemma evalNd3_gv (nd : Nd3) (w3 : Nat) (hw : w3 < 24) :
    gv (evalNd3 S b nd) w3 = ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24,
      sN3 S nd w0 w1 w2 w3 * 2 ^ (b * w0)) * 2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2) := by
  unfold evalNd3
  rw [finalStage_val _ _ w3 (by rw [hS]; exact hw)]
  set xs := (nd.kids.map (evalNd2 S b nd.m3)).foldr addL [] with hxs
  have hlen : xs.length ≤ S.dimsq nd.m3 :=
    foldr_addL_length_le _ _ fun L hL => by
      simp only [List.mem_map] at hL; obtain ⟨n2, _, rfl⟩ := hL; exact evalNd2_length_le S b _ _
  rw [show (∑ k ∈ range (min ((S.rows nd.m3).getD w3 []).length xs.length),
      (((S.rows nd.m3).getD w3 []).getD k SInt.zero).val * (xs.getD k SInt.zero).val) =
      ∑ k ∈ range (S.dimsq nd.m3), aval (S.rows nd.m3) w3 k * gv xs k from by
    rw [show (∑ k ∈ range (min ((S.rows nd.m3).getD w3 []).length xs.length),
        (((S.rows nd.m3).getD w3 []).getD k SInt.zero).val * (xs.getD k SInt.zero).val) =
        ∑ k ∈ range (min (min ((S.rows nd.m3).getD w3 []).length xs.length) (S.dimsq nd.m3)),
        aval (S.rows nd.m3) w3 k * gv xs k from by
      rw [min_eq_left (le_trans (min_le_right _ _) hlen)]; rfl]
    exact sum_range_min_eq fun k hk => by
      rcases le_total ((S.rows nd.m3).getD w3 []).length xs.length with h | h
      · rw [min_eq_left h] at hk; rw [aval_eq_zero_of_le _ _ _ hk, zero_mul]
      · rw [min_eq_right h] at hk; rw [gv_eq_zero_of_le _ _ hk, mul_zero]]
  rw [hxs]
  simp only [gv_foldr_map]
  have hidx : ∀ k ∈ range (S.dimsq nd.m3),
      (nd.kids.map fun n2 => gv (evalNd2 S b nd.m3 n2) k).sum =
      ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24, (nd.kids.map fun n2 => sN2 S nd.m3 n2 w0 w1 w2 k).sum *
        2 ^ (b * w0)) * 2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2) := by
    intro k hk
    rw [show (nd.kids.map fun n2 => gv (evalNd2 S b nd.m3 n2) k) =
        (nd.kids.map fun n2 => ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24, sN2 S nd.m3 n2 w0 w1 w2 k *
          2 ^ (b * w0)) * 2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2)) from
        List.map_congr_left fun n2 _ => evalNd2_gv S b hS _ n2 _ (Finset.mem_range.1 hk),
      list_sum_map_sum]
    refine Finset.sum_congr rfl fun w2 _ => ?_
    rw [list_sum_map_mul_right, list_sum_map_sum]
    congr 1
    refine Finset.sum_congr rfl fun w1 _ => ?_
    rw [list_sum_map_mul_right, list_sum_map_sum]
    congr 1
    exact Finset.sum_congr rfl fun w0 _ => list_sum_map_mul_right _ _ _
  rw [Finset.sum_congr rfl fun k hk => by rw [hidx k hk]]
  simp only [sN3, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w2 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w0 _ => Finset.sum_congr rfl fun k _ => by ring

/-- **Pipeline lemma.** Slice `w3` of a box tree is the packed vector of its multilinear form. -/
lemma evalTree_gv (tree : List Nd3) (w3 : Nat) (hw : w3 < 24) :
    gv (evalTree S b tree) w3 = ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24,
      specTree S tree w0 w1 w2 w3 * 2 ^ (b * w0)) * 2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2) := by
  unfold evalTree
  rw [gv_foldr_map]
  rw [show (tree.map fun nd => gv (evalNd3 S b nd) w3) = (tree.map fun nd =>
      ∑ w2 ∈ range 24, (∑ w1 ∈ range 24, (∑ w0 ∈ range 24, sN3 S nd w0 w1 w2 w3 * 2 ^ (b * w0)) *
        2 ^ (24 * b * w1)) * 2 ^ (576 * b * w2)) from List.map_congr_left fun nd _ => evalNd3_gv S b hS nd w3 hw,
    list_sum_map_sum]
  refine Finset.sum_congr rfl fun w2 _ => ?_
  rw [list_sum_map_mul_right, list_sum_map_sum]
  congr 1
  refine Finset.sum_congr rfl fun w1 _ => ?_
  rw [list_sum_map_mul_right, list_sum_map_sum]
  congr 1
  refine Finset.sum_congr rfl fun w0 _ => ?_
  rw [list_sum_map_mul_right]; rfl

omit hS in
lemma ruleSpec_rows (X : Ctx) (i : Nat) : ∀ m, ((ruleSpec X i).rows m).length = 24 :=
  fun _ => localRows_length _ _

end NPT.Cert.Ident
