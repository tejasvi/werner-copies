/-
NPT.Cert.Ident.Bound — the a-priori bound `|specGrp X G w| ≤ boundGrp X G`.
-/
import NPT.Cert.Ident.Pipe

open BigOperators Finset

namespace NPT.Cert.Ident

lemma SInt.abs_val (a : SInt) : |a.val| = a.mag := by
  rcases a with ⟨_ | _, m⟩ <;> simp [SInt.val]

lemma sum_range_getD_le (l : List Nat) : ∀ n, ∑ k ∈ range n, l.getD k 0 ≤ l.sum := by
  induction l with
  | nil => intro n; simp
  | cons a l ih =>
    intro n
    rcases n with _ | n
    · simp
    · rw [Finset.sum_range_succ']; simp only [List.getD_cons_succ, List.getD_cons_zero, List.sum_cons]
      have := ih n; omega

lemma le_foldr_max {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.mem_cons] at h
    simp only [List.foldr_cons]
    rcases h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma map_mag_getD : ∀ (l : List SInt) (k : Nat), (l.map SInt.mag).getD k 0 = (l.getD k SInt.zero).mag
  | [], k => by simp [SInt.zero]
  | x :: l, 0 => by simp
  | x :: l, k + 1 => by simp only [List.map_cons, List.getD_cons_succ]; exact map_mag_getD l k

lemma getD_mem_of_lt {β : Type} (l : List β) (k : Nat) (d : β) (hk : k < l.length) : l.getD k d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem hk

lemma aval_abs_sum_le (A : List (List SInt)) (w n : Nat) (hw : w < A.length) :
    ∑ k ∈ range n, |aval A w k| ≤ (rowAbs A : Int) := by
  have h1 : ∑ k ∈ range n, |aval A w k| = ((∑ k ∈ range n, ((A.getD w []).map SInt.mag).getD k 0 : Nat) : Int) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [aval, SInt.abs_val, map_mag_getD]
  rw [h1]
  have h2 := sum_range_getD_le ((A.getD w []).map SInt.mag) n
  have h3 : ((A.getD w []).map SInt.mag).sum ≤ rowAbs A := by
    unfold rowAbs
    apply le_foldr_max
    exact List.mem_map.2 ⟨A.getD w [], getD_mem_of_lt A w [] hw, rfl⟩
  exact_mod_cast le_trans h2 h3

lemma gv_abs_le (T : List SInt) (j : Nat) : |gv T j| ≤ (maxAbs T : Int) := by
  rw [gv, SInt.abs_val]
  rcases Nat.lt_or_ge j T.length with hj | hj
  · have : (T.getD j SInt.zero).mag ≤ maxAbs T := by
      unfold maxAbs; apply le_foldr_max
      exact List.mem_map.2 ⟨T.getD j SInt.zero, getD_mem_of_lt T j _ hj, rfl⟩
    exact_mod_cast this
  · rw [getD_zero_of_le _ _ hj]; simp [SInt.zero]

/-- `|Σ_k a_k x_k| ≤ (Σ_k |a_k|) · B` if all `|x_k| ≤ B`. -/
lemma abs_sum_mul_le (n : Nat) (a x : Nat → Int) (B : Int) (hx : ∀ k < n, |x k| ≤ B) :
    |∑ k ∈ range n, a k * x k| ≤ (∑ k ∈ range n, |a k|) * B := by
  calc |∑ k ∈ range n, a k * x k| ≤ ∑ k ∈ range n, |a k * x k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range n, |a k| * B := Finset.sum_le_sum fun k hk => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hx k (Finset.mem_range.1 hk)) (abs_nonneg _)
    _ = (∑ k ∈ range n, |a k|) * B := by rw [Finset.sum_mul]

lemma abs_list_sum_le {α : Type*} (L : List α) (f : α → Int) (g : α → Nat) (h : ∀ x ∈ L, |f x| ≤ g x) :
    |(L.map f).sum| ≤ ((L.map g).sum : Int) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    calc |f a + (L.map f).sum| ≤ |f a| + |(L.map f).sum| := abs_add_le _ _
      _ ≤ g a + ((L.map g).sum : Int) := add_le_add (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

variable (S : Spec) (hS : ∀ m, (S.rows m).length = 24)
include hS

lemma sL_abs (m1 m2 m3 : Nat) (lf : Leaf) (w0 j : Nat) (hw : w0 < 24) :
    |sL S m1 m2 m3 lf w0 j| ≤ (boundLeaf S m1 m2 m3 lf : Int) := by
  unfold sL boundLeaf
  rw [Nat.cast_mul]
  calc _ ≤ (∑ k ∈ range (S.dimsq lf.m0), |aval (S.rows lf.m0) w0 k|) * (maxAbs (S.leaf m1 m2 m3 lf) : Int) :=
        abs_sum_mul_le _ _ _ _ fun k _ => gv_abs_le _ _
    _ ≤ (rowAbs (S.rows lf.m0) : Int) * maxAbs (S.leaf m1 m2 m3 lf) :=
        mul_le_mul_of_nonneg_right (aval_abs_sum_le _ _ _ (by rw [hS]; exact hw)) (by positivity)

lemma sN1_abs (m2 m3 : Nat) (nd : Nd1) (w0 w1 j : Nat) (hw0 : w0 < 24) (hw1 : w1 < 24) :
    |sN1 S m2 m3 nd w0 w1 j| ≤ (boundNd1 S m2 m3 nd : Int) := by
  unfold sN1 boundNd1
  rw [Nat.cast_mul]
  calc _ ≤ (∑ k ∈ range (S.dimsq nd.m1), |aval (S.rows nd.m1) w1 k|) *
        ((nd.kids.map (boundLeaf S nd.m1 m2 m3)).sum : Int) :=
        abs_sum_mul_le _ _ _ _ fun k _ => abs_list_sum_le _ _ _ fun lf _ => sL_abs S hS _ _ _ lf _ _ hw0
    _ ≤ _ := mul_le_mul_of_nonneg_right (aval_abs_sum_le _ _ _ (by rw [hS]; exact hw1)) (by positivity)

lemma sN2_abs (m3 : Nat) (nd : Nd2) (w0 w1 w2 j : Nat) (hw0 : w0 < 24) (hw1 : w1 < 24) (hw2 : w2 < 24) :
    |sN2 S m3 nd w0 w1 w2 j| ≤ (boundNd2 S m3 nd : Int) := by
  unfold sN2 boundNd2
  rw [Nat.cast_mul]
  calc _ ≤ (∑ k ∈ range (S.dimsq nd.m2), |aval (S.rows nd.m2) w2 k|) *
        ((nd.kids.map (boundNd1 S nd.m2 m3)).sum : Int) :=
        abs_sum_mul_le _ _ _ _ fun k _ => abs_list_sum_le _ _ _ fun n1 _ => sN1_abs S hS _ _ n1 _ _ _ hw0 hw1
    _ ≤ _ := mul_le_mul_of_nonneg_right (aval_abs_sum_le _ _ _ (by rw [hS]; exact hw2)) (by positivity)

lemma sN3_abs (nd : Nd3) (w0 w1 w2 w3 : Nat) (hw0 : w0 < 24) (hw1 : w1 < 24) (hw2 : w2 < 24) (hw3 : w3 < 24) :
    |sN3 S nd w0 w1 w2 w3| ≤ (boundNd3 S nd : Int) := by
  unfold sN3 boundNd3
  rw [Nat.cast_mul]
  calc _ ≤ (∑ k ∈ range (S.dimsq nd.m3), |aval (S.rows nd.m3) w3 k|) *
        ((nd.kids.map (boundNd2 S nd.m3)).sum : Int) :=
        abs_sum_mul_le _ _ _ _ fun k _ => abs_list_sum_le _ _ _ fun n2 _ => sN2_abs S hS _ n2 _ _ _ _ hw0 hw1 hw2
    _ ≤ _ := mul_le_mul_of_nonneg_right (aval_abs_sum_le _ _ _ (by rw [hS]; exact hw3)) (by positivity)

/-- **A-priori bound** on a box tree's word values. -/
lemma specTree_abs (tree : List Nd3) (w0 w1 w2 w3 : Nat) (hw0 : w0 < 24) (hw1 : w1 < 24) (hw2 : w2 < 24)
    (hw3 : w3 < 24) : |specTree S tree w0 w1 w2 w3| ≤ (boundTree S tree : Int) := by
  unfold specTree boundTree
  exact abs_list_sum_le _ _ _ fun nd _ => sN3_abs S hS nd _ _ _ _ hw0 hw1 hw2 hw3

end NPT.Cert.Ident
