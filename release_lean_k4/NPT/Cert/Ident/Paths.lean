/-
NPT.Cert.Ident.Paths — the multilinear form of a box tree as a sum over root-to-leaf paths of box forms.
-/
import NPT.Cert.Ident.Pipe

open BigOperators Finset

namespace NPT.Cert.Ident

variable (S : Spec)

/-- The box form of one leaf (path `m3 → m2 → m1 → lf`). -/
def boxF (m1 m2 m3 : ℕ) (lf : Leaf) (w0 w1 w2 w3 : ℕ) : Int :=
  ∑ i0 ∈ range (S.dimsq lf.m0), ∑ i1 ∈ range (S.dimsq m1), ∑ i2 ∈ range (S.dimsq m2), ∑ i3 ∈ range (S.dimsq m3),
    aval (S.rows lf.m0) w0 i0 * aval (S.rows m1) w1 i1 * aval (S.rows m2) w2 i2 * aval (S.rows m3) w3 i3 *
      gv (S.leaf m1 m2 m3 lf) (i0 * (S.dimsq m1 * S.dimsq m2 * S.dimsq m3) +
        (i1 * (S.dimsq m2 * S.dimsq m3) + (i2 * S.dimsq m3 + i3)))

lemma mul_list_sum {α : Type*} (c : Int) (L : List α) (f : α → Int) :
    c * (L.map f).sum = (L.map fun x => c * f x).sum := (List.sum_map_mul_left L f c).symm

lemma sum_list1 {α : Type*} (s : Finset ℕ) (L : List α) (f : α → ℕ → Int) :
    ∑ k ∈ s, (L.map fun x => f x k).sum = (L.map fun x => ∑ k ∈ s, f x k).sum :=
  (list_sum_map_sum L s f).symm

lemma sum_list2 {α β : Type*} (s : Finset ℕ) (L : List α) (K : α → List β) (f : α → β → ℕ → Int) :
    ∑ k ∈ s, (L.map fun x => ((K x).map fun y => f x y k).sum).sum =
      (L.map fun x => ((K x).map fun y => ∑ k ∈ s, f x y k).sum).sum := by
  rw [sum_list1]
  exact congrArg List.sum (List.map_congr_left fun x _ => sum_list1 s (K x) (f x))

lemma sum_list3 {α β γ : Type*} (s : Finset ℕ) (L : List α) (K : α → List β) (M : α → β → List γ)
    (f : α → β → γ → ℕ → Int) :
    ∑ k ∈ s, (L.map fun x => ((K x).map fun y => ((M x y).map fun z => f x y z k).sum).sum).sum =
      (L.map fun x => ((K x).map fun y => ((M x y).map fun z => ∑ k ∈ s, f x y z k).sum).sum).sum := by
  rw [sum_list1]
  exact congrArg List.sum (List.map_congr_left fun x _ => sum_list2 s (K x) (M x) (f x))

/-- `Nd1` level as a list sum over leaves. -/
lemma sN1_eq (m2 m3 : ℕ) (nd : Nd1) (w0 w1 j : ℕ) :
    sN1 S m2 m3 nd w0 w1 j = (nd.kids.map fun lf => ∑ i1 ∈ range (S.dimsq nd.m1), ∑ i0 ∈ range (S.dimsq lf.m0),
      aval (S.rows nd.m1) w1 i1 * (aval (S.rows lf.m0) w0 i0 *
        gv (S.leaf nd.m1 m2 m3 lf) (i0 * (S.dimsq nd.m1 * S.dimsq m2 * S.dimsq m3) +
          (i1 * (S.dimsq m2 * S.dimsq m3) + j)))).sum := by
  unfold sN1
  rw [← sum_list1]
  refine Finset.sum_congr rfl fun i1 _ => ?_
  rw [mul_list_sum]
  exact congrArg List.sum (List.map_congr_left fun lf _ => by unfold sL; rw [Finset.mul_sum])

/-- `Nd2` level as a nested list sum. -/
lemma sN2_eq (m3 : ℕ) (nd : Nd2) (w0 w1 w2 j : ℕ) :
    sN2 S m3 nd w0 w1 w2 j = (nd.kids.map fun n1 => (n1.kids.map fun lf =>
      ∑ i2 ∈ range (S.dimsq nd.m2), ∑ i1 ∈ range (S.dimsq n1.m1), ∑ i0 ∈ range (S.dimsq lf.m0),
      aval (S.rows nd.m2) w2 i2 * (aval (S.rows n1.m1) w1 i1 * (aval (S.rows lf.m0) w0 i0 *
        gv (S.leaf n1.m1 nd.m2 m3 lf) (i0 * (S.dimsq n1.m1 * S.dimsq nd.m2 * S.dimsq m3) +
          (i1 * (S.dimsq nd.m2 * S.dimsq m3) + (i2 * S.dimsq m3 + j)))))).sum).sum := by
  unfold sN2
  rw [← sum_list2]
  refine Finset.sum_congr rfl fun i2 _ => ?_
  rw [mul_list_sum]
  refine congrArg List.sum (List.map_congr_left fun n1 _ => ?_)
  rw [sN1_eq, mul_list_sum]
  exact congrArg List.sum (List.map_congr_left fun lf _ => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i1 _ => by rw [Finset.mul_sum])

/-- `Nd3` level as a nested list sum. -/
lemma sN3_eq (nd : Nd3) (w0 w1 w2 w3 : ℕ) :
    sN3 S nd w0 w1 w2 w3 = (nd.kids.map fun n2 => (n2.kids.map fun n1 => (n1.kids.map fun lf =>
      ∑ i3 ∈ range (S.dimsq nd.m3), ∑ i2 ∈ range (S.dimsq n2.m2), ∑ i1 ∈ range (S.dimsq n1.m1),
      ∑ i0 ∈ range (S.dimsq lf.m0),
      aval (S.rows nd.m3) w3 i3 * (aval (S.rows n2.m2) w2 i2 * (aval (S.rows n1.m1) w1 i1 *
        (aval (S.rows lf.m0) w0 i0 *
        gv (S.leaf n1.m1 n2.m2 nd.m3 lf) (i0 * (S.dimsq n1.m1 * S.dimsq n2.m2 * S.dimsq nd.m3) +
          (i1 * (S.dimsq n2.m2 * S.dimsq nd.m3) + (i2 * S.dimsq nd.m3 + i3))))))).sum).sum).sum := by
  unfold sN3
  rw [← sum_list3]
  refine Finset.sum_congr rfl fun i3 _ => ?_
  rw [mul_list_sum]
  refine congrArg List.sum (List.map_congr_left fun n2 _ => ?_)
  rw [sN2_eq, mul_list_sum]
  refine congrArg List.sum (List.map_congr_left fun n1 _ => ?_)
  rw [mul_list_sum]
  exact congrArg List.sum (List.map_congr_left fun lf _ => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i2 _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i1 _ => by rw [Finset.mul_sum])

lemma sum4_rev (A B C D : Finset ℕ) (f : ℕ → ℕ → ℕ → ℕ → Int) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d = ∑ d ∈ D, ∑ c ∈ C, ∑ b ∈ B, ∑ a ∈ A, f a b c d := by
  calc ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d
      = ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ D, ∑ c ∈ C, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a ∈ A, ∑ d ∈ D, ∑ b ∈ B, ∑ c ∈ C, f a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, f a b c d := Finset.sum_comm
    _ = ∑ d ∈ D, ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, f a b c d :=
        Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d ∈ D, ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, f a b c d := Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d ∈ D, ∑ c ∈ C, ∑ b ∈ B, ∑ a ∈ A, f a b c d :=
        Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- **Paths.** The multilinear form of a tree is the sum of the box forms of its leaves. -/
lemma specTree_paths (tree : List Nd3) (w0 w1 w2 w3 : ℕ) :
    specTree S tree w0 w1 w2 w3 = (tree.map fun n3 => (n3.kids.map fun n2 => (n2.kids.map fun n1 =>
      (n1.kids.map fun lf => boxF S n1.m1 n2.m2 n3.m3 lf w0 w1 w2 w3).sum).sum).sum).sum := by
  unfold specTree
  refine congrArg List.sum (List.map_congr_left fun n3 _ => ?_)
  rw [sN3_eq]
  refine congrArg List.sum (List.map_congr_left fun n2 _ => ?_)
  refine congrArg List.sum (List.map_congr_left fun n1 _ => ?_)
  refine congrArg List.sum (List.map_congr_left fun lf _ => ?_)
  unfold boxF
  rw [sum4_rev]
  refine Finset.sum_congr rfl fun i3 _ => Finset.sum_congr rfl fun i2 _ =>
    Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i0 _ => by ring

end NPT.Cert.Ident
