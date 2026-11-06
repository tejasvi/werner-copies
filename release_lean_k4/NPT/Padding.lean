/-
NPT.Padding — zero padding: an operator on copies of `ℂ^{d'}` embeds into copies of `ℂ^d` (`d' ≤ d`)
with the same rank bound and the same value of `q`. Hence `EP ι d t → EP ι d' t`.
-/
import NPT.Basic

open Matrix BigOperators Finset

namespace NPT

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d' d : ℕ}

/-- Embedding of multi-indices `Idx ι d' → Idx ι d` (coordinatewise `Fin.castLE`). -/
def emb (h : d' ≤ d) (x : Idx ι d') : Idx ι d := fun i => Fin.castLE h (x i)

lemma emb_injective (h : d' ≤ d) : Function.Injective (emb (ι := ι) h) := by
  intro x y hxy
  funext i
  have := congrFun hxy i
  exact Fin.ext (by simpa [emb, Fin.castLE] using this)

/-- `x` has all coordinates below `d'`. -/
def InRange (d' : ℕ) (x : Idx ι d) : Prop := ∀ i, (x i).val < d'

instance (x : Idx ι d) : Decidable (InRange d' x) := by unfold InRange; infer_instance

/-- Restriction of an in-range multi-index. -/
def res (x : Idx ι d) (hx : InRange d' x) : Idx ι d' := fun i => ⟨(x i).val, hx i⟩

lemma inRange_emb (h : d' ≤ d) (x : Idx ι d') : InRange d' (emb h x) := fun i => by
  simp [emb, Fin.castLE]

lemma res_emb (h : d' ≤ d) (x : Idx ι d') : res (emb h x) (inRange_emb h x) = x := by
  funext i; simp [res, emb, Fin.castLE]

lemma emb_res (h : d' ≤ d) (x : Idx ι d) (hx : InRange d' x) : emb h (res x hx) = x := by
  funext i; simp [res, emb, Fin.castLE]

/-- Zero padding of an operator. -/
def pad (C : Op ι d') : Op ι d := fun x y =>
  if hxy : InRange d' x ∧ InRange d' y then C (res x hxy.1) (res y hxy.2) else 0

lemma pad_emb (h : d' ≤ d) (C : Op ι d') (x y : Idx ι d') : pad C (emb h x) (emb h y) = C x y := by
  have hx := inRange_emb h x
  have hy := inRange_emb h y
  simp [pad, hx, hy, res_emb]

lemma pad_apply_pos {C : Op ι d'} {x y : Idx ι d} (hx : InRange d' x) (hy : InRange d' y) :
    pad C x y = C (res x hx) (res y hy) := by
  show (if hxy : InRange d' x ∧ InRange d' y then C (res x hxy.1) (res y hxy.2) else 0) = _
  rw [dif_pos ⟨hx, hy⟩]

lemma pad_apply_neg {C : Op ι d'} {x y : Idx ι d} (h : ¬ (InRange d' x ∧ InRange d' y)) :
    pad C x y = 0 := by
  show (if hxy : InRange d' x ∧ InRange d' y then C (res x hxy.1) (res y hxy.2) else 0) = _
  rw [dif_neg h]

/-- A sum over multi-indices of a function vanishing off the range of `emb` reduces to `Idx ι d'`. -/
lemma sum_eq_sum_emb {M : Type*} [AddCommMonoid M] (h : d' ≤ d) (F : Idx ι d → M)
    (hF : ∀ x, ¬ InRange d' x → F x = 0) : ∑ x, F x = ∑ x', F (emb h x') := by
  have hs : (Finset.univ.map ⟨emb (ι := ι) h, emb_injective h⟩) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hs, Finset.sum_map]
  · rfl
  · intro x _ hx
    apply hF
    intro hin
    apply hx
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    exact ⟨res x hin, emb_res h x hin⟩

lemma zeroOn_res [NeZero d'] [NeZero d] (J : Finset ι) (x : Idx ι d) (hx : InRange d' x) :
    ZeroOn J (res x hx) ↔ ZeroOn J x := by
  unfold ZeroOn
  refine forall₂_congr fun i _ => ?_
  constructor
  · intro h0
    have := congrArg Fin.val h0
    exact Fin.ext (by simpa [res] using this)
  · intro h0
    exact Fin.ext (by simp [res, h0])

lemma upd_emb (h : d' ≤ d) (J : Finset ι) (x : Idx ι d) (hx : InRange d' x) (z : J → Fin d') :
    upd J x (fun j => Fin.castLE h (z j)) = emb h (upd J (res x hx) z) := by
  funext i
  by_cases hi : i ∈ J
  · simp [upd, emb, hi]
  · have := congrFun (emb_res h x hx) i
    simp [upd, hi, emb] at this ⊢
    exact this.symm

/-- Partial traces commute with zero padding. -/
lemma ptrace_pad [NeZero d'] [NeZero d] (h : d' ≤ d) (J : Finset ι) (C : Op ι d') :
    ptrace J (pad (d := d) C) = pad (d := d) (ptrace J C) := by
  funext x y
  by_cases hz : ZeroOn J x ∧ ZeroOn J y
  · by_cases hr : InRange d' x ∧ InRange d' y
    · have hz' : ZeroOn J (res x hr.1) ∧ ZeroOn J (res y hr.2) :=
        ⟨(zeroOn_res J x hr.1).2 hz.1, (zeroOn_res J y hr.2).2 hz.2⟩
      rw [ptrace_apply_pos hz, pad_apply_pos hr.1 hr.2, ptrace_apply_pos hz']
      rw [sum_eq_sum_emb (ι := J) h]
      · refine Finset.sum_congr rfl fun z' _ => ?_
        have e1 := upd_emb h J x hr.1 z'
        have e2 := upd_emb h J y hr.2 z'
        have : (emb (ι := J) h z') = (fun j => Fin.castLE h (z' j)) := rfl
        rw [this, e1, e2, pad_emb]
      · intro z hzr
        apply pad_apply_neg
        intro hin
        apply hzr
        intro j
        have := hin.1 j
        simpa [upd, j.2] using this
    · rw [ptrace_apply_pos hz, pad_apply_neg hr]
      refine Finset.sum_eq_zero fun z _ => ?_
      apply pad_apply_neg
      intro hin
      apply hr
      constructor
      · intro i
        by_cases hi : i ∈ J
        · rw [hz.1 i hi]; exact Nat.pos_of_ne_zero (NeZero.ne d')
        · have := hin.1 i; simpa [upd, hi] using this
      · intro i
        by_cases hi : i ∈ J
        · rw [hz.2 i hi]; exact Nat.pos_of_ne_zero (NeZero.ne d')
        · have := hin.2 i; simpa [upd, hi] using this
  · rw [ptrace_apply_neg hz]
    by_cases hr : InRange d' x ∧ InRange d' y
    · have hz' : ¬ (ZeroOn J (res x hr.1) ∧ ZeroOn J (res y hr.2)) := by
        rwa [zeroOn_res, zeroOn_res]
      rw [pad_apply_pos hr.1 hr.2, ptrace_apply_neg hz']
    · rw [pad_apply_neg hr]

/-- Zero padding preserves the Frobenius norm. -/
lemma frobSq_pad (h : d' ≤ d) (A : Op ι d') : frobSq (pad (d := d) A) = frobSq A := by
  unfold frobSq
  rw [sum_eq_sum_emb h]
  · refine Finset.sum_congr rfl fun x' _ => ?_
    rw [sum_eq_sum_emb h]
    · refine Finset.sum_congr rfl fun y' _ => ?_
      rw [pad_emb]
    · intro y hy
      rw [pad_apply_neg (fun hh => hy hh.2), map_zero]
  · intro x hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [pad_apply_neg (fun hh => hx hh.1), map_zero]

/-- Zero padding preserves `q`. -/
theorem q_pad [NeZero d'] [NeZero d] (h : d' ≤ d) (t : ℝ) (C : Op ι d') :
    q t (pad (d := d) C) = q t C := by
  unfold q
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [ptrace_pad h, frobSq_pad h]

/-- Zero padding preserves the rank bound. -/
theorem rank_pad (C : Op ι d') (hC : RankLE2 C) : RankLE2 (pad (d := d) C) := by
  obtain ⟨A, B, rfl⟩ := hC
  refine ⟨Matrix.of fun x r => if hx : InRange d' x then A (res x hx) r else 0,
          Matrix.of fun y r => if hy : InRange d' y then B (res y hy) r else 0, ?_⟩
  ext x y
  rw [Matrix.mul_apply]
  by_cases hx : InRange d' x <;> by_cases hy : InRange d' y
  · rw [pad_apply_pos hx hy, Matrix.mul_apply]
    simp [hx, hy]
  · rw [pad_apply_neg (fun hh => hy hh.2)]
    simp [hy]
  · rw [pad_apply_neg (fun hh => hx hh.1)]
    simp [hx]
  · rw [pad_apply_neg (fun hh => hx hh.1)]
    simp [hx]

/-- Dimension monotonicity: the endpoint property passes from `d` to every `d' ≤ d`. -/
theorem EP_mono_dim [NeZero d'] [NeZero d] (h : d' ≤ d) {t : ℝ} (hEP : EP ι d t) : EP ι d' t := by
  intro C hC
  rw [← q_pad (d := d) h]
  exact hEP _ (rank_pad C hC)

end NPT
