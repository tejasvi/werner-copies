/-
NPT.Copies — relabelling the copies. Pulling an operator back along a bijection `e : ι ≃ ι'` of the copy
index types keeps the rank bound and every term of `q` (`Tr_J` becomes `Tr_{e(J)}`), so `EP ι d t` gives
`EP ι' d t`; with `EP_restrict` to two of three copies, `EP_3` gives `EP_2` for `t < 1`.
-/
import NPT.Basic
import NPT.Restrict

open Matrix BigOperators Finset

namespace NPT

section Reindex

variable {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] {d : ℕ}

/-- Pull an operator on the copies `ι'` back to the copies `ι` along `e : ι ≃ ι'`. -/
def reidx (e : ι ≃ ι') (C : Op ι' d) : Op ι d := fun x y => C (x ∘ e.symm) (y ∘ e.symm)

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
lemma rank_reidx (e : ι ≃ ι') {C : Op ι' d} (hC : RankLE2 C) : RankLE2 (reidx e C) := by
  obtain ⟨A, B, rfl⟩ := hC
  refine ⟨Matrix.of fun x r => A (x ∘ e.symm) r, Matrix.of fun y r => B (y ∘ e.symm) r, ?_⟩
  ext x y
  simp [reidx, Matrix.mul_apply]

lemma frobSq_reidx (e : ι ≃ ι') (A : Op ι' d) : frobSq (reidx e A) = frobSq A := by
  unfold frobSq
  exact Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl (Fin d))) _ _ fun x =>
    Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl (Fin d))) _ _ fun y => rfl

/-- The copies in `J`, relabelled by `e`. -/
def subEquiv (e : ι ≃ ι') (J : Finset ι) : J ≃ J.map e.toEmbedding :=
  e.subtypeEquiv fun a => by simp

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
lemma zeroOn_reidx [NeZero d] (e : ι ≃ ι') (J : Finset ι) (v : Idx ι d) :
    ZeroOn (J.map e.toEmbedding) (v ∘ e.symm) ↔ ZeroOn J v := by
  constructor
  · intro h i hi
    simpa using h (e i) (by simpa [Finset.mem_map_equiv] using hi)
  · intro h i' hi'
    exact h _ (Finset.mem_map_equiv.1 hi')

omit [Fintype ι] [Fintype ι'] in
lemma upd_reidx (e : ι ≃ ι') (J : Finset ι) (v : Idx ι d) (z : J → Fin d) :
    upd (J.map e.toEmbedding) (v ∘ e.symm) (z ∘ (subEquiv e J).symm) = upd J v z ∘ e.symm := by
  funext i'
  show (if h : i' ∈ J.map e.toEmbedding then z ((subEquiv e J).symm ⟨i', h⟩) else v (e.symm i')) =
    (if h : e.symm i' ∈ J then z ⟨e.symm i', h⟩ else v (e.symm i'))
  by_cases h : e.symm i' ∈ J
  · rw [dite_eq_left (Finset.mem_map_equiv.2 h), dite_eq_left h]
    rfl
  · rw [dite_eq_right (fun h' => h (Finset.mem_map_equiv.1 h')), dite_eq_right h]

lemma ptrace_reidx [NeZero d] (e : ι ≃ ι') (J : Finset ι) (C : Op ι' d) :
    ptrace J (reidx e C) = reidx e (ptrace (J.map e.toEmbedding) C) := by
  funext x y
  show ptrace J (reidx e C) x y = ptrace (J.map e.toEmbedding) C (x ∘ e.symm) (y ∘ e.symm)
  by_cases hJ : ZeroOn J x ∧ ZeroOn J y
  · rw [ptrace_apply_pos hJ,
      ptrace_apply_pos ⟨(zeroOn_reidx e J x).2 hJ.1, (zeroOn_reidx e J y).2 hJ.2⟩]
    refine Fintype.sum_equiv (Equiv.arrowCongr (subEquiv e J) (Equiv.refl (Fin d))) _ _ fun z => ?_
    show C (upd J x z ∘ e.symm) (upd J y z ∘ e.symm) =
      C (upd (J.map e.toEmbedding) (x ∘ e.symm) (z ∘ (subEquiv e J).symm))
        (upd (J.map e.toEmbedding) (y ∘ e.symm) (z ∘ (subEquiv e J).symm))
    rw [upd_reidx, upd_reidx]
  · rw [ptrace_apply_neg hJ, ptrace_apply_neg]
    rwa [zeroOn_reidx, zeroOn_reidx]

/-- `q` is invariant under relabelling the copies. -/
lemma q_reidx [NeZero d] (e : ι ≃ ι') (t : ℝ) (C : Op ι' d) : q t (reidx e C) = q t C := by
  unfold q
  refine Fintype.sum_equiv (Equiv.finsetCongr e) _ _ fun J => ?_
  rw [ptrace_reidx, frobSq_reidx, Equiv.finsetCongr_apply, Finset.card_map]

end Reindex

/-- The endpoint property is invariant under relabelling the copies. -/
theorem EP_equiv {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] {d : ℕ}
    [NeZero d] (e : ι ≃ ι') {t : ℝ} (h : EP ι d t) : EP ι' d t := by
  intro C hC
  rw [← q_reidx e]
  exact h _ (rank_reidx e hC)

/-- `EP` on three copies gives `EP` on two copies (`t < 1`): restrict to the copies `{0, 1}`. -/
theorem EP2_of_EP3 {d : ℕ} [NeZero d] {t : ℝ} (ht : t < 1) (h : EP (Fin 3) d t) : EP (Fin 2) d t :=
  EP_equiv (Fintype.equivFinOfCardEq (by decide)) (EP_restrict ({0, 1} : Finset (Fin 3)) ht h)

end NPT

#print axioms NPT.EP_equiv
#print axioms NPT.EP2_of_EP3
