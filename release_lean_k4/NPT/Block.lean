/-
NPT.Block — spectator copies: the partial form `Qpart g S C` is a sum, over the spectator indices,
of the form `q g` of rank-≤2 blocks living on the copies in `S`.
-/
import NPT.Interp

open Matrix BigOperators Finset

namespace NPT

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- Copies in `S`. -/
abbrev In (S : Finset ι) := {i // i ∈ S}
/-- Spectator copies. -/
abbrev Out (S : Finset ι) := {i // i ∉ S}

/-- Glue an index on `S` and an index on the spectators. -/
def glue (S : Finset ι) (u : Idx (In S) d) (a : Idx (Out S) d) : Idx ι d :=
  fun i => if h : i ∈ S then u ⟨i, h⟩ else a ⟨i, h⟩

/-- The block of `C` with spectator indices `a, b`. -/
def block (S : Finset ι) (a b : Idx (Out S) d) (C : Op ι d) : Op (In S) d :=
  fun u v => C (glue S u a) (glue S v b)

theorem rank_block (S : Finset ι) (a b : Idx (Out S) d) {C : Op ι d} (hC : RankLE2 C) :
    RankLE2 (block S a b C) := by
  obtain ⟨A, B, rfl⟩ := hC
  refine ⟨Matrix.of fun u r => A (glue S u a) r, Matrix.of fun v r => B (glue S v b) r, ?_⟩
  ext u v
  simp [block, Matrix.mul_apply]

/-- Splitting a multi-index into its `S` and spectator parts is a bijection. -/
def splitEquiv (S : Finset ι) : Idx ι d ≃ Idx (In S) d × Idx (Out S) d where
  toFun x := (fun i => x i.1, fun i => x i.1)
  invFun p := glue S p.1 p.2
  left_inv x := by funext i; by_cases h : i ∈ S <;> simp [glue, h]
  right_inv p := by
    obtain ⟨u, a⟩ := p
    ext i
    · simp [glue, i.2]
    · simp [glue, i.2]

/-- A subset of `S`, seen as a subset of the copies `In S`. -/
def toIn (S J : Finset ι) : Finset (In S) := J.subtype (· ∈ S)

/-- The elements of `J ⊆ S` correspond to those of `toIn S J`. -/
def toInEquiv {S J : Finset ι} (hJS : J ⊆ S) : J ≃ toIn S J where
  toFun i := ⟨⟨i.1, hJS i.2⟩, by simp [toIn, Finset.mem_subtype, i.2]⟩
  invFun i := ⟨i.1.1, by simpa [toIn, Finset.mem_subtype] using i.2⟩
  left_inv i := rfl
  right_inv i := rfl

lemma card_toIn {S J : Finset ι} (hJS : J ⊆ S) : (toIn S J).card = J.card := by
  unfold toIn
  rw [Finset.card_subtype, Finset.filter_true_of_mem (fun i hi => hJS hi)]

lemma zeroOn_toIn_iff [NeZero d] {S J : Finset ι} (hJS : J ⊆ S) (u : Idx (In S) d) (a : Idx (Out S) d) :
    ZeroOn (toIn S J) u ↔ ZeroOn J (glue S u a) := by
  unfold ZeroOn
  constructor
  · intro h i hi
    have := h ⟨i, hJS hi⟩ (by simp [toIn, Finset.mem_subtype, hi])
    simpa [glue, hJS hi] using this
  · intro h i hi
    have hiJ : i.1 ∈ J := by simpa [toIn, Finset.mem_subtype] using hi
    have := h i.1 hiJ
    simpa [glue, i.2] using this

lemma glue_upd {S J : Finset ι} (hJS : J ⊆ S) (u : Idx (In S) d) (a : Idx (Out S) d) (z : J → Fin d) :
    glue S (upd (toIn S J) u (fun i => z ((toInEquiv hJS).symm i))) a = upd J (glue S u a) z := by
  funext i
  by_cases hiJ : i ∈ J
  · have hiS : i ∈ S := hJS hiJ
    have hmem : (⟨i, hiS⟩ : In S) ∈ toIn S J := by simp [toIn, Finset.mem_subtype, hiJ]
    simp [glue, upd, hiS, hiJ, hmem, toInEquiv]
  · by_cases hiS : i ∈ S
    · have hmem : (⟨i, hiS⟩ : In S) ∉ toIn S J := by simp [toIn, Finset.mem_subtype, hiJ]
      simp [glue, upd, hiS, hiJ, hmem]
    · simp [glue, upd, hiS, hiJ]

/-- Partial traces inside `S` commute with taking blocks. -/
lemma ptrace_block [NeZero d] {S J : Finset ι} (hJS : J ⊆ S) (a b : Idx (Out S) d) (C : Op ι d)
    (u v : Idx (In S) d) :
    ptrace (toIn S J) (block S a b C) u v = ptrace J C (glue S u a) (glue S v b) := by
  by_cases hz : ZeroOn J (glue S u a) ∧ ZeroOn J (glue S v b)
  · have hz' : ZeroOn (toIn S J) u ∧ ZeroOn (toIn S J) v :=
      ⟨(zeroOn_toIn_iff hJS u a).2 hz.1, (zeroOn_toIn_iff hJS v b).2 hz.2⟩
    rw [ptrace_apply_pos hz', ptrace_apply_pos hz]
    rw [← Equiv.sum_comp ((toInEquiv hJS).arrowCongr (Equiv.refl (Fin d)))]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hzz : ((toInEquiv hJS).arrowCongr (Equiv.refl (Fin d))) z = fun i => z ((toInEquiv hJS).symm i) := by
      funext i; simp [Equiv.arrowCongr_apply]
    show C (glue S (upd (toIn S J) u (((toInEquiv hJS).arrowCongr (Equiv.refl (Fin d))) z)) a)
        (glue S (upd (toIn S J) v (((toInEquiv hJS).arrowCongr (Equiv.refl (Fin d))) z)) b) = _
    rw [hzz, glue_upd hJS u a z, glue_upd hJS v b z]
  · have hz' : ¬ (ZeroOn (toIn S J) u ∧ ZeroOn (toIn S J) v) := by
      rwa [zeroOn_toIn_iff hJS u a, zeroOn_toIn_iff hJS v b]
    rw [ptrace_apply_neg hz', ptrace_apply_neg hz]

/-- Frobenius norms of partial traces inside `S` split over the spectator indices. -/
lemma frobSq_ptrace_eq_sum_block [NeZero d] {S J : Finset ι} (hJS : J ⊆ S) (C : Op ι d) :
    frobSq (ptrace J C) = ∑ a : Idx (Out S) d, ∑ b : Idx (Out S) d,
      frobSq (ptrace (toIn S J) (block S a b C)) := by
  have hsplit : ∀ F : Idx ι d → ℝ, ∑ x, F x = ∑ u : Idx (In S) d, ∑ a : Idx (Out S) d, F (glue S u a) := by
    intro F
    rw [← Equiv.sum_comp (splitEquiv (d := d) S).symm, Fintype.sum_prod_type]
    rfl
  unfold frobSq
  rw [hsplit]
  simp_rw [hsplit (fun y => Complex.normSq (ptrace J C _ y))]
  simp_rw [← ptrace_block hJS]
  -- Σ_u Σ_a Σ_v Σ_b  =  Σ_a Σ_b Σ_u Σ_v
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ u : Idx (In S) d, ∑ v : Idx (In S) d, ∑ b : Idx (Out S) d,
        Complex.normSq (ptrace (toIn S J) (block S a b C) u v)
      = ∑ u : Idx (In S) d, ∑ b : Idx (Out S) d, ∑ v : Idx (In S) d,
        Complex.normSq (ptrace (toIn S J) (block S a b C) u v) :=
          Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
    _ = ∑ b : Idx (Out S) d, ∑ u : Idx (In S) d, ∑ v : Idx (In S) d,
        Complex.normSq (ptrace (toIn S J) (block S a b C) u v) := Finset.sum_comm

/-- The partial form is a sum of full forms of blocks. -/
theorem Qpart_eq_sum_q_block [NeZero d] (g : ℝ) (S : Finset ι) (C : Op ι d) :
    Qpart g S C = ∑ a : Idx (Out S) d, ∑ b : Idx (Out S) d, q g (block S a b C) := by
  unfold Qpart q
  have h1 : ∑ J ∈ S.powerset, (-g) ^ J.card * frobSq (ptrace J C)
      = ∑ J ∈ S.powerset, ∑ a : Idx (Out S) d, ∑ b : Idx (Out S) d,
          (-g) ^ J.card * frobSq (ptrace (toIn S J) (block S a b C)) := by
    refine Finset.sum_congr rfl fun J hJ => ?_
    rw [frobSq_ptrace_eq_sum_block (Finset.mem_powerset.mp hJ), Finset.mul_sum]
    simp_rw [Finset.mul_sum]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_nbij' (fun J => toIn S J) (fun J' => J'.map ⟨Subtype.val, Subtype.val_injective⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro J _; exact Finset.mem_univ _
  · intro J' _
    simp only [Finset.mem_powerset]
    intro x hx
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  · intro J hJ
    have hJS := Finset.mem_powerset.mp hJ
    ext x
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, toIn, Finset.mem_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hJS hx⟩, hx, rfl⟩
  · intro J' _
    ext x
    simp [toIn, Finset.mem_subtype]
  · intro J hJ
    rw [card_toIn (Finset.mem_powerset.mp hJ)]

/-- Spectator positivity: `EP` on the copies `In S` gives `Qpart g S C ≥ 0`. -/
theorem Qpart_nonneg_of_EP [NeZero d] {g : ℝ} {S : Finset ι} (hEP : EP (In S) d g) {C : Op ι d}
    (hC : RankLE2 C) : 0 ≤ Qpart g S C := by
  rw [Qpart_eq_sum_q_block]
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hEP _ (rank_block S a b hC)

/-- Monotonicity in `t` (Lemma M2): if `EP` holds at `g` on every subset of the copies, it holds at
every `t ∈ [0, g]` on all copies. -/
theorem EP_of_EP_sub [NeZero d] {g t : ℝ} (hg : 0 < g) (ht0 : 0 ≤ t) (htg : t ≤ g)
    (hsub : ∀ S : Finset ι, EP (In S) d g) : EP ι d t := fun C hC =>
  q_nonneg_of_Qpart hg ht0 htg C fun S => Qpart_nonneg_of_EP (hsub S) hC

end NPT
