/-
NPT.Cert.Ident.KmatF — local block maps on flat indices: `Sem.Kmat` equals a brute-force sum over
flat digit indices `kmatF`, and `localRowsF` tabulates it (row `p`, entry `μ·dim + ν`).
-/
import NPT.Cert.Ident.Reindex
import NPT.Cert.Ident.Pipe

open BigOperators Finset Matrix NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.Ident

/-- Entries of the permutation operator (cut 0): `V_p[a; b] = [a = b ∘ p⁻¹]`. -/
lemma VG0_apply {n : ℕ} (p : Fin 24) (a b : Fin 4 → Fin n) :
    VG ℚ n 0 p a b = if a = b ∘ pinvf p then 1 else 0 := by
  have hb : bSel 0 p = id := by funext s; simp [bSel, inS]
  have ha : aSel 0 p = pinvf p := by funext s; simp [aSel, inS]
  simp only [VG, SelOp, ha, hb, Matrix.sum_apply, Matrix.single_apply, Function.comp_id]
  rw [Finset.sum_eq_single b]
  · by_cases h : a = b ∘ pinvf p
    · rw [if_pos ⟨h.symm, rfl⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.1.symm), if_neg h]
  · intro x _ hx; rw [if_neg (fun h => hx h.2)]
  · intro h; exact absurd (Finset.mem_univ b) h

/-- Digit `c` of the 8-digit string `(digits xi, digits yi)`. -/
def appDig (n xi yi c : ℕ) : ℕ := if c < 4 then dgt n 4 xi c else dgt n 4 yi (c - 4)

/-- The entry-rule condition on flat indices. -/
def condF (n : ℕ) (kpos lpos : List ℕ) (p : Fin 24) (xi yi : ℕ) : Bool :=
  (List.finRange 4).all fun s =>
    appDig n xi yi ((kpos.getD s.val 0) % 8) == appDig n xi yi ((lpos.getD (pinvf p s).val 0) % 8)

/-- `Σ_{x,y} J[x][μ] J[y][ν] [cond]` on flat indices. -/
def kmatF (n : ℕ) (J : List (List Int)) (kpos lpos : List ℕ) (p : Fin 24) (μ ν : ℕ) : Int :=
  ∑ xi ∈ range (n ^ 4), ∑ yi ∈ range (n ^ 4),
    ((J.getD xi []).getD μ 0 * (J.getD yi []).getD ν 0 * if condF n kpos lpos p xi yi then 1 else 0)

lemma append_unflat_val {n : ℕ} [NeZero n] (xi yi : ℕ) (c : Fin (4 + 4)) :
    (Fin.append (unflat n 4 xi) (unflat n 4 yi) c).val = appDig n xi yi c.val := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) c
  · rw [Fin.append_left]; simp [appDig, unflat, i.isLt]
  · rw [Fin.append_right]
    simp only [appDig, Fin.natAdd, unflat]
    rw [if_neg (by omega), show 4 + i.val - 4 = i.val by omega]

lemma condF_iff {n : ℕ} [NeZero n] (kpos lpos : List ℕ) (p : Fin 24) (xi yi : ℕ) :
    condF n kpos lpos p xi yi = true ↔
      Fin.append (unflat n 4 xi) (unflat n 4 yi) ∘ posOf kpos =
        (Fin.append (unflat n 4 xi) (unflat n 4 yi) ∘ posOf lpos) ∘ pinvf p := by
  rw [condF, List.all_eq_true, funext_iff]
  constructor
  · intro h s
    have := h s (List.mem_finRange s)
    rw [beq_iff_eq] at this
    apply Fin.ext
    simp only [Function.comp_apply, append_unflat_val, posOf, Fin.val_ofNat]
    exact this
  · intro h s _
    rw [beq_iff_eq]
    have := congrArg Fin.val (h s)
    simpa only [Function.comp_apply, append_unflat_val, posOf, Fin.val_ofNat] using this

/-- **`Kmat` on flat indices.** -/
lemma Kmat_eq_kmatF {n : ℕ} [NeZero n] (J : List (List Int)) (dim : ℕ) (kpos lpos : List ℕ) (p : Fin 24)
    (μ ν : Fin dim) : Kmat n J dim kpos lpos p μ ν = (kmatF n J kpos lpos p μ ν : ℚ) := by
  unfold Kmat
  simp only [Matrix.mul_apply, Matrix.transpose_apply, ruleOp, VG0_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [sum_fun_range]
  unfold kmatF
  push_cast
  refine Finset.sum_congr rfl fun xi hxi => ?_
  rw [sum_fun_range]
  refine Finset.sum_congr rfl fun yi hyi => ?_
  have hx : flat (unflat n 4 xi) = xi := flat_unflat xi (Finset.mem_range.1 hxi)
  have hy : flat (unflat n 4 yi) = yi := flat_unflat yi (Finset.mem_range.1 hyi)
  simp only [Jm, hx, hy]
  by_cases hc : condF n kpos lpos p xi yi = true
  · rw [if_pos ((condF_iff kpos lpos p xi yi).1 hc), if_pos hc]; ring
  · rw [if_neg (fun h => hc ((condF_iff kpos lpos p xi yi).2 h)), if_neg hc]; ring

/-- Local rows on flat indices: row `p`, entry `μ·dim + ν` = `kmatF … p μ ν`. -/
def localRowsF (md : ModD) (kpos lpos : List ℕ) : List (List SInt) :=
  (List.finRange 24).map fun p => (List.range (md.dim * md.dim)).map fun k =>
    SInt.ofInt (kmatF md.n md.J kpos lpos p (k / md.dim) (k % md.dim))

lemma localRowsF_length (md : ModD) (kpos lpos : List ℕ) : (localRowsF md kpos lpos).length = 24 := by
  simp [localRowsF]

lemma localRowsF_row (md : ModD) (kpos lpos : List ℕ) (p : Fin 24) :
    (localRowsF md kpos lpos).getD p.val [] = (List.range (md.dim * md.dim)).map fun k =>
      SInt.ofInt (kmatF md.n md.J kpos lpos p (k / md.dim) (k % md.dim)) := by
  unfold localRowsF
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by simp)]
  simp only [Option.map_some, Option.getD_some, List.getElem_finRange]
  rfl

lemma aval_localRowsF (md : ModD) (kpos lpos : List ℕ) (p : Fin 24) (μ ν : ℕ) (hμ : μ < md.dim) (hν : ν < md.dim) :
    aval (localRowsF md kpos lpos) p.val (μ * md.dim + ν) = kmatF md.n md.J kpos lpos p μ ν := by
  have hk : μ * md.dim + ν < md.dim * md.dim := by nlinarith
  unfold aval
  rw [localRowsF_row, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.getD_some]
  rw [SInt.val_ofInt]
  congr 1
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hν, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hν]

lemma aval_localRowsF' (md : ModD) (kpos lpos : List ℕ) (p : Fin 24) (i : ℕ) (hi : i < md.dim * md.dim) :
    aval (localRowsF md kpos lpos) p.val i = kmatF md.n md.J kpos lpos p (i / md.dim) (i % md.dim) := by
  have hd : 0 < md.dim := by
    rcases Nat.eq_zero_or_pos md.dim with h | h
    · rw [h] at hi; simp at hi
    · exact h
  have := aval_localRowsF md kpos lpos p (i / md.dim) (i % md.dim)
    (Nat.div_lt_of_lt_mul hi) (Nat.mod_lt _ hd)
  rwa [Nat.div_add_mod'] at this

end NPT.Cert.Ident
