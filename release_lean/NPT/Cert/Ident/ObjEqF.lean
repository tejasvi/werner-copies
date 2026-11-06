/-
NPT.Cert.Ident.ObjEqF — objective traces and equality local maps on flat indices (for the
identity fact): computable integer forms `trF`, `trMulF`, `eqLocF`, proved equal to `Matrix.trace` of `VG`,
`VG·VG` and to `Sem.CertD.eqLoc`.
* `trF`, `trMulF`: counts of digit strings `a` with `a = a ∘ σ` (`V_p[a; b] = [a = b ∘ p⁻¹]`).
* `eqLocF`, kind 0 (`del`): when `(slot, order)` describe a traced slot with its survivors (`SOk`, decidable),
  `Σ_{a : 4 digits} [a sl = a (p sl)] J[a ∘ ord][μ] J[a ∘ p ∘ ord][ν]` (`n^4` terms; the traced digit and the
  column index are forced); otherwise the brute-force sum over `(x, y, z)`. Kind 1 (`stiefel_aux`, `n = 2`):
  brute force over `16 × 16` digit strings.
-/
import NPT.Cert.Ident.KmatF

open BigOperators Finset Matrix NPT.Cert.Sem NPT.Brauer

namespace NPT.Cert.Ident

/-! ### Traces -/

/-- Number of digit strings `a` (flat index `k < n^4`) with `a = a ∘ σ`. -/
def fixF (n : ℕ) (σ : Fin 4 → Fin 4) : ℤ :=
  ∑ k ∈ range (n ^ 4), if (List.finRange 4).all (fun s => dgt n 4 k s.val == dgt n 4 k (σ s).val) then 1 else 0

def trF (n : ℕ) (p : Fin 24) : ℤ := fixF n (pinvf p)

def trMulF (n : ℕ) (p q : Fin 24) : ℤ := fixF n (pinvf p ∘ pinvf q)

lemma fix_iff {n : ℕ} [NeZero n] (σ : Fin 4 → Fin 4) (k : ℕ) :
    ((List.finRange 4).all fun s => dgt n 4 k s.val == dgt n 4 k (σ s).val) = true ↔
      unflat n 4 k = unflat n 4 k ∘ σ := by
  rw [List.all_eq_true, funext_iff]
  constructor
  · intro h s
    have := h s (List.mem_finRange s)
    rw [beq_iff_eq] at this
    exact Fin.ext this
  · intro h s _
    rw [beq_iff_eq]
    exact congrArg Fin.val (h s)

lemma fixF_eq (n : ℕ) [NeZero n] (σ : Fin 4 → Fin 4) :
    (fixF n σ : ℚ) = ∑ a : Fin 4 → Fin n, if a = a ∘ σ then 1 else 0 := by
  rw [sum_fun_range]
  unfold fixF
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : unflat n 4 k = unflat n 4 k ∘ σ
  · rw [ite_eq_left ((fix_iff σ k).2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((fix_iff σ k).1 h')), ite_eq_right h]

lemma trF_eq (n : ℕ) [NeZero n] (p : Fin 24) : (trF n p : ℚ) = Matrix.trace (NPT.Brauer.VG ℚ n 0 p) := by
  rw [trF, fixF_eq]
  simp only [Matrix.trace, Matrix.diag, VG0_apply]

lemma trMulF_eq (n : ℕ) [NeZero n] (p q : Fin 24) :
    (trMulF n p q : ℚ) = Matrix.trace (NPT.Brauer.VG ℚ n 0 p * NPT.Brauer.VG ℚ n 0 q) := by
  rw [trMulF, fixF_eq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, VG0_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (b ∘ pinvf p)]
  · simp only [ite_true, one_mul, Function.comp_assoc]
  · intro a _ ha
    rw [ite_eq_right ha, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### Flat sandwiches -/

/-- `(Jᵀ M J)[μ, ν]` as a double sum over flat indices. -/
lemma sandwich_flat {n m : ℕ} [NeZero n] (J : List (List Int)) (dim : ℕ)
    (M : Matrix (Fin m → Fin n) (Fin m → Fin n) ℚ) (μ ν : Fin dim) :
    ((Jm n m J dim)ᵀ * M * Jm n m J dim) μ ν =
      ∑ xi ∈ range (n ^ m), ∑ yi ∈ range (n ^ m),
        ((J.getD xi []).getD μ.val 0 : ℚ) * M (unflat n m xi) (unflat n m yi) *
          ((J.getD yi []).getD ν.val 0 : ℚ) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm, sum_fun_range]
  refine Finset.sum_congr rfl fun xi hxi => ?_
  rw [sum_fun_range]
  refine Finset.sum_congr rfl fun yi hyi => ?_
  have hx : flat (unflat n m xi) = xi := flat_unflat xi (Finset.mem_range.1 hxi)
  have hy : flat (unflat n m yi) = yi := flat_unflat yi (Finset.mem_range.1 hyi)
  simp only [Jm, hx, hy]

/-! ### Kind 1: the Stiefel contrast at `n = 2` (brute force) -/

/-- Entry `[i; j]` of `stief slot (V_p)`. -/
def stiefE (slot : ℕ) (p : Fin 24) (i j : Fin 4 → Fin 2) : ℤ :=
  2 * (if i = j ∘ pinvf p then 1 else 0) -
    (if i (Fin.ofNat 4 slot) = j (Fin.ofNat 4 slot) then
      ∑ z : Fin 2, if insAt slot (natOrder slot) (restr slot i) z =
        insAt slot (natOrder slot) (restr slot j) z ∘ pinvf p then 1 else 0
    else 0)

def stiefF (J : List (List Int)) (slot : ℕ) (p : Fin 24) (μ ν : ℕ) : ℤ :=
  ∑ ii ∈ range (2 ^ 4), ∑ jj ∈ range (2 ^ 4),
    (J.getD ii []).getD μ 0 * stiefE slot p (unflat 2 4 ii) (unflat 2 4 jj) * (J.getD jj []).getD ν 0

lemma stiefE_eq (slot : ℕ) (p : Fin 24) (i j : Fin 4 → Fin 2) :
    (stiefE slot p i j : ℚ) = stief slot (VG ℚ 2 0 p) i j := by
  simp only [stiefE, stief, trSlot, VG0_apply]
  push_cast
  try rfl

lemma stief_flat (J : List (List Int)) (dim : ℕ) (slot : ℕ) (p : Fin 24) (μ ν : Fin dim) :
    ((Jm 2 4 J dim)ᵀ * stief slot (VG ℚ 2 0 p) * Jm 2 4 J dim) μ ν = (stiefF J slot p μ ν : ℚ) := by
  rw [sandwich_flat]
  simp only [stiefF, ← stiefE_eq]
  push_cast
  try rfl

/-! ### Kind 0: the partial trace -/

/-- Entry `[x; y]` of `trSlot slot order (V_p)` (brute force over the traced digit). -/
def trE (slot : ℕ) (order : List ℕ) (n : ℕ) (p : Fin 24) (x y : Fin 3 → Fin n) : ℤ :=
  ∑ z : Fin n, if insAt slot order x z = insAt slot order y z ∘ pinvf p then 1 else 0

/-- Brute-force `del` entry (`n^7` terms). -/
def delB (J : List (List Int)) (slot : ℕ) (order : List ℕ) (n : ℕ) [NeZero n] (p : Fin 24) (μ ν : ℕ) : ℤ :=
  ∑ xi ∈ range (n ^ 3), ∑ yi ∈ range (n ^ 3),
    (J.getD xi []).getD μ 0 * trE slot order n p (unflat n 3 xi) (unflat n 3 yi) * (J.getD yi []).getD ν 0

lemma trE_eq {n : ℕ} [NeZero n] (slot : ℕ) (order : List ℕ) (p : Fin 24) (x y : Fin 3 → Fin n) :
    (trE slot order n p x y : ℚ) = trSlot slot order (VG ℚ n 0 p) x y := by
  simp only [trE, trSlot, VG0_apply]
  push_cast
  try rfl

lemma del_brute (J : List (List Int)) {n : ℕ} [NeZero n] (dim : ℕ) (slot : ℕ) (order : List ℕ) (p : Fin 24)
    (μ ν : Fin dim) :
    ((Jm n 3 J dim)ᵀ * trSlot slot order (VG ℚ n 0 p) * Jm n 3 J dim) μ ν = (delB J slot order n p μ ν : ℚ) := by
  rw [sandwich_flat]
  simp only [delB, ← trE_eq]
  push_cast
  try rfl

/-- The traced slot. -/
def sF (slot : ℕ) : Fin 4 := Fin.ofNat 4 slot
/-- Survivor `u` sits at replica `oF order u`. -/
def oF (order : List ℕ) (u : Fin 3) : Fin 4 := Fin.ofNat 4 (order.getD u.val 0)
/-- Replica `t` is survivor `iF order t` (`Sem.insAt`'s lookup). -/
def iF (order : List ℕ) (t : Fin 4) : Fin 3 := Fin.ofNat 3 (order.idxOf t.val)

/-- `(slot, order)` describe a traced slot `< 4` with its three survivors in some order. -/
def SOk (slot : ℕ) (order : List ℕ) : Prop :=
  slot < 4 ∧ (∀ u, oF order u ≠ sF slot) ∧ (∀ u, iF order (oF order u) = u) ∧
    (∀ t, t ≠ sF slot → oF order (iF order t) = t)

instance (slot : ℕ) (order : List ℕ) : Decidable (SOk slot order) := by unfold SOk; infer_instance

section Split

variable {slot : ℕ} {order : List ℕ}

/-- `a ↦ (a sl, a ∘ ord)`. -/
def splitE (h : SOk slot order) {n : ℕ} : (Fin 4 → Fin n) ≃ Fin n × (Fin 3 → Fin n) where
  toFun a := (a (sF slot), a ∘ oF order)
  invFun zy t := if t = sF slot then zy.1 else zy.2 (iF order t)
  left_inv a := by
    funext t
    by_cases ht : t = sF slot
    · simp [ht]
    · simp [ht, h.2.2.2 t ht]
  right_inv zy := by
    obtain ⟨z, y⟩ := zy
    refine Prod.ext (by simp) ?_
    funext u
    simp [h.2.1 u, h.2.2.1 u]

lemma insAt_splitE (h : SOk slot order) {n : ℕ} (x : Fin 3 → Fin n) (z : Fin n) :
    insAt slot order x z = (splitE h).symm (z, x) := by
  funext t
  show (if t.val = slot then z else x (Fin.ofNat 3 (order.idxOf t.val))) =
    (if t = sF slot then z else x (iF order t))
  have ht : t.val = slot ↔ t = sF slot := by
    constructor
    · intro e; apply Fin.ext; show t.val = slot % 4; rw [Nat.mod_eq_of_lt h.1, e]
    · intro e; rw [e]; show slot % 4 = slot; exact Nat.mod_eq_of_lt h.1
  by_cases h' : t = sF slot
  · rw [ite_eq_left (ht.2 h'), ite_eq_left h']
  · rw [ite_eq_right (fun e => h' (ht.1 e)), ite_eq_right h']
    rfl

lemma splitE_symm_eq_iff (h : SOk slot order) {n : ℕ} (z : Fin n) (y : Fin 3 → Fin n) (b : Fin 4 → Fin n) :
    (splitE h).symm (z, y) = b ↔ z = b (sF slot) ∧ y = b ∘ oF order := by
  rw [Equiv.symm_apply_eq]
  show (z, y) = (b (sF slot), b ∘ oF order) ↔ _
  exact Iff.of_eq (Prod.mk.injEq _ _ _ _)

end Split

lemma comp_pinvf_iff {n : ℕ} (p : Fin 24) (a b : Fin 4 → Fin n) : a = b ∘ pinvf p ↔ b = a ∘ pf p := by
  constructor
  · rintro rfl; funext u; simp [pinvf_pf]
  · rintro rfl; funext u; simp [pf_pinvf]

/-- Fast `del` entry (`n^4` terms), valid when `SOk slot order`. -/
def delFast (J : List (List Int)) (slot : ℕ) (order : List ℕ) (n : ℕ) [NeZero n] (p : Fin 24) (μ ν : ℕ) : ℤ :=
  ∑ k ∈ range (n ^ 4),
    if unflat n 4 k (sF slot) = unflat n 4 k (pf p (sF slot)) then
      (J.getD (flat (unflat n 4 k ∘ oF order)) []).getD μ 0 *
        (J.getD (flat (unflat n 4 k ∘ pf p ∘ oF order)) []).getD ν 0
    else 0

lemma del_fast {slot : ℕ} {order : List ℕ} (h : SOk slot order) (J : List (List Int)) {n : ℕ} [NeZero n]
    (dim : ℕ) (p : Fin 24) (μ ν : Fin dim) :
    ((Jm n 3 J dim)ᵀ * trSlot slot order (VG ℚ n 0 p) * Jm n 3 J dim) μ ν =
      (delFast J slot order n p μ ν : ℚ) := by
  set Jq := Jm n 3 J dim
  -- the entry as a triple sum
  have e1 : ((Jq)ᵀ * trSlot slot order (VG ℚ n 0 p) * Jq) μ ν =
      ∑ x : Fin 3 → Fin n, ∑ z : Fin n, ∑ y : Fin 3 → Fin n,
        Jq x μ * (Jq y ν * if (splitE h).symm (z, y) = (splitE h).symm (z, x) ∘ pf p then 1 else 0) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, trSlot, VG0_apply, insAt_splitE h, comp_pinvf_iff,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  -- reindex `(z, x) ↦ a = (splitE h).symm (z, x)`
  have e2 : ∑ x : Fin 3 → Fin n, ∑ z : Fin n, ∑ y : Fin 3 → Fin n,
        Jq x μ * (Jq y ν * if (splitE h).symm (z, y) = (splitE h).symm (z, x) ∘ pf p then 1 else 0) =
      ∑ a : Fin 4 → Fin n, ∑ y : Fin 3 → Fin n,
        Jq (a ∘ oF order) μ * (Jq y ν * if (splitE h).symm (a (sF slot), y) = a ∘ pf p then 1 else 0) := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type']
    refine (Fintype.sum_equiv (splitE h) _ _ fun a => ?_).symm
    show _ = ∑ y : Fin 3 → Fin n, Jq (a ∘ oF order) μ *
      (Jq y ν * if (splitE h).symm (a (sF slot), y) = (splitE h).symm (splitE h a) ∘ pf p then 1 else 0)
    rw [Equiv.symm_apply_apply]
  -- the column index and the traced digit are forced
  have e3 : ∀ a : Fin 4 → Fin n, ∑ y : Fin 3 → Fin n,
        Jq (a ∘ oF order) μ * (Jq y ν * if (splitE h).symm (a (sF slot), y) = a ∘ pf p then 1 else 0) =
      if a (sF slot) = a (pf p (sF slot)) then Jq (a ∘ oF order) μ * Jq (a ∘ pf p ∘ oF order) ν else 0 := by
    intro a
    simp only [splitE_symm_eq_iff h, Function.comp_apply]
    by_cases ha : a (sF slot) = a (pf p (sF slot))
    · rw [ite_eq_left ha]
      simp only [ha, true_and, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ite_true]
      rfl
    · rw [ite_eq_right ha]
      simp only [ha, false_and, ite_false, mul_zero, Finset.sum_const_zero]
  rw [e1, e2, Finset.sum_congr rfl fun a _ => e3 a, sum_fun_range]
  unfold delFast
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rfl

/-! ### Equality local maps -/

/-- Equality local map entry on flat indices (`Sem.CertD.eqLoc`). -/
def eqLocF (C : NPT.Cert.Sem.CertD) (sp : NPT.Cert.Sem.EqSpecD) (n : ℕ) (p : Fin 24) (o : ℕ) : ℤ :=
  let dec := C.eqDecode sp.mkeys o
  let md := C.mods.getD (sp.mkeys.getD dec.1 0) default
  if dec.2.1 < md.dim then if dec.2.2 < md.dim then
    if sp.kind = 0 then
      if hn : n = 0 then 0 else
        haveI : NeZero n := ⟨hn⟩
        if SOk sp.slot sp.order then delFast md.J sp.slot sp.order n p dec.2.1 dec.2.2
        else delB md.J sp.slot sp.order n p dec.2.1 dec.2.2
    else stiefF md.J sp.slot p dec.2.1 dec.2.2
  else 0 else 0

-- `hkind` (from the spec) is not needed: the kind-1 branch of `eqLoc` does not depend on `n`.
set_option linter.unusedVariables false in
lemma eqLocF_eq (C : NPT.Cert.Sem.CertD) (sp : NPT.Cert.Sem.EqSpecD) (n : ℕ) [NeZero n] (p : Fin 24) (o : ℕ)
    (hkind : sp.kind = 0 ∨ n = 2) : (eqLocF C sp n p o : ℚ) = C.eqLoc sp n p o := by
  unfold eqLocF CertD.eqLoc
  dsimp only
  generalize C.eqDecode sp.mkeys o = dec
  generalize C.mods.getD (sp.mkeys.getD dec.1 0) default = md
  split_ifs with hμ hν hk hn hso
  · exact absurd hn (NeZero.ne n)
  · exact (del_fast hso md.J (n := n) md.dim p ⟨dec.2.1, hμ⟩ ⟨dec.2.2, hν⟩).symm
  · exact (del_brute md.J (n := n) md.dim sp.slot sp.order p ⟨dec.2.1, hμ⟩ ⟨dec.2.2, hν⟩).symm
  · exact (stief_flat md.J md.dim sp.slot p ⟨dec.2.1, hμ⟩ ⟨dec.2.2, hν⟩).symm
  · simp
  · simp

end NPT.Cert.Ident

#print axioms NPT.Cert.Ident.trF_eq
#print axioms NPT.Cert.Ident.trMulF_eq
#print axioms NPT.Cert.Ident.eqLocF_eq
