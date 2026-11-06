/-
NPT.Cert.EP3D3.KBoundW — the bounds of `KBound` for the 1200-bit moduli `psW` (width `bW`) of families 0 and 1, in the forms of the hypotheses `hBp`, `hFmod` of `KAssembly.hsumK_f0` / `hsumK_f1`, stated with
`eqLocF cert` (`= eqTK eqTabsK cert` by `KEqOK.eqTK_eqLocF`); `hB` is `KBound.wordBound_f<f>` (`KB = 2^5487`):
* `wordBound_prodW` (`hBp`): `24 · slen · KB < ∏ psW`;
* `wordBoundModW_f<f>` (`hFmod`): for every `p ∈ psW` (all `≤ 2^1200`), every reduced word value is below `2^(bW − 1)`
  (`crudeBMod`, about `2^1351`).
-/
import NPT.Cert.EP3D3.KBound
import NPT.Cert.EP3D3.KPrimesW
set_option maxRecDepth 100000

open NPT.Cert.Ident NPT.Cert.Sem

namespace NPT.Cert.EP3D3

theorem wordBound_prodW : 24 * slen * KB < psW.prod := by decide +kernel

theorem psW_pos_le : ∀ p ∈ psW, 0 < p ∧ p ≤ 2 ^ 1200 := by decide +kernel

theorem crudeBMod_ltW_f0 : crudeBMod cert 0 gs0 zsT zaT (2 ^ 1200) < 2 ^ (bW - 1) := by decide +kernel
theorem crudeBMod_ltW_f1 : crudeBMod cert 1 gs1 zsT zaT (2 ^ 1200) < 2 ^ (bW - 1) := by decide +kernel

theorem wordBoundModW_f0 : ∀ p ∈ psW, ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
    |partsF (famPartsMod p zmul cert 0 gs0 zsT zaT (eqLocF cert)) w0 w1 w2 w3| < 2 ^ (bW - 1) :=
  fun p hp w0 w1 w2 w3 h0 h1 h2 h3 =>
    lt_of_le_of_lt (partsF_le_crudeBMod_eqLocF p zmul cert 0 gs0 zsT zaT _ (psW_pos_le p hp).1 (psW_pos_le p hp).2
      w0 w1 w2 w3 h0 h1 h2 h3) (by exact_mod_cast crudeBMod_ltW_f0)

theorem wordBoundModW_f1 : ∀ p ∈ psW, ∀ w0 w1 w2 w3, w0 < 24 → w1 < 24 → w2 < 24 → w3 < 24 →
    |partsF (famPartsMod p zmul cert 1 gs1 zsT zaT (eqLocF cert)) w0 w1 w2 w3| < 2 ^ (bW - 1) :=
  fun p hp w0 w1 w2 w3 h0 h1 h2 h3 =>
    lt_of_le_of_lt (partsF_le_crudeBMod_eqLocF p zmul cert 1 gs1 zsT zaT _ (psW_pos_le p hp).1 (psW_pos_le p hp).2
      w0 w1 w2 w3 h0 h1 h2 h3) (by exact_mod_cast crudeBMod_ltW_f1)

end NPT.Cert.EP3D3
