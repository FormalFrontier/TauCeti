/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

-- `ZMod.coe_int_isUnit_iff_isCoprime` is used only inside the proof below.
import Mathlib.Data.ZMod.Units
import TauCeti.Data.ZMod.Divisibility

/-!
# Reduced integer solutions to linear congruences

A linear congruence with coefficient coprime to its modulus has a solution in the canonical
interval of representatives.

## Main results

* `Int.exists_nonneg_lt_and_dvd_mul_sub`: an integer in `[0, m)` solving
  `a * r ≡ b (mod m)` when `a` is coprime to `m`.
-/

public section

namespace Int

/-- **A reduced integer solution to a linear congruence.** With `a` coprime to `m` there is an
`r` in `[0, m)` solving `a * r ≡ b (mod m)`.

This is `ZMod.exists_dvd_sub_val_mul` repackaged from a residue class into its canonical integer
representative. -/
lemma exists_nonneg_lt_and_dvd_mul_sub (a b : ℤ) (m : ℕ) (hm_pos : 0 < m)
    (ham : Int.gcd a m = 1) :
    ∃ r : ℤ, 0 ≤ r ∧ r < m ∧ (m : ℤ) ∣ a * r - b := by
  have : NeZero m := ⟨hm_pos.ne'⟩
  have hunit : IsUnit ((a : ℤ) : ZMod m) := (ZMod.coe_int_isUnit_iff_isCoprime a m).mpr
    (isCoprime_comm.mp (Int.isCoprime_iff_gcd_eq_one.mpr ham))
  obtain ⟨r, hr⟩ := ZMod.exists_dvd_sub_val_mul m b a hunit
  refine ⟨(r.val : ℤ), Int.natCast_nonneg _, by exact_mod_cast r.val_lt, ?_⟩
  rw [← neg_sub, mul_comm]
  exact dvd_neg.mpr hr

end Int
