/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Recovering an ideal from its relative norm

For a finite torsion-free extension `A → B` of Dedekind domains, the relative norm
`Ideal.relNorm A : Ideal B →*₀ Ideal A` is monotone but far from injective. It is, however,
injective on any chain: two nested ideals with the same relative norm are equal.

This is the step that turns a containment obtained from generators into an equality, which is how
norm computations identify an ideal. Mathlib's `Mathlib/RingTheory/Ideal/Norm/RelNorm.lean` has the
ingredients — multiplicativity, `Ideal.relNorm_eq_bot_iff` and `Ideal.relNorm_le_comap` — but not
this consequence.

## Main results

* `Ideal.eq_of_le_of_relNorm_eq`: a containment of ideals of `B` with equal relative norms over `A`
  is an equality.
-/

public section

namespace Ideal

variable {A B : Type*} [CommRing A] [IsDedekindDomain A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B]

/-- **A containment of ideals with equal relative norms is an equality.** -/
theorem eq_of_le_of_relNorm_eq {I J : Ideal B} (hIJ : I ≤ J)
    (hnorm : relNorm A I = relNorm A J) : I = J := by
  rcases eq_or_ne J 0 with rfl | hJne
  · -- `I ≤ 0` leaves no room for `I`.
    simpa [zero_eq_bot, le_bot_iff] using hIJ
  -- `J ∣ I`, so `I = J * C`; cancelling the norms gives `relNorm C = 1`, and an ideal whose norm
  -- is the unit ideal is itself the unit ideal, its norm lying below its contraction.
  obtain ⟨C, hC⟩ := dvd_iff_le.mpr hIJ
  have hJnorm_ne : relNorm A J ≠ 0 := by
    rw [Ne, zero_eq_bot, relNorm_eq_bot_iff, ← zero_eq_bot]; exact hJne
  have hC1 : relNorm A C = 1 := by
    apply mul_left_cancel₀ hJnorm_ne
    rw [mul_one, ← map_mul (relNorm A), ← hC, hnorm]
  have hCtop : C = ⊤ := by
    have hle : (⊤ : Ideal A) ≤ comap (algebraMap A B) C := by
      rw [← one_eq_top, ← hC1]; exact relNorm_le_comap A C
    rw [eq_top_iff_one]
    have := hle (Submodule.mem_top (x := (1 : A)))
    rwa [mem_comap, map_one] at this
  rw [hC, hCtop, mul_top]

end Ideal

end
