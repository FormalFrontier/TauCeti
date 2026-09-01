/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

/-!
# Normalized absolute values on number-field completions

The finite and infinite completions of a number field carry their usual norm, but the global
product formula uses the normalized local absolute value: the norm at a real place and the square
of the norm at a complex place.  This file packages those values as multiplicative maps with zero.

At a finite place the required map is already Mathlib's `normHom` on `v.adicCompletion K`, and its
comparison with `HeightOneSpectrum.adicAbv` is Mathlib's `FinitePlace.norm_embedding`.  The new
infinite-place map is the norm on `w.Completion` raised to `w.mult`.  The latter exponent is one at
real places and two at complex places, so its restriction to the number field agrees with the
normalization used by `NumberField.prod_abs_eq_one`.  These completion-side maps are the local
factors used by the global idele norm; the single all-places carrier is developed separately.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II.
-/

public section
noncomputable section

namespace TauCeti.GlobalNumberFields

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped WithZero

variable {K : Type*} [Field K]

section Infinite

/-- The normalized absolute value on the completion at an infinite place. -/
def infiniteCompletionNormalizedAbsValue (w : InfinitePlace K) : w.Completion →*₀ ℝ :=
  (powMonoidWithZeroHom (InfinitePlace.mult_ne_zero (w := w))).comp normHom

/-- Evaluating the normalized absolute value at `x` gives `‖x‖ ^ w.mult`. -/
@[simp]
theorem infiniteCompletionNormalizedAbsValue_apply (w : InfinitePlace K) (x : w.Completion) :
    infiniteCompletionNormalizedAbsValue w x = ‖x‖ ^ w.mult :=
  (rfl)

private lemma norm_algebraMap_infinitePlace_completion (w : InfinitePlace K) (x : K) :
    ‖algebraMap K w.Completion x‖ = w x := by
  -- `algebraMap_apply` hides the `WithAbs` synonym used by the completion construction.
  change ‖(WithAbs.toAbs w.1 x : w.Completion)‖ = w x
  exact InfinitePlace.Completion.norm_coe w (WithAbs.toAbs w.1 x)

/-- On the dense copy of `K`, the infinite completion value is the normalized
infinite-place value. -/
theorem infiniteCompletionNormalizedAbsValue_algebraMap (w : InfinitePlace K) (x : K) :
    infiniteCompletionNormalizedAbsValue w (algebraMap K w.Completion x) = w x ^ w.mult := by
  rw [infiniteCompletionNormalizedAbsValue_apply, norm_algebraMap_infinitePlace_completion]

/-- On the dense copy of `K`, a real place contributes its ordinary absolute value. -/
theorem infiniteCompletionNormalizedAbsValue_algebraMap_of_isReal
    (w : InfinitePlace K) (hw : w.IsReal) (x : K) :
    infiniteCompletionNormalizedAbsValue w (algebraMap K w.Completion x) = w x := by
  rw [infiniteCompletionNormalizedAbsValue_algebraMap, hw.mult_eq_one, pow_one]

/-- On the dense copy of `K`, a complex place contributes the square of its absolute value. -/
theorem infiniteCompletionNormalizedAbsValue_algebraMap_of_isComplex
    (w : InfinitePlace K) (hw : w.IsComplex) (x : K) :
    infiniteCompletionNormalizedAbsValue w (algebraMap K w.Completion x) = w x ^ 2 := by
  rw [infiniteCompletionNormalizedAbsValue_algebraMap, hw.mult_eq_two]

/-- At a real place the completion value is the ordinary absolute value. -/
theorem infiniteCompletionNormalizedAbsValue_of_isReal
    (w : InfinitePlace K) (hw : w.IsReal) (x : w.Completion) :
    infiniteCompletionNormalizedAbsValue w x = ‖x‖ := by
  rw [infiniteCompletionNormalizedAbsValue_apply, hw.mult_eq_one, pow_one]

/-- At a complex place the completion value is the square of the ordinary absolute value. -/
theorem infiniteCompletionNormalizedAbsValue_of_isComplex
    (w : InfinitePlace K) (hw : w.IsComplex) (x : w.Completion) :
    infiniteCompletionNormalizedAbsValue w x = ‖x‖ ^ 2 := by
  rw [infiniteCompletionNormalizedAbsValue_apply, hw.mult_eq_two]

/-- The infinite completion value is continuous. -/
theorem continuous_infiniteCompletionNormalizedAbsValue (w : InfinitePlace K) :
    Continuous (infiniteCompletionNormalizedAbsValue w : w.Completion → ℝ) := by
  -- `Continuous` does not simplify through the coercion of the bundled hom, so explicitly
  -- identify its underlying function using the pointwise evaluation theorem.
  convert continuous_norm.pow w.mult using 1
  ext x
  exact infiniteCompletionNormalizedAbsValue_apply w x

/-- The infinite completion value vanishes exactly at zero. -/
theorem infiniteCompletionNormalizedAbsValue_eq_zero_iff
    (w : InfinitePlace K) (x : w.Completion) :
    infiniteCompletionNormalizedAbsValue w x = 0 ↔ x = 0 := by
  simp [infiniteCompletionNormalizedAbsValue, InfinitePlace.mult_ne_zero]

end Infinite

end TauCeti.GlobalNumberFields
