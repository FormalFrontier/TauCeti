/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.Theorem
public import TauCeti.Probability.Moments.LaplaceDeterminacy

/-!
# Uniqueness in Bernstein's representation theorem

A completely monotone function on `[0, ∞)` has a unique finite representing measure on `ℝ≥0`.
The existence half is supplied by Bernstein's theorem, while uniqueness follows from the fact
that a finite measure on `ℝ≥0` is determined by its Laplace transform.

This completes the existence-and-uniqueness direction of the Bernstein milestone in
`TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B. The converse direction, asserting
complete monotonicity of Laplace transforms under the appropriate boundary regularity, is a
separate development.

## Main result

* `TauCeti.existsUnique_isFiniteMeasure_integral_exp_neg_mul_eq_of_isCompletelyMonotone`:
  every completely monotone function has a unique finite Laplace-representing measure.

## References

* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*
  (de Gruyter, 2nd ed. 2012), Theorem 1.4.
-/

public section

open MeasureTheory
open scoped NNReal

namespace TauCeti

variable {f : ℝ → ℝ}

/-- **Bernstein representation, existence and uniqueness.** A completely monotone function on
`[0, ∞)` is the Laplace transform of a unique finite positive measure on `ℝ≥0`.

This is the existence-and-uniqueness direction of Bernstein's theorem. The representing measure
is unique among all finite measures whose Laplace transform agrees with `f` at every nonnegative
real argument. -/
theorem existsUnique_isFiniteMeasure_integral_exp_neg_mul_eq_of_isCompletelyMonotone
    (hcm : IsCompletelyMonotone f) :
    ∃! μ : Measure ℝ≥0, IsFiniteMeasure μ ∧
      ∀ t : ℝ, 0 ≤ t → f t = ∫ x, Real.exp (-t * (x : ℝ)) ∂μ := by
  obtain ⟨μ, hμfin, hμ⟩ :=
    exists_isFiniteMeasure_integral_exp_neg_mul_eq_of_isCompletelyMonotone hcm
  refine ⟨μ, ⟨hμfin, hμ⟩, ?_⟩
  intro ν hν
  letI : IsFiniteMeasure μ := hμfin
  letI : IsFiniteMeasure ν := hν.1
  apply Measure.ext_of_forall_integral_exp_neg_mul_eq
  intro t ht
  rw [← hμ t ht, ← hν.2 t ht]

end TauCeti
