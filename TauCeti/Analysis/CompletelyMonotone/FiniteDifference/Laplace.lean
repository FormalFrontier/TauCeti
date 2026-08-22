/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.Theorem
public import TauCeti.Analysis.CompletelyMonotone.FiniteDifference.Mollify

/-!
# Approximate Bernstein representation from finite differences

Bernstein's theorem in the form
`TauCeti.exists_representsLaplace_of_isCompletelyMonotone` takes a completely monotone function,
that is a *smooth* one with alternating iterated derivatives, and produces a finite measure on
`ℝ≥0` whose Laplace transform it is. The hypothesis available in applications is the
finite-difference one of
`TauCeti.IsDifferenceCompletelyMonotone`, which carries no smoothness.

Feeding the smoothing of
`TauCeti.IsDifferenceCompletelyMonotone.exists_isCompletelyMonotone_between_shift` into Bernstein's
theorem bridges the two up to an arbitrarily small shift of the argument: a function on `[0, ∞)`
all of whose mixed forward differences alternate is squeezed, for every `ε > 0`, between
the shift `f (· + ε)` and `f` by the Laplace transform of a finite measure.

What is *not* done here is the passage to the limit `ε → 0`, and compactness alone does not
achieve it: the finite-difference hypothesis says nothing about the behaviour of `f` at the
endpoint. The indicator `f 0 = 1`, `f t = 0` for `t ≠ 0` has every mixed difference with
nonnegative steps of the required sign on `[0, ∞)` — with all steps positive, the only surviving
term of `Δ_{h₁} ⋯ Δ_{hₙ} f` at a point of `[0, ∞)` is `(-1)ⁿ f 0` at the origin — while no finite
positive measure has it as its Laplace transform. A full representation therefore needs
right-continuity at `0` on top of the weak cluster point of the approximating measures, the
compactness step that Bernstein's own existence proof performs for the Chafaï measures.

## Main declarations

* `TauCeti.IsDifferenceCompletelyMonotone.exists_isFiniteMeasure_laplaceTransform_between_shift`:
  the approximate
  Laplace representation of a finite-difference completely monotone function.

## References

* D. V. Widder, *The Laplace Transform* (Princeton, 1941), Chapter IV.
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace TauCeti

variable {f : ℝ → ℝ}

/-- **Approximate Bernstein representation.** A function that is completely monotone in the
finite-difference sense is squeezed, for every `ε > 0`, between
`f (· + ε)` and `f` by the Laplace transform of a finite positive measure on `ℝ≥0`.

A Bernstein representation of `f` itself does not follow from these measures by compactness
alone: the hypothesis leaves the value at the endpoint free, so it needs right-continuity of `f`
at `0` in addition to a weak cluster point as `ε → 0`. -/
theorem IsDifferenceCompletelyMonotone.exists_isFiniteMeasure_laplaceTransform_between_shift
    (hf : IsDifferenceCompletelyMonotone f) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : Measure ℝ≥0, IsFiniteMeasure μ ∧ ∀ t : ℝ, 0 ≤ t →
      f (t + ε) ≤ laplaceTransform μ t ∧ laplaceTransform μ t ≤ f t := by
  obtain ⟨g, hg, hgle⟩ := hf.exists_isCompletelyMonotone_between_shift hε
  obtain ⟨μ, hμ⟩ := exists_representsLaplace_of_isCompletelyMonotone hg
  refine ⟨μ, hμ.isFiniteMeasure, fun t ht => ?_⟩
  rw [← hμ.eq_laplaceTransform ht]
  exact hgle t ht

end TauCeti
