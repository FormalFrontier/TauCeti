/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.FiniteDifference.Laplace

/-!
# Hausdorff--Bernstein--Widder theorem

This file proves the finite-measure form of the Hausdorff--Bernstein--Widder theorem for
completely monotone functions on the closed half-line: a function is continuous on `[0, ∞)`
and completely monotone on `(0, ∞)` if and only if it is the Laplace transform of a (unique)
finite positive measure on `ℝ≥0`.

The hard direction is a direct application of the finite-difference representation theorem in
`FiniteDifference/Laplace.lean`: derivative complete monotonicity implies the mixed-difference
condition, and continuity on `[0, ∞)` supplies right-continuity at zero. The easy direction and
uniqueness live in `Laplace/Representation.lean`.

## Main declarations

* `TauCeti.exists_representsLaplace_of_isContinuousCompletelyMonotoneOnIoi`
* `TauCeti.hausdorff_bernstein_widder`, `TauCeti.hausdorff_bernstein_widder_existsUnique`
* `TauCeti.bernsteinMeasure`: the canonical representing measure, with its uniqueness,
  total-mass, and algebraic API.

## References

The finite-measure representation is the Hausdorff--Bernstein--Widder theorem, after
S. Bernstein (1928) and D. V. Widder, *The Laplace Transform*, Chapter IV.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem
  milestone).
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Topology

namespace TauCeti

/-- **Existence half of the Hausdorff--Bernstein--Widder theorem**: a function continuous on
`[0, ∞)` and completely monotone on `(0, ∞)` is the Laplace transform of a finite positive
measure on `ℝ≥0`. -/
theorem exists_representsLaplace_of_isContinuousCompletelyMonotoneOnIoi
    {f : ℝ → ℝ} (hf : IsContinuousCompletelyMonotoneOnIoi f) :
    ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f :=
  exists_representsLaplace_of_isDifferenceCompletelyMonotone_of_continuousWithinAt
    hf.isDifferenceCompletelyMonotone
    (hf.continuousOn.continuousWithinAt (mem_Ici.2 le_rfl))

/-! ## Headline theorem -/

/-- **Hausdorff--Bernstein--Widder theorem**, finite-measure version on `ℝ≥0`.

A function is continuous on `[0, ∞)` and completely monotone on `(0, ∞)` if and only if it is
the Laplace transform of a finite positive measure on `ℝ≥0`. -/
theorem hausdorff_bernstein_widder (f : ℝ → ℝ) :
    IsContinuousCompletelyMonotoneOnIoi f ↔ ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  constructor
  · exact exists_representsLaplace_of_isContinuousCompletelyMonotoneOnIoi
  · rintro ⟨μ, hμ⟩
    exact hμ.isContinuousCompletelyMonotoneOnIoi

/-- Unique-existence form of the Hausdorff--Bernstein--Widder theorem. -/
theorem hausdorff_bernstein_widder_existsUnique (f : ℝ → ℝ) :
    IsContinuousCompletelyMonotoneOnIoi f ↔ ∃! μ : Measure ℝ≥0, RepresentsLaplace μ f := by
  rw [hausdorff_bernstein_widder]
  exact ⟨fun ⟨μ, hμ⟩ => ⟨μ, hμ, fun ν hν => hν.unique hμ⟩,
    fun ⟨μ, hμ, _⟩ => ⟨μ, hμ⟩⟩

/-! ## The canonical representing measure -/

variable {f : ℝ → ℝ}

open Classical in
/-- **The Bernstein representing measure** of `f`: the unique finite measure on `ℝ≥0` whose
Laplace transform is `f` on `[0, ∞)`, when `f` has one, and the zero measure otherwise.

By `TauCeti.hausdorff_bernstein_widder` a representing measure exists exactly when `f` is
continuous on `[0, ∞)` and completely monotone on `(0, ∞)`. -/
noncomputable def bernsteinMeasure (f : ℝ → ℝ) : Measure ℝ≥0 :=
  if h : ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f then h.choose else 0

/-- Outside the hypotheses of the Hausdorff--Bernstein--Widder theorem the Bernstein measure is
`0`. -/
theorem bernsteinMeasure_eq_zero_of_not (h : ¬ ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f) :
    bernsteinMeasure f = 0 := by
  classical
  rw [bernsteinMeasure, dite_eq_right h]

/-- **The Bernstein measure represents its function.** -/
theorem representsLaplace_bernsteinMeasure (hf : IsContinuousCompletelyMonotoneOnIoi f) :
    RepresentsLaplace (bernsteinMeasure f) f := by
  classical
  have h : ∃ μ : Measure ℝ≥0, RepresentsLaplace μ f := (hausdorff_bernstein_widder f).mp hf
  rw [bernsteinMeasure, dite_eq_left h]
  exact h.choose_spec

/-- The Bernstein measure of any function is finite: for a represented function this is the
finiteness of its representing measure, and otherwise the measure is `0`. -/
instance isFiniteMeasure_bernsteinMeasure (f : ℝ → ℝ) : IsFiniteMeasure (bernsteinMeasure f) := by
  classical
  rw [bernsteinMeasure]
  split
  · rename_i h
    exact h.choose_spec.isFiniteMeasure
  · infer_instance

/-- **Uniqueness of the Bernstein measure.** Any finite measure representing `f` by its Laplace
transform is the Bernstein measure of `f`. No hypothesis on `f` is needed: a represented function
is automatically continuous and completely monotone. -/
theorem eq_bernsteinMeasure (μ : Measure ℝ≥0) (hμ : RepresentsLaplace μ f) :
    μ = bernsteinMeasure f :=
  hμ.unique (representsLaplace_bernsteinMeasure hμ.isContinuousCompletelyMonotoneOnIoi)

/-- The Laplace transform of the Bernstein measure recovers the function on `[0, ∞)`. -/
@[grind =>]
theorem laplaceTransform_bernsteinMeasure (hf : IsContinuousCompletelyMonotoneOnIoi f) {t : ℝ}
    (ht : 0 ≤ t) : laplaceTransform (bernsteinMeasure f) t = f t :=
  ((representsLaplace_bernsteinMeasure hf).eq_laplaceTransform ht).symm

/-- The total mass of the Bernstein measure is the value of the function at `0`. -/
@[simp]
theorem bernsteinMeasure_real_univ (hf : IsContinuousCompletelyMonotoneOnIoi f) :
    (bernsteinMeasure f).real univ = f 0 :=
  ((representsLaplace_bernsteinMeasure hf).apply_zero).symm

/-- The total mass of the Bernstein measure, as an extended nonnegative real. -/
@[simp]
theorem bernsteinMeasure_univ (hf : IsContinuousCompletelyMonotoneOnIoi f) :
    bernsteinMeasure f univ = ENNReal.ofReal (f 0) := by
  rw [← bernsteinMeasure_real_univ hf, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- A function with total mass `1` has a probability measure for its Bernstein measure. -/
theorem isProbabilityMeasure_bernsteinMeasure (hf : IsContinuousCompletelyMonotoneOnIoi f)
    (hf0 : f 0 = 1) : IsProbabilityMeasure (bernsteinMeasure f) :=
  isProbabilityMeasure_iff_real.mpr <| by rw [bernsteinMeasure_real_univ hf, hf0]

/-- The Bernstein measure of the zero function is the zero measure. -/
@[simp]
theorem bernsteinMeasure_zero : bernsteinMeasure (fun _ : ℝ => (0 : ℝ)) = 0 :=
  (eq_bernsteinMeasure 0 representsLaplace_zero).symm

/-- The Bernstein measure turns sums of functions into sums of measures. -/
theorem bernsteinMeasure_add {g : ℝ → ℝ} (hf : IsContinuousCompletelyMonotoneOnIoi f)
    (hg : IsContinuousCompletelyMonotoneOnIoi g) :
    bernsteinMeasure (f + g) = bernsteinMeasure f + bernsteinMeasure g :=
  (eq_bernsteinMeasure _ ((representsLaplace_bernsteinMeasure hf).add
    (representsLaplace_bernsteinMeasure hg))).symm

/-- The Bernstein measure turns nonnegative scalar multiples of functions into scalar multiples of
measures. -/
theorem bernsteinMeasure_const_mul (hf : IsContinuousCompletelyMonotoneOnIoi f) (c : ℝ≥0) :
    bernsteinMeasure (fun t => (c : ℝ) * f t) = (c : ℝ≥0∞) • bernsteinMeasure f :=
  (eq_bernsteinMeasure _ ((representsLaplace_bernsteinMeasure hf).smul c)).symm

end TauCeti
