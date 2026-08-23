/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CompletelyMonotone.Bernstein.HausdorffBernsteinWidder
public import TauCeti.Analysis.CompletelyMonotone.Laplace.Measurability
public import Mathlib.Probability.Kernel.Defs

/-!
# The Bernstein representing measure, and its kernel form

The Hausdorff--Bernstein--Widder theorem attaches to a completely monotone function `f` on
`[0, ∞)` a *unique* finite measure on `ℝ≥0` whose Laplace transform is `f`. This file names that
measure, `TauCeti.bernsteinMeasure`, develops its basic API, and — the point of the file — shows
that it depends **measurably** on a parameter: a family `a ↦ f a` of completely monotone
functions whose values at the natural numbers are measurable in `a` has Bernstein measures
forming a `ProbabilityTheory.Kernel`.

Measurability is not a selection statement. The representing measure is unique, so the family
`a ↦ bernsteinMeasure (f a)` is already determined; what has to be proved is that this
particular family is measurable, and that is
`TauCeti.measurable_of_measurable_laplaceTransform_natCast`, applied to the identity
`laplaceTransform (bernsteinMeasure (f a)) n = f a n`.

## Main declarations

* `TauCeti.bernsteinMeasure`: the representing measure of a completely monotone function, and
  the zero measure for a function that has none.
* `TauCeti.representsLaplace_bernsteinMeasure`, `TauCeti.eq_bernsteinMeasure`: it represents its
  function, and it is the only finite measure that does.
* `TauCeti.bernsteinMeasure_add`, `TauCeti.bernsteinMeasure_const_mul`,
  `TauCeti.bernsteinMeasure_univ`: the algebraic API and the total mass.
* `TauCeti.measurable_bernsteinMeasure`: measurable dependence on a parameter.
* `TauCeti.bernsteinMeasureKernel`: the resulting kernel, with its finiteness criterion.

## References

The finite-measure representation is the Hausdorff--Bernstein--Widder theorem, after
S. Bernstein (1928) and D. V. Widder, *The Laplace Transform*, Chapter IV; see also
R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions* (de Gruyter, 2nd ed. 2012),
Theorem 1.4.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
  (BCR semigroup--Bochner).
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti

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
theorem laplaceTransform_bernsteinMeasure (hf : IsContinuousCompletelyMonotoneOnIoi f) {t : ℝ}
    (ht : 0 ≤ t) : laplaceTransform (bernsteinMeasure f) t = f t :=
  ((representsLaplace_bernsteinMeasure hf).eq_laplaceTransform ht).symm

/-- The total mass of the Bernstein measure is the value of the function at `0`. -/
theorem bernsteinMeasure_real_univ (hf : IsContinuousCompletelyMonotoneOnIoi f) :
    (bernsteinMeasure f).real univ = f 0 :=
  ((representsLaplace_bernsteinMeasure hf).apply_zero).symm

/-- The total mass of the Bernstein measure, as an extended nonnegative real. -/
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

/-! ## Measurable dependence on a parameter -/

variable {α : Type*} [MeasurableSpace α] {F : α → ℝ → ℝ}

/-- **The Bernstein measure depends measurably on a parameter.** If every member of a family of
functions is continuous on `[0, ∞)` and completely monotone on `(0, ∞)`, and if the family is
measurable in the parameter at each natural number, then the family of Bernstein measures is
measurable for the Giry σ-algebra.

Only the values at natural numbers enter, because a finite measure on `ℝ≥0` is already determined
by its Laplace transform there. -/
theorem measurable_bernsteinMeasure (hcm : ∀ a, IsContinuousCompletelyMonotoneOnIoi (F a))
    (hmeas : ∀ n : ℕ, Measurable fun a => F a (n : ℝ)) :
    Measurable fun a => bernsteinMeasure (F a) := by
  refine measurable_of_measurable_laplaceTransform_natCast fun n => ?_
  have hrw : (fun a => laplaceTransform (bernsteinMeasure (F a)) (n : ℝ))
      = fun a => F a (n : ℝ) := by
    funext a
    exact laplaceTransform_bernsteinMeasure (hcm a) (Nat.cast_nonneg n)
  rw [hrw]
  exact hmeas n

/-- **The Bernstein kernel of a measurable family.** The Bernstein representing measures of a
measurable family of completely monotone functions assemble into a kernel from the parameter
space to `ℝ≥0`. -/
noncomputable def bernsteinMeasureKernel (F : α → ℝ → ℝ)
    (hcm : ∀ a, IsContinuousCompletelyMonotoneOnIoi (F a))
    (hmeas : ∀ n : ℕ, Measurable fun a => F a (n : ℝ)) : Kernel α ℝ≥0 :=
  ⟨fun a => bernsteinMeasure (F a), measurable_bernsteinMeasure hcm hmeas⟩

@[simp]
theorem bernsteinMeasureKernel_apply (hcm : ∀ a, IsContinuousCompletelyMonotoneOnIoi (F a))
    (hmeas : ∀ n : ℕ, Measurable fun a => F a (n : ℝ)) (a : α) :
    bernsteinMeasureKernel F hcm hmeas a = bernsteinMeasure (F a) :=
  (rfl)

/-- Every fibre of the Bernstein kernel represents the corresponding member of the family. -/
theorem representsLaplace_bernsteinMeasureKernel
    (hcm : ∀ a, IsContinuousCompletelyMonotoneOnIoi (F a))
    (hmeas : ∀ n : ℕ, Measurable fun a => F a (n : ℝ)) (a : α) :
    RepresentsLaplace (bernsteinMeasureKernel F hcm hmeas a) (F a) := by
  rw [bernsteinMeasureKernel_apply]
  exact representsLaplace_bernsteinMeasure (hcm a)

/-- The Bernstein kernel is finite as soon as the values of the family at `0` are bounded; those
values are exactly the fibre masses. -/
theorem isFiniteKernel_bernsteinMeasureKernel
    (hcm : ∀ a, IsContinuousCompletelyMonotoneOnIoi (F a))
    (hmeas : ∀ n : ℕ, Measurable fun a => F a (n : ℝ)) {C : ℝ} (hC : ∀ a, F a 0 ≤ C) :
    IsFiniteKernel (bernsteinMeasureKernel F hcm hmeas) := by
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_lt_top, fun a => ?_⟩
  rw [bernsteinMeasureKernel_apply, bernsteinMeasure_univ (hcm a)]
  exact ENNReal.ofReal_le_ofReal (hC a)

/-- A family of normalized functions gives a Markov kernel. -/
theorem isMarkovKernel_bernsteinMeasureKernel
    (hcm : ∀ a, IsContinuousCompletelyMonotoneOnIoi (F a))
    (hmeas : ∀ n : ℕ, Measurable fun a => F a (n : ℝ)) (hone : ∀ a, F a 0 = 1) :
    IsMarkovKernel (bernsteinMeasureKernel F hcm hmeas) := by
  refine ⟨fun a => ?_⟩
  rw [bernsteinMeasureKernel_apply]
  exact isProbabilityMeasure_bernsteinMeasure (hcm a) (hone a)

end TauCeti
