/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.MeasurableSpace.Analytic
public import TauCeti.MeasureTheory.OptimalTransport.CTransform

/-!
# Analytic measurability of the infimal `c`-transform

For Polish source and target spaces, a Borel integrand
`(x, y) ↦ (c (x, y) : EReal) - φ x` need not have a Borel infimum over `x`. Its strict sublevel
sets are nevertheless analytic: each is the projection of the corresponding Borel strict
sublevel set of the integrand. Luzin's theorem then makes every such sublevel measurable in the
completion of each finite Borel measure. This is the precise measurability regime used to
integrate general Kantorovich potentials without incorrectly claiming Borel measurability.

The symmetric transform is included with the same hypotheses on the transposed integrand.

## Main results

* `TauCeti.analyticSet_setOf_cTransform_lt`: strict sublevels of the infimal transform are
  analytic;
* `TauCeti.nullMeasurableSet_setOf_cTransform_lt`: those sublevels are measurable after
  completing any finite Borel measure;
* `TauCeti.nullMeasurable_cTransform`: the transform itself is null-measurable for each finite
  Borel measure;
* the corresponding three results with `cTransformSymm` in their names.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer, 2009, Chapter 5.
* A. S. Kechris, *Classical Descriptive Set Theory*, Springer-Verlag, 1995, Theorem 29.7.
-/

public section

open MeasureTheory Set

noncomputable section

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {c : X × Y → ℝ} {φ : X → EReal} {ψ : Y → EReal}

/-- If the defining integrand of a `c`-transform is Borel measurable, every strict sublevel of
the transform is analytic. It is the second-coordinate projection of the corresponding Borel
strict sublevel of the integrand. -/
theorem analyticSet_setOf_cTransform_lt (a : EReal)
    (h : Measurable fun z : X × Y => (c z : EReal) - φ z.1) :
    AnalyticSet {y | cTransform c φ y < a} := by
  simpa only [cTransform_apply] using
    MeasureTheory.analyticSet_setOf_iInf_lt
      (fun z : X × Y => (c z : EReal) - φ z.1) a (h measurableSet_Iio)

/-- If the defining integrand of a symmetric `c`-transform is Borel measurable, every strict
sublevel of the transform is analytic. -/
theorem analyticSet_setOf_cTransformSymm_lt (a : EReal)
    (h : Measurable fun z : X × Y => (c z : EReal) - ψ z.2) :
    AnalyticSet {x | cTransformSymm c ψ x < a} := by
  simpa only [cTransformSymm_apply] using
    MeasureTheory.analyticSet_setOf_iInf_lt
      (fun z : Y × X => (c (z.2, z.1) : EReal) - ψ z.1) a
        ((h.comp measurable_swap) measurableSet_Iio)

/-- A strict sublevel of a `c`-transform with Borel defining integrand is measurable after
completing any finite Borel measure on the target. -/
theorem nullMeasurableSet_setOf_cTransform_lt (μ : Measure Y) [IsFiniteMeasure μ] (a : EReal)
    (h : Measurable fun z : X × Y => (c z : EReal) - φ z.1) :
    NullMeasurableSet {y | cTransform c φ y < a} μ :=
  MeasureTheory.AnalyticSet.nullMeasurableSet (analyticSet_setOf_cTransform_lt a h) μ

/-- A strict sublevel of a symmetric `c`-transform with Borel defining integrand is measurable
after completing any finite Borel measure on the source. -/
theorem nullMeasurableSet_setOf_cTransformSymm_lt (μ : Measure X) [IsFiniteMeasure μ]
    (a : EReal) (h : Measurable fun z : X × Y => (c z : EReal) - ψ z.2) :
    NullMeasurableSet {x | cTransformSymm c ψ x < a} μ :=
  MeasureTheory.AnalyticSet.nullMeasurableSet (analyticSet_setOf_cTransformSymm_lt a h) μ

/-- A `c`-transform with Borel defining integrand is measurable for the completion of every
finite Borel measure on the target. This is deliberately `NullMeasurable`, not Borel
`Measurable`. -/
theorem nullMeasurable_cTransform (μ : Measure Y) [IsFiniteMeasure μ]
    (h : Measurable fun z : X × Y => (c z : EReal) - φ z.1) :
    NullMeasurable (cTransform c φ) μ := by
  have hm : @Measurable (NullMeasurableSpace Y μ) EReal _ _ (cTransform c φ) :=
    measurable_of_Iio fun a =>
      MeasureTheory.AnalyticSet.nullMeasurableSet (analyticSet_setOf_cTransform_lt a h) μ
  exact hm

/-- A symmetric `c`-transform with Borel defining integrand is measurable for the completion of
every finite Borel measure on the source. -/
theorem nullMeasurable_cTransformSymm (μ : Measure X) [IsFiniteMeasure μ]
    (h : Measurable fun z : X × Y => (c z : EReal) - ψ z.2) :
    NullMeasurable (cTransformSymm c ψ) μ := by
  have hm : @Measurable (NullMeasurableSpace X μ) EReal _ _ (cTransformSymm c ψ) :=
    measurable_of_Iio fun a =>
      MeasureTheory.AnalyticSet.nullMeasurableSet (analyticSet_setOf_cTransformSymm_lt a h) μ
  exact hm

end TauCeti
