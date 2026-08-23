/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The Laplace--Fourier transform of a measure on `ℝ≥0 × V`

For a *finite-dimensional* real inner product space `V`, the Berg--Christensen--Ressel
representation writes a bounded continuous positive-definite function on the involutive
semigroup `ℝ≥0 × V` as the Laplace--Fourier transform

`F (t, a) = ∫ (p, q), exp (-t p) * exp (-2πi⟪a, q⟫) ∂μ`

of a finite measure `μ` on `ℝ≥0 × V`. This file defines that transform for an arbitrary `V`
— no finite-dimensionality is needed to write it down — through the atoms of
`TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.Basic`, and packages the
predicate that a finite measure represents a given function this way. It is the material both
halves of the representation theorem share: the uniqueness half
(`TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.Uniqueness`) and the existence
half, which consumes Bochner's theorem on `V`.

## Main declarations

* `TauCeti.laplaceFourierTransform`: the Laplace--Fourier transform of a measure on `ℝ≥0 × V`,
  in Mathlib's `2π` Fourier convention.
* `TauCeti.laplaceFourierTransform_apply_exp`: the transform in the exponential form used by the
  Berg--Christensen--Ressel statement.
* `TauCeti.RepresentsLaplaceFourier`: the predicate that a finite measure represents a function
  on `ℝ≥0 × V` by its Laplace--Fourier transform.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
  ("BCR semigroup--Bochner"), whose statement this transform expresses.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-! ## The Laplace--Fourier atoms of a fixed evaluation point -/

section Atoms

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Laplace--Fourier atoms are bounded by `1` in norm: the Laplace factor is at most `1`
because both parameters are nonnegative, and the Fourier factor is unimodular. -/
theorem norm_laplaceAtom_mul_fourierAtom_le_one (t p : ℝ≥0) (a q : V) :
    ‖laplaceAtom t p * fourierAtom a q‖ ≤ 1 := by
  rw [norm_mul, laplaceAtom_def, fourierAtom_eq_fourierChar, Complex.norm_real,
    Circle.norm_coe, mul_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 p.coe_nonneg) t.coe_nonneg

end Atoms

/-! ## The Laplace--Fourier transform of a measure -/

section Defs

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]

/-- The **Laplace--Fourier transform** of a measure on `ℝ≥0 × V`, evaluated at a point
`x = (t, a)` of the involutive semigroup `ℝ≥0 × V`:

`(t, a) ↦ ∫ (p, q), exp (-t p) * exp (-2πi⟪a, q⟫) ∂μ`.

The integrand is the separated Laplace--Fourier atom of
`TauCeti.isSemigroupGroupPD_laplaceFourierAtom`. Nothing here relates the measurable structure
on `V` to its topology, so the integral need not converge; integrability of the atoms against a
finite measure is `TauCeti.integrable_laplaceAtom_mul_fourierAtom`, which additionally assumes
`OpensMeasurableSpace V`. For a finite-dimensional `V`, the Berg--Christensen--Ressel theorem
asserts that every bounded continuous semigroup-group positive-definite function on `ℝ≥0 × V`
is the transform of a finite measure. -/
noncomputable def laplaceFourierTransform (μ : Measure (ℝ≥0 × V)) (x : ℝ≥0 × V) : ℂ :=
  ∫ y, laplaceAtom x.1 y.1 * fourierAtom x.2 y.2 ∂μ

/-- The defining formula for `laplaceFourierTransform`. Not `@[simp]`: simp should not unfold
the abstraction into a raw integral. -/
theorem laplaceFourierTransform_apply (μ : Measure (ℝ≥0 × V)) (x : ℝ≥0 × V) :
    laplaceFourierTransform μ x = ∫ y, laplaceAtom x.1 y.1 * fourierAtom x.2 y.2 ∂μ := by
  rw [laplaceFourierTransform]

/-- The Laplace--Fourier transform in the exponential form used by the Berg--Christensen--Ressel
statement: the transform at `(t, a)` integrates `exp (-t p) * exp (-2πi⟪a, q⟫)`. -/
theorem laplaceFourierTransform_apply_exp (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) (a : V) :
    laplaceFourierTransform μ (t, a) =
      ∫ y, (Real.exp (-(t : ℝ) * (y.1 : ℝ)) : ℂ) *
        Complex.exp (-2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ a y.2 : ℝ) : ℂ)) ∂μ := by
  rw [laplaceFourierTransform_apply]
  refine integral_congr_ae (.of_forall fun y => ?_)
  -- beta-reduce the two integrands and the projections of the pair `(t, a)`
  dsimp only
  rw [laplaceAtom_comm, laplaceAtom_def, fourierAtom_apply, real_inner_comm]

/-- The integrand of the Laplace--Fourier transform is integrable against a finite measure. -/
theorem integrable_laplaceAtom_mul_fourierAtom [OpensMeasurableSpace V]
    (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ] (t : ℝ≥0) (a : V) :
    Integrable (fun y : ℝ≥0 × V => laplaceAtom t y.1 * fourierAtom a y.2) μ :=
  (integrable_const (1 : ℝ)).mono'
    (continuous_mul_time_spatial (continuous_laplaceAtom t)
      (continuous_fourierAtom a)).aestronglyMeasurable
    (.of_forall fun y => norm_laplaceAtom_mul_fourierAtom_le_one t y.1 a y.2)

/-! ## Values and elementary measure operations -/

/-- The Laplace--Fourier transform at the identity `0` of `ℝ≥0 × V` is the total mass: both
atoms are `1` there. -/
@[simp]
theorem laplaceFourierTransform_zero (μ : Measure (ℝ≥0 × V)) :
    laplaceFourierTransform μ 0 = (μ.real univ : ℂ) := by
  rw [laplaceFourierTransform_apply]
  simp [laplaceAtom_def, fourierAtom_apply, Complex.real_smul]

/-- The zero measure has zero Laplace--Fourier transform. -/
@[simp]
theorem laplaceFourierTransform_zero_measure (x : ℝ≥0 × V) :
    laplaceFourierTransform (0 : Measure (ℝ≥0 × V)) x = 0 := by
  rw [laplaceFourierTransform_apply, integral_zero_measure]

/-- The Laplace--Fourier transform of a Dirac mass is the atom at its point. -/
@[simp]
theorem laplaceFourierTransform_dirac [OpensMeasurableSpace V] (y x : ℝ≥0 × V) :
    laplaceFourierTransform (Measure.dirac y) x = laplaceAtom x.1 y.1 * fourierAtom x.2 y.2 := by
  rw [laplaceFourierTransform_apply,
    integral_dirac' _ y (continuous_mul_time_spatial (continuous_laplaceAtom x.1)
      (continuous_fourierAtom x.2)).stronglyMeasurable]

/-- The Laplace--Fourier transform is additive in the measure. -/
@[simp]
theorem laplaceFourierTransform_add_measure [OpensMeasurableSpace V] (μ ν : Measure (ℝ≥0 × V))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (x : ℝ≥0 × V) :
    laplaceFourierTransform (μ + ν) x =
      laplaceFourierTransform μ x + laplaceFourierTransform ν x := by
  simp only [laplaceFourierTransform_apply]
  exact integral_add_measure (integrable_laplaceAtom_mul_fourierAtom μ x.1 x.2)
    (integrable_laplaceAtom_mul_fourierAtom ν x.1 x.2)

/-- Scaling the measure scales its Laplace--Fourier transform. -/
@[simp]
theorem laplaceFourierTransform_smul_measure (μ : Measure (ℝ≥0 × V)) (c : ℝ≥0∞)
    (x : ℝ≥0 × V) :
    laplaceFourierTransform (c • μ) x = c.toReal • laplaceFourierTransform μ x := by
  simp only [laplaceFourierTransform_apply]
  exact integral_smul_measure _ c

/-! ## The representation predicate -/

/-- A finite measure represents a function on `ℝ≥0 × V` by its Laplace--Fourier transform. This
is the representation asserted by the Berg--Christensen--Ressel theorem. -/
def RepresentsLaplaceFourier (μ : Measure (ℝ≥0 × V)) (F : ℝ≥0 × V → ℂ) : Prop :=
  IsFiniteMeasure μ ∧ ∀ x, F x = laplaceFourierTransform μ x

/-- `RepresentsLaplaceFourier μ F` unfolds to finiteness of `μ` together with the
Laplace--Fourier representation of `F`. -/
theorem representsLaplaceFourier_iff {μ : Measure (ℝ≥0 × V)} {F : ℝ≥0 × V → ℂ} :
    RepresentsLaplaceFourier μ F ↔
      IsFiniteMeasure μ ∧ ∀ x, F x = laplaceFourierTransform μ x :=
  Iff.rfl

namespace RepresentsLaplaceFourier

variable {μ : Measure (ℝ≥0 × V)} {F : ℝ≥0 × V → ℂ}

/-- A representing measure is finite. -/
@[grind →]
theorem isFiniteMeasure (h : RepresentsLaplaceFourier μ F) : IsFiniteMeasure μ := h.1

/-- A representing measure has the advertised Laplace--Fourier transform. -/
@[grind =>]
theorem eq_laplaceFourierTransform (h : RepresentsLaplaceFourier μ F) (x : ℝ≥0 × V) :
    F x = laplaceFourierTransform μ x :=
  h.2 x

/-- The value of a represented function at the identity of `ℝ≥0 × V` is the total mass of the
representing measure. (Not `@[simp]`: the left-hand side has a variable head symbol.) -/
theorem apply_zero (h : RepresentsLaplaceFourier μ F) : F 0 = (μ.real univ : ℂ) := by
  rw [h.eq_laplaceFourierTransform 0, laplaceFourierTransform_zero]

/-- The sum of two representing measures represents the sum of the functions. -/
protected theorem add [OpensMeasurableSpace V] {G : ℝ≥0 × V → ℂ} {ν : Measure (ℝ≥0 × V)}
    (hF : RepresentsLaplaceFourier μ F) (hG : RepresentsLaplaceFourier ν G) :
    RepresentsLaplaceFourier (μ + ν) (F + G) := by
  have := hF.isFiniteMeasure
  have := hG.isFiniteMeasure
  refine ⟨inferInstance, fun x => ?_⟩
  rw [Pi.add_apply, hF.eq_laplaceFourierTransform x, hG.eq_laplaceFourierTransform x,
    laplaceFourierTransform_add_measure]

/-- Scaling a representing measure by `c : ℝ≥0` represents the scaled function. -/
protected theorem smul (c : ℝ≥0) (hF : RepresentsLaplaceFourier μ F) :
    RepresentsLaplaceFourier ((c : ℝ≥0∞) • μ) (fun x => (c : ℝ) • F x) := by
  have := hF.isFiniteMeasure
  have : IsFiniteMeasure ((c : ℝ≥0∞) • μ) := μ.smul_finite ENNReal.coe_ne_top
  refine ⟨inferInstance, fun x => ?_⟩
  -- beta-reduce the scaled function at `x`
  dsimp only
  rw [laplaceFourierTransform_smul_measure, ENNReal.coe_toReal, hF.eq_laplaceFourierTransform x]

end RepresentsLaplaceFourier

/-- The zero measure represents the zero function. -/
theorem representsLaplaceFourier_zero :
    RepresentsLaplaceFourier (0 : Measure (ℝ≥0 × V)) 0 :=
  ⟨inferInstance, fun x => by simp⟩

/-- The Dirac mass at `y` represents the Laplace--Fourier atom of `y`. -/
theorem representsLaplaceFourier_dirac [OpensMeasurableSpace V] (y : ℝ≥0 × V) :
    RepresentsLaplaceFourier (Measure.dirac y)
      (fun x => laplaceAtom x.1 y.1 * fourierAtom x.2 y.2) :=
  ⟨inferInstance, fun x => by rw [laplaceFourierTransform_dirac]⟩

end Defs

end TauCeti
