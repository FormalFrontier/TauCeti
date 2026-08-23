/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.Transform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Positive definiteness of Laplace--Fourier transforms

A finite positive measure on `ℝ≥0 × V` has a bounded, continuous, semigroup-group
positive-definite Laplace--Fourier transform.  This is the easy direction of the
Berg--Christensen--Ressel representation theorem: each point of the measure supplies the
positive-definite atom

`(t, a) ↦ exp (-t p) * exp (-2πi⟪a, q⟫)`,

and integration preserves its finite quadratic-form inequalities.  Continuity follows from
dominated convergence, since every atom has norm at most one.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
("BCR semigroup--Bochner").  Together with the transform definition and uniqueness theorem, it
supplies the complete measure-to-function direction and leaves the representation of an arbitrary
bounded continuous positive-definite function as the remaining existence problem.

## Main declarations

* `TauCeti.norm_laplaceFourierTransform_le`: the transform is bounded by the total mass.
* `TauCeti.continuous_laplaceFourierTransform`: a finite measure's transform is continuous.
* `TauCeti.isSemigroupGroupPD_laplaceFourierTransform`: a finite measure's transform is
  semigroup-group positive definite.
* `TauCeti.RepresentsLaplaceFourier.isSemigroupGroupPD` and
  `TauCeti.RepresentsLaplaceFourier.continuous`: every represented function inherits the two
  structural properties.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13.
-/

public section

open ComplexConjugate MeasureTheory
open scoped ComplexOrder NNReal

namespace TauCeti

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Fourier atoms are symmetric in their frequency and evaluation arguments over a real inner
product space. -/
private theorem fourierAtom_comm (a q : V) : fourierAtom a q = fourierAtom q a := by
  rw [fourierAtom_apply, fourierAtom_apply, real_inner_comm]

/-- The transform integrand can be read as the positive-definite atom indexed by the integration
variable. -/
private theorem laplaceFourierIntegrand_comm (x y : ℝ≥0 × V) :
    laplaceAtom x.1 y.1 * fourierAtom x.2 y.2 =
      laplaceAtom y.1 x.1 * fourierAtom y.2 x.2 := by
  rw [laplaceAtom_comm, fourierAtom_comm]

/-- The BCR kernel symmetry of a single Laplace--Fourier transform integrand. -/
private theorem conj_laplaceFourierIntegrand (y p q : ℝ≥0 × V) :
    conj (laplaceAtom (p.1 + q.1) y.1 * fourierAtom (p.2 - q.2) y.2) =
      laplaceAtom (q.1 + p.1) y.1 * fourierAtom (q.2 - p.2) y.2 := by
  have h := (isSemigroupGroupPD_laplaceFourierAtom y.1 y.2).conj_symm p q
  simpa only [laplaceAtom_comm, fourierAtom_comm] using h

variable [MeasurableSpace V]

/-- The Laplace--Fourier transform of a finite measure is bounded in norm by the measure's total
mass.  In particular it is a bounded function, as required in the BCR representation theorem. -/
theorem norm_laplaceFourierTransform_le (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ]
    (x : ℝ≥0 × V) :
    ‖laplaceFourierTransform μ x‖ ≤ μ.real Set.univ := by
  rw [laplaceFourierTransform_apply]
  simpa using norm_integral_le_of_norm_le_const
    (μ := μ) (C := 1) (.of_forall fun y =>
      norm_laplaceAtom_mul_fourierAtom_le_one x.1 y.1 x.2 y.2)

variable [OpensMeasurableSpace V]

/-- The Laplace--Fourier transform of a finite measure is continuous.  The integrands are jointly
continuous in the evaluation variable and uniformly dominated by the integrable constant one. -/
theorem continuous_laplaceFourierTransform (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ] :
    Continuous (laplaceFourierTransform μ) := by
  have h_eq : laplaceFourierTransform μ =
      fun x => ∫ y, laplaceAtom x.1 y.1 * fourierAtom x.2 y.2 ∂μ :=
    funext (laplaceFourierTransform_apply μ)
  rw [h_eq]
  refine continuous_of_dominated (bound := fun _ => 1) ?_ ?_ (integrable_const 1) ?_
  · intro x
    exact (continuous_mul_time_spatial (continuous_laplaceAtom x.1)
      (continuous_fourierAtom x.2)).aestronglyMeasurable
  · intro x
    exact .of_forall fun y => norm_laplaceAtom_mul_fourierAtom_le_one x.1 y.1 x.2 y.2
  · exact .of_forall fun y => by
      convert continuous_mul_time_spatial (continuous_laplaceAtom y.1)
        (continuous_fourierAtom y.2) using 1
      ext x
      exact laplaceFourierIntegrand_comm x y

/-- The finite quadratic form of a Laplace--Fourier transform is the integral of the corresponding
quadratic forms of its atoms. -/
private theorem laplaceFourierTransform_sum_eq_integral
    (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ] {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (p : ι → ℝ≥0 × V) :
    (∑ i, ∑ j, c i * conj (c j) *
        laplaceFourierTransform μ ((p i).1 + (p j).1, (p i).2 - (p j).2)) =
      ∫ y, ∑ i, ∑ j, c i * conj (c j) *
        (laplaceAtom ((p i).1 + (p j).1) y.1 *
          fourierAtom ((p i).2 - (p j).2) y.2) ∂μ := by
  classical
  have hterm (i j : ι) : Integrable (fun y : ℝ≥0 × V =>
      c i * conj (c j) * (laplaceAtom ((p i).1 + (p j).1) y.1 *
        fourierAtom ((p i).2 - (p j).2) y.2)) μ :=
    (integrable_laplaceAtom_mul_fourierAtom μ
      ((p i).1 + (p j).1) ((p i).2 - (p j).2)).const_mul _
  have hrow (i : ι) : Integrable (fun y : ℝ≥0 × V =>
      ∑ j, c i * conj (c j) * (laplaceAtom ((p i).1 + (p j).1) y.1 *
        fourierAtom ((p i).2 - (p j).2) y.2)) μ :=
    integrable_finsetSum Finset.univ fun j _ => hterm i j
  calc
    (∑ i, ∑ j, c i * conj (c j) *
        laplaceFourierTransform μ ((p i).1 + (p j).1, (p i).2 - (p j).2)) =
        ∑ i, ∑ j, ∫ y, c i * conj (c j) *
          (laplaceAtom ((p i).1 + (p j).1) y.1 *
            fourierAtom ((p i).2 - (p j).2) y.2) ∂μ := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [laplaceFourierTransform_apply, integral_const_mul]
    _ = ∑ i, ∫ y, ∑ j, c i * conj (c j) *
        (laplaceAtom ((p i).1 + (p j).1) y.1 *
          fourierAtom ((p i).2 - (p j).2) y.2) ∂μ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      exact (integral_finsetSum Finset.univ fun j _ => hterm i j).symm
    _ = ∫ y, ∑ i, ∑ j, c i * conj (c j) *
        (laplaceAtom ((p i).1 + (p j).1) y.1 *
          fourierAtom ((p i).2 - (p j).2) y.2) ∂μ :=
      (integral_finsetSum Finset.univ fun i _ => hrow i).symm

/-- The Laplace--Fourier transform of a finite positive measure is semigroup-group positive
definite.  This is the positivity half of the measure-to-function direction of BCR. -/
theorem isSemigroupGroupPD_laplaceFourierTransform
    (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ] :
    IsSemigroupGroupPD (laplaceFourierTransform μ) := by
  rw [isSemigroupGroupPD_iff.{_, 0}]
  refine ⟨?_, ?_⟩
  · intro p q
    rw [laplaceFourierTransform_apply, laplaceFourierTransform_apply, ← integral_conj]
    exact integral_congr_ae (.of_forall fun y => conj_laplaceFourierIntegrand y p q)
  · intro ι _ c p
    rw [laplaceFourierTransform_sum_eq_integral μ c p]
    refine MeasureTheory.integral_nonneg (E := ℂ) fun y => ?_
    dsimp only [Pi.zero_apply]
    simpa only [laplaceAtom_comm, fourierAtom_comm] using
      (IsSemigroupGroupPD.sum_nonneg (V := V) (ι := ι)
        (isSemigroupGroupPD_laplaceFourierAtom y.1 y.2) c p)

namespace RepresentsLaplaceFourier

variable {μ : Measure (ℝ≥0 × V)} {F : ℝ≥0 × V → ℂ}

/-- A function represented by a finite measure is semigroup-group positive definite. -/
theorem isSemigroupGroupPD (h : RepresentsLaplaceFourier μ F) : IsSemigroupGroupPD F := by
  let _ : IsFiniteMeasure μ := h.isFiniteMeasure
  have hF : F = laplaceFourierTransform μ := funext h.eq_laplaceFourierTransform
  rw [hF]
  exact isSemigroupGroupPD_laplaceFourierTransform μ

/-- A function represented by a finite measure is continuous. -/
theorem continuous (h : RepresentsLaplaceFourier μ F) : Continuous F := by
  let _ : IsFiniteMeasure μ := h.isFiniteMeasure
  have hF : F = laplaceFourierTransform μ := funext h.eq_laplaceFourierTransform
  rw [hF]
  exact continuous_laplaceFourierTransform μ

omit [OpensMeasurableSpace V] in
/-- A function represented by `μ` is uniformly bounded in norm by the total mass of `μ`. -/
theorem norm_le_mass (h : RepresentsLaplaceFourier μ F) (x : ℝ≥0 × V) :
    ‖F x‖ ≤ μ.real Set.univ := by
  let _ : IsFiniteMeasure μ := h.isFiniteMeasure
  rw [h.eq_laplaceFourierTransform x]
  exact norm_laplaceFourierTransform_le μ x

end RepresentsLaplaceFourier

end TauCeti
