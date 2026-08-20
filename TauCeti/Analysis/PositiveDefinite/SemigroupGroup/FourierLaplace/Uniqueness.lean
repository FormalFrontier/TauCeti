/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.Slice

/-!
# Uniqueness of the Berg--Christensen--Ressel representing measure

For a *finite-dimensional* real inner product space `V`, the Berg--Christensen--Ressel
representation writes a bounded continuous positive-definite function on the involutive
semigroup `ℝ≥0 × V` as the Laplace--Fourier transform

`F (t, a) = ∫ (p, q), exp (-t p) * exp (-2πi⟪a, q⟫) ∂μ`

of a finite measure `μ` on `ℝ≥0 × V`. This file supplies the **uniqueness half**: a finite
measure on `ℝ≥0 × V` is determined by its Laplace--Fourier transform. Uniqueness needs no
finite-dimensionality — a complete, second-countable `V` with its Borel σ-algebra suffices —
and it is independent of the existence half, which consumes Bochner's theorem on the
finite-dimensional `V`; the transform itself and the representation predicate live in
`TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.Transform`, which both halves
share.

The proof separates the two variables. The characteristic function of the spatial slice at
time `t` (`TauCeti.charFun_spatialSlice`) is, after the `-2π` rescaling of Mathlib's Fourier
convention, the Laplace--Fourier transform at time `t`; Fourier uniqueness for finite measures
on `V` therefore pins down every spatial slice. That a finite measure on `ℝ≥0 × V` is in turn
determined by its spatial slices is `TauCeti.Measure.ext_of_forall_spatialSlice_eq`, proved
through Laplace determinacy in the time variable.

## Main declarations

* `TauCeti.Measure.ext_of_forall_laplaceFourierTransform_eq`: **finite measures on `ℝ≥0 × V`
  are determined by their Laplace--Fourier transforms**. This is the statement the roadmap
  calls `laplaceFourier_unique`.
* `TauCeti.RepresentsLaplaceFourier.unique`: a function has at most one representing finite
  measure.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
  ("BCR semigroup--Bochner"), whose uniqueness half this file is.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-! ## Uniqueness -/

section Uniqueness

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [SecondCountableTopology V] [CompleteSpace V]

/-- **A finite measure on `ℝ≥0 × V` is determined by its Laplace--Fourier transform.**

This is the uniqueness half of the Berg--Christensen--Ressel representation theorem; the
roadmap calls it `laplaceFourier_unique`. Its proof uses no positive-definiteness: it is pure
transform injectivity, Fourier in the spatial variable and Laplace in the time variable. -/
theorem Measure.ext_of_forall_laplaceFourierTransform_eq {μ ν : Measure (ℝ≥0 × V)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ x, laplaceFourierTransform μ x = laplaceFourierTransform ν x) :
    μ = ν := by
  refine Measure.ext_of_forall_spatialSlice_eq fun t => ?_
  -- Fourier uniqueness on `V` identifies the spatial slice at every time.
  refine MeasureTheory.Measure.ext_of_charFun (funext fun b => ?_)
  have hpi : (-2 * Real.pi) ≠ 0 := by simp
  have hb : ((-2 * Real.pi) • ((-2 * Real.pi)⁻¹ • b) : V) = b := by
    rw [smul_smul, mul_inv_cancel₀ hpi, one_smul]
  rw [← hb, charFun_spatialSlice, charFun_spatialSlice, h]

namespace RepresentsLaplaceFourier

/-- **A function has at most one representing finite measure.** -/
protected theorem unique {μ ν : Measure (ℝ≥0 × V)} {F : ℝ≥0 × V → ℂ}
    (hμ : RepresentsLaplaceFourier μ F) (hν : RepresentsLaplaceFourier ν F) : μ = ν := by
  have := hμ.isFiniteMeasure
  have := hν.isFiniteMeasure
  exact Measure.ext_of_forall_laplaceFourierTransform_eq fun x => by
    rw [← hμ.eq_laplaceFourierTransform x, hν.eq_laplaceFourierTransform x]

end RepresentsLaplaceFourier

end Uniqueness

end TauCeti
