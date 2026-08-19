/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.Transform
-- Non-public: the two determinacy inputs (Fourier on `V` through the convention conversion,
-- Laplace on `ℝ≥0`), the bound on the Laplace kernel, and the product-`σ`-algebra plumbing, all
-- consumed inside proofs only.
import TauCeti.Analysis.Bochner.Fourier.Convention
import TauCeti.Analysis.CompletelyMonotone.Laplace.Kernel
import TauCeti.Probability.Moments.LaplaceDeterminacy
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Prod

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

The proof separates the two variables. Weighting `μ` by the Laplace factor `exp (-t p)` and
pushing forward to `V` gives a finite spatial measure whose characteristic function is, after
the `-2π` rescaling of Mathlib's Fourier convention, the Laplace--Fourier transform at time
`t`; Fourier uniqueness for finite measures on `V` therefore pins down every spatial slice.
Testing a slice against a measurable set `B ⊆ V` leaves the Laplace transform of the finite
time-marginal of the slab `ℝ≥0 × B`, and Laplace determinacy pins that down in turn. The two
steps together evaluate `μ` on every measurable rectangle, and rectangles form a π-system
generating the product σ-algebra.

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

/-! ## Slicing a measure on `ℝ≥0 × V` -/

section Slices

variable {V : Type*} [MeasurableSpace V]

/-- The **spatial slice** of a measure on `ℝ≥0 × V` at time `t`: weight by the Laplace factor
`exp (-t p)`, then forget the time coordinate. Its characteristic function is the
Laplace--Fourier transform at time `t`, up to the `-2π` Fourier rescaling. -/
private noncomputable def spatialSlice (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) : Measure V :=
  (μ.withDensity fun y =>
    ((Real.toNNReal (Real.exp (-(t : ℝ) * (y.1 : ℝ))) : ℝ≥0) : ℝ≥0∞)).snd

private theorem measurable_laplaceWeight (t : ℝ≥0) :
    Measurable fun y : ℝ≥0 × V => Real.toNNReal (Real.exp (-(t : ℝ) * (y.1 : ℝ))) := by
  fun_prop

private theorem isFiniteMeasure_laplaceWithDensity (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ]
    (t : ℝ≥0) :
    IsFiniteMeasure (μ.withDensity fun y =>
      ((Real.toNNReal (Real.exp (-(t : ℝ) * (y.1 : ℝ))) : ℝ≥0) : ℝ≥0∞)) :=
  isFiniteMeasure_withDensity <| ne_of_lt <|
    calc ∫⁻ y, ((Real.toNNReal (Real.exp (-(t : ℝ) * (y.1 : ℝ))) : ℝ≥0) : ℝ≥0∞) ∂μ
        ≤ ∫⁻ _, 1 ∂μ := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.coe_one, ENNReal.coe_le_coe, ← Real.toNNReal_one, neg_mul]
          exact Real.toNNReal_le_toNNReal (exp_neg_mul_le_one t.coe_nonneg y.1)
      _ < ⊤ := by simp

private instance isFiniteMeasure_spatialSlice (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ]
    (t : ℝ≥0) : IsFiniteMeasure (spatialSlice μ t) :=
  have := isFiniteMeasure_laplaceWithDensity μ t
  Measure.snd.instIsFiniteMeasure

/-- The measure a spatial slice assigns to a measurable set is the Laplace-weighted mass of the
corresponding slab. -/
private theorem spatialSlice_apply (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) {B : Set V}
    (hB : MeasurableSet B) :
    spatialSlice μ t B =
      ∫⁻ y in Prod.snd ⁻¹' B,
        ((Real.toNNReal (Real.exp (-(t : ℝ) * (y.1 : ℝ))) : ℝ≥0) : ℝ≥0∞) ∂μ := by
  rw [spatialSlice, Measure.snd_apply hB, withDensity_apply _ (measurable_snd hB)]

/-- The Laplace-weighted mass of a slab, as a Bochner integral. -/
private theorem ofReal_integral_slab (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ] (t : ℝ≥0)
    {B : Set V} (hB : MeasurableSet B) :
    ENNReal.ofReal (∫ y in Prod.snd ⁻¹' B, Real.exp (-(t : ℝ) * (y.1 : ℝ)) ∂μ) =
      spatialSlice μ t B := by
  have hint : Integrable (fun y : ℝ≥0 × V => Real.exp (-(t : ℝ) * (y.1 : ℝ)))
      (μ.restrict (Prod.snd ⁻¹' B)) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), neg_mul]
    exact exp_neg_mul_le_one t.coe_nonneg y.1
  rw [spatialSlice_apply μ t hB,
    ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun y => (Real.exp_pos _).le)]
  simp_rw [ENNReal.ofNNReal_toNNReal]

/-- The **time-marginal** of the slab `ℝ≥0 × B`, as a measure on `ℝ≥0`. -/
private noncomputable def timeMarginal (μ : Measure (ℝ≥0 × V)) (B : Set V) : Measure ℝ≥0 :=
  (μ.restrict (Prod.snd ⁻¹' B)).fst

private instance isFiniteMeasure_timeMarginal (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ]
    (B : Set V) : IsFiniteMeasure (timeMarginal μ B) :=
  Measure.fst.instIsFiniteMeasure

private theorem integral_exp_timeMarginal (μ : Measure (ℝ≥0 × V)) (B : Set V) (t : ℝ) :
    ∫ p, Real.exp (-t * (p : ℝ)) ∂(timeMarginal μ B) =
      ∫ y in Prod.snd ⁻¹' B, Real.exp (-t * (y.1 : ℝ)) ∂μ := by
  rw [timeMarginal, Measure.fst, integral_map measurable_fst.aemeasurable (by fun_prop)]

private theorem timeMarginal_apply (μ : Measure (ℝ≥0 × V)) {A : Set ℝ≥0} (hA : MeasurableSet A)
    (B : Set V) : timeMarginal μ B A = μ (A ×ˢ B) := by
  rw [timeMarginal, Measure.fst_apply hA, Measure.restrict_apply (measurable_fst hA),
    Set.prod_eq]

end Slices

/-! ## Uniqueness -/

section Uniqueness

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [SecondCountableTopology V] [CompleteSpace V]

omit [InnerProductSpace ℝ V] [SecondCountableTopology V] [CompleteSpace V] in
/-- Integration against a spatial slice reinstates the Laplace weight. -/
private theorem integral_spatialSlice (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) {f : V → ℂ}
    (hf : Continuous f) :
    ∫ q, f q ∂(spatialSlice μ t) = ∫ y, (Real.exp (-(t : ℝ) * (y.1 : ℝ)) : ℂ) * f y.2 ∂μ := by
  rw [spatialSlice, Measure.snd, integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul (measurable_laplaceWeight t)]
  refine integral_congr_ae (.of_forall fun y => ?_)
  -- beta-reduce the two integrands left by `integral_congr_ae`
  dsimp only
  rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_nonneg _), Complex.real_smul]

omit [SecondCountableTopology V] [CompleteSpace V] in
/-- The characteristic function of a spatial slice is the Laplace--Fourier transform, after the
`-2π` rescaling that converts Mathlib's Fourier convention into the characteristic-function
convention. -/
private theorem charFun_spatialSlice (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0)
    (a : V) :
    charFun (spatialSlice μ t) ((-2 * Real.pi) • a) = laplaceFourierTransform μ (t, a) := by
  rw [← integral_fourierAtom_eq_charFun_neg_two_pi_smul,
    integral_spatialSlice μ t (continuous_fourierAtom a), laplaceFourierTransform_apply]
  refine integral_congr_ae (.of_forall fun y => ?_)
  -- beta-reduce the two integrands and the projections of the pair `(t, a)`
  dsimp only
  rw [laplaceAtom_comm, laplaceAtom_def]

/-- **A finite measure on `ℝ≥0 × V` is determined by its Laplace--Fourier transform.**

This is the uniqueness half of the Berg--Christensen--Ressel representation theorem; the
roadmap calls it `laplaceFourier_unique`. Its proof uses no positive-definiteness: it is pure
transform injectivity, Fourier in the spatial variable and Laplace in the time variable. -/
theorem Measure.ext_of_forall_laplaceFourierTransform_eq {μ ν : Measure (ℝ≥0 × V)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ x, laplaceFourierTransform μ x = laplaceFourierTransform ν x) :
    μ = ν := by
  -- Step 1: Fourier uniqueness on `V` identifies every spatial slice.
  have hslice : ∀ t : ℝ≥0, spatialSlice μ t = spatialSlice ν t := by
    intro t
    refine MeasureTheory.Measure.ext_of_charFun (funext fun b => ?_)
    have hpi : (-2 * Real.pi) ≠ 0 := by simp
    have hb : ((-2 * Real.pi) • ((-2 * Real.pi)⁻¹ • b) : V) = b := by
      rw [smul_smul, mul_inv_cancel₀ hpi, one_smul]
    rw [← hb, charFun_spatialSlice, charFun_spatialSlice, h]
  -- Step 2: Laplace determinacy on `ℝ≥0` identifies every measurable rectangle.
  have hrect : ∀ B : Set V, MeasurableSet B → ∀ A : Set ℝ≥0, MeasurableSet A →
      μ (A ×ˢ B) = ν (A ×ˢ B) := by
    intro B hB
    have hmarg : timeMarginal μ B = timeMarginal ν B := by
      refine TauCeti.Measure.ext_of_forall_integral_exp_neg_mul_eq fun t ht => ?_
      rw [integral_exp_timeMarginal, integral_exp_timeMarginal]
      have hofReal := congrArg (fun ρ : Measure V => ρ B) (hslice t.toNNReal)
      rw [← ofReal_integral_slab μ t.toNNReal hB, ← ofReal_integral_slab ν t.toNNReal hB,
        Real.coe_toNNReal t ht] at hofReal
      have hnonneg : ∀ ρ : Measure (ℝ≥0 × V),
          0 ≤ ∫ y in Prod.snd ⁻¹' B, Real.exp (-t * (y.1 : ℝ)) ∂ρ := fun _ =>
        integral_nonneg fun _ => (Real.exp_pos _).le
      exact (ENNReal.ofReal_eq_ofReal_iff (hnonneg μ) (hnonneg ν)).1 hofReal
    intro A hA
    rw [← timeMarginal_apply μ hA B, ← timeMarginal_apply ν hA B, hmarg]
  -- Step 3: rectangles form a π-system generating the product σ-algebra.
  refine MeasureTheory.ext_of_generate_finite _ _root_.generateFrom_prod.symm
    _root_.isPiSystem_prod ?_ ?_
  · rintro s ⟨A, hA, B, hB, rfl⟩
    exact hrect B hB A hA
  · rw [← Set.univ_prod_univ]
    exact hrect univ MeasurableSet.univ univ MeasurableSet.univ

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
