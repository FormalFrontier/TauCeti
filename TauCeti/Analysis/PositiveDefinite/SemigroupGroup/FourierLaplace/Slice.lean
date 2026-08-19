/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import TauCeti.Analysis.Bochner.BochnerTheorem
public import TauCeti.Analysis.CompletelyMonotone.Laplace.Representation
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.Transform
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Time.Slice
-- Non-public: the Fourier-convention bridge between the atom integral and `charFun`, the bound
-- on the Laplace kernel, Laplace determinacy on `ℝ≥0` and the product-`σ`-algebra plumbing are
-- all consumed inside proofs only.
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import TauCeti.Analysis.Bochner.Fourier.Convention
import TauCeti.Analysis.CompletelyMonotone.Laplace.Kernel
import TauCeti.Probability.Moments.LaplaceDeterminacy

/-!
# Spatial slices of a measure on `ℝ≥0 × V`

The Berg--Christensen--Ressel representation writes a bounded continuous positive-definite
function on the involutive semigroup `ℝ≥0 × V` as the Laplace--Fourier transform

`F (t, a) = ∫ (p, q), exp (-t p) * exp (-2πi⟪a, q⟫) ∂μ`

of a finite measure `μ` on `ℝ≥0 × V`. Freezing the time variable at `t` leaves a *spatial*
representation: weighting `μ` by the Laplace factor `exp (-t p)` and forgetting the time
coordinate produces a finite measure on `V` whose Fourier-convention transform is the time
slice `F (t, ·)`. This file develops that slicing operation, `TauCeti.spatialSlice`, and the
companion time marginal of a slab `ℝ≥0 × B`.

The two structural results are the *necessary conditions* a representing measure satisfies,
each phrased against the representation theorem it consumes:

* by Bochner's theorem on `V`, each spatial slice of a representing measure **is** the Bochner
  measure of the corresponding time slice of `F`, and conversely a finite measure whose spatial
  slices are those Bochner measures represents `F`
  (`TauCeti.representsLaplaceFourier_iff_forall_spatialSlice_eq`);
* the mass a spatial slice assigns to a fixed measurable set is, as a function of the time,
  the Laplace transform of a finite measure on `ℝ≥0`
  (`TauCeti.representsLaplace_timeMarginal`).

Together they say what a representing measure has to look like: its slices are prescribed by
Bochner's theorem, and the resulting set functions `t ↦ μ_t B` are Laplace transforms. The
existence half of the Berg--Christensen--Ressel theorem has to reverse both implications, and
the criterion above is what it discharges last.

## Main declarations

* `TauCeti.spatialSlice`: the Laplace-weighted spatial marginal of a measure on `ℝ≥0 × V`.
* `TauCeti.spatialSlice_apply`, `TauCeti.spatialSlice_real_apply`: the mass of a measurable set
  under a spatial slice, as a lower and as a Bochner integral over the corresponding slab.
* `TauCeti.integral_fourierAtom_spatialSlice`, `TauCeti.charFun_spatialSlice`: the
  Fourier-convention transform, and the characteristic function, of a spatial slice are the
  Laplace--Fourier transform at that time.
* `TauCeti.antitone_spatialSlice`: spatial slices decrease in time.
* `TauCeti.timeMarginal`: the time marginal of the slab `ℝ≥0 × B`.
* `TauCeti.RepresentsLaplaceFourier.spatialSlice_eq` and
  `TauCeti.representsLaplaceFourier_iff_forall_spatialSlice_eq`: the spatial slices of a
  representing measure are the Bochner measures of the time slices, and this property
  characterizes the representing measure.
* `TauCeti.representsLaplace_timeMarginal`: the slab masses of the spatial slices are Laplace
  transforms.
* `TauCeti.Measure.ext_of_forall_spatialSlice_eq`: a finite measure on `ℝ≥0 × V` is determined
  by its spatial slices.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
  ("BCR semigroup--Bochner"), whose existence half these slices reduce to Bochner's theorem
  on `V`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-! ## The spatial slices and the time marginals -/

section Slices

variable {V : Type*} [MeasurableSpace V]

/-- The **spatial slice** of a measure on `ℝ≥0 × V` at time `t`: weight by the Laplace factor
`exp (-t p)`, then forget the time coordinate. Its characteristic function is the
Laplace--Fourier transform at time `t`, up to the `-2π` Fourier rescaling
(`TauCeti.charFun_spatialSlice`). -/
noncomputable def spatialSlice (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) : Measure V :=
  (μ.withDensity fun y =>
    ((Real.toNNReal (Real.exp (-(t : ℝ) * (y.1 : ℝ))) : ℝ≥0) : ℝ≥0∞)).snd

private theorem measurable_laplaceWeight (t : ℝ≥0) :
    Measurable fun y : ℝ≥0 × V => Real.toNNReal (Real.exp (-(t : ℝ) * (y.1 : ℝ))) := by
  fun_prop

omit [MeasurableSpace V] in
/-- The Laplace weight is bounded by `1`, both parameters being nonnegative. -/
private theorem laplaceWeight_le_one (t : ℝ≥0) (y : ℝ≥0 × V) :
    Real.toNNReal (Real.exp (-(t : ℝ) * (y.1 : ℝ))) ≤ 1 := by
  rw [← Real.toNNReal_one, neg_mul]
  exact Real.toNNReal_le_toNNReal (exp_neg_mul_le_one t.coe_nonneg y.1)

private theorem isFiniteMeasure_laplaceWithDensity (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ]
    (t : ℝ≥0) :
    IsFiniteMeasure (μ.withDensity fun y =>
      ((Real.toNNReal (Real.exp (-(t : ℝ) * (y.1 : ℝ))) : ℝ≥0) : ℝ≥0∞)) :=
  isFiniteMeasure_withDensity <| ne_of_lt <|
    calc ∫⁻ y, ((Real.toNNReal (Real.exp (-(t : ℝ) * (y.1 : ℝ))) : ℝ≥0) : ℝ≥0∞) ∂μ
        ≤ ∫⁻ _, 1 ∂μ := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.coe_one, ENNReal.coe_le_coe]
          exact laplaceWeight_le_one t y
      _ < ⊤ := by simp

/-- A spatial slice of a finite measure is finite: the Laplace weight is at most `1`. -/
instance isFiniteMeasure_spatialSlice (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ] (t : ℝ≥0) :
    IsFiniteMeasure (spatialSlice μ t) :=
  have := isFiniteMeasure_laplaceWithDensity μ t
  Measure.snd.instIsFiniteMeasure

/-- The measure a spatial slice assigns to a measurable set is the Laplace-weighted mass of the
corresponding slab. -/
theorem spatialSlice_apply (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) {B : Set V}
    (hB : MeasurableSet B) :
    spatialSlice μ t B =
      ∫⁻ y in Prod.snd ⁻¹' B,
        ((Real.toNNReal (Real.exp (-(t : ℝ) * (y.1 : ℝ))) : ℝ≥0) : ℝ≥0∞) ∂μ := by
  rw [spatialSlice, Measure.snd_apply hB, withDensity_apply _ (measurable_snd hB)]

/-- The Laplace weight is integrable over any slab of a finite measure. -/
private theorem integrableOn_laplaceWeight (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ] (t : ℝ≥0)
    (B : Set V) :
    Integrable (fun y : ℝ≥0 × V => Real.exp (-(t : ℝ) * (y.1 : ℝ)))
      (μ.restrict (Prod.snd ⁻¹' B)) := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), neg_mul]
  exact exp_neg_mul_le_one t.coe_nonneg y.1

/-- The mass of a measurable set under a spatial slice, as a Bochner integral over the slab. -/
theorem spatialSlice_apply_eq_ofReal_integral (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ]
    (t : ℝ≥0) {B : Set V} (hB : MeasurableSet B) :
    spatialSlice μ t B =
      ENNReal.ofReal (∫ y in Prod.snd ⁻¹' B, Real.exp (-(t : ℝ) * (y.1 : ℝ)) ∂μ) := by
  rw [spatialSlice_apply μ t hB, ofReal_integral_eq_lintegral_ofReal
    (integrableOn_laplaceWeight μ t B) (.of_forall fun y => (Real.exp_pos _).le)]
  simp_rw [ENNReal.ofNNReal_toNNReal]

/-- The real-valued mass of a measurable set under a spatial slice. -/
theorem spatialSlice_real_apply (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ] (t : ℝ≥0)
    {B : Set V} (hB : MeasurableSet B) :
    (spatialSlice μ t).real B = ∫ y in Prod.snd ⁻¹' B, Real.exp (-(t : ℝ) * (y.1 : ℝ)) ∂μ := by
  rw [measureReal_def, spatialSlice_apply_eq_ofReal_integral μ t hB,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => (Real.exp_pos _).le)]

/-- At time `0` the Laplace weight is trivial, so the spatial slice is the spatial marginal. -/
@[simp]
theorem spatialSlice_zero (μ : Measure (ℝ≥0 × V)) : spatialSlice μ 0 = μ.snd := by
  have hone : (fun y : ℝ≥0 × V =>
      ((Real.toNNReal (Real.exp (-((0 : ℝ≥0) : ℝ) * (y.1 : ℝ))) : ℝ≥0) : ℝ≥0∞)) = 1 := by
    funext y
    simp
  rw [spatialSlice, hone, withDensity_one]

/-- Every spatial slice of the zero measure is the zero measure. -/
@[simp]
theorem spatialSlice_zero_measure (t : ℝ≥0) :
    spatialSlice (0 : Measure (ℝ≥0 × V)) t = 0 := by
  rw [spatialSlice, withDensity_zero_left, Measure.snd_zero]

/-- **The spatial slices decrease in time**: the Laplace weight `exp (-t p)` is nonincreasing
in `t` at every frequency `p ≥ 0`. -/
theorem antitone_spatialSlice (μ : Measure (ℝ≥0 × V)) : Antitone (spatialSlice μ) := by
  refine fun t u htu => Measure.le_iff.mpr fun B hB => ?_
  rw [spatialSlice_apply μ t hB, spatialSlice_apply μ u hB]
  refine lintegral_mono fun y => ?_
  rw [ENNReal.coe_le_coe]
  refine Real.toNNReal_le_toNNReal (Real.exp_le_exp.mpr ?_)
  exact mul_le_mul_of_nonneg_right (neg_le_neg (mod_cast htu)) y.1.coe_nonneg

/-- Every spatial slice is dominated by the spatial marginal. -/
theorem spatialSlice_le_snd (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) : spatialSlice μ t ≤ μ.snd :=
  spatialSlice_zero μ ▸ antitone_spatialSlice μ t.coe_nonneg

/-- The **time marginal** of the slab `ℝ≥0 × B`, as a measure on `ℝ≥0`. It is the measure whose
Laplace transform records the masses `t ↦ (spatialSlice μ t).real B`
(`TauCeti.representsLaplace_timeMarginal`). -/
noncomputable def timeMarginal (μ : Measure (ℝ≥0 × V)) (B : Set V) : Measure ℝ≥0 :=
  (μ.restrict (Prod.snd ⁻¹' B)).fst

/-- A time marginal of a finite measure is finite. -/
instance isFiniteMeasure_timeMarginal (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ] (B : Set V) :
    IsFiniteMeasure (timeMarginal μ B) :=
  Measure.fst.instIsFiniteMeasure

/-- Integrating the Laplace kernel against a time marginal integrates it over the slab. -/
theorem integral_exp_timeMarginal (μ : Measure (ℝ≥0 × V)) (B : Set V) (t : ℝ) :
    ∫ p, Real.exp (-t * (p : ℝ)) ∂(timeMarginal μ B) =
      ∫ y in Prod.snd ⁻¹' B, Real.exp (-t * (y.1 : ℝ)) ∂μ := by
  rw [timeMarginal, Measure.fst, integral_map measurable_fst.aemeasurable (by fun_prop)]

/-- A time marginal evaluates to the mass of the corresponding rectangle. -/
theorem timeMarginal_apply (μ : Measure (ℝ≥0 × V)) {A : Set ℝ≥0} (hA : MeasurableSet A)
    (B : Set V) : timeMarginal μ B A = μ (A ×ˢ B) := by
  rw [timeMarginal, Measure.fst_apply hA, Measure.restrict_apply (measurable_fst hA),
    Set.prod_eq]

/-- **The slab masses of the spatial slices are Laplace transforms.** For a measurable `B ⊆ V`,
the function `t ↦ (spatialSlice μ t).real B` on `[0, ∞)` is the Laplace transform of the finite
measure `timeMarginal μ B` on `ℝ≥0`. This is the time-direction necessary condition on a
Berg--Christensen--Ressel representing measure. -/
theorem representsLaplace_timeMarginal (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ] {B : Set V}
    (hB : MeasurableSet B) :
    RepresentsLaplace (timeMarginal μ B) fun t : ℝ => (spatialSlice μ t.toNNReal).real B := by
  refine representsLaplace_iff.mpr ⟨inferInstance, fun t ht => ?_⟩
  rw [spatialSlice_real_apply μ _ hB, Real.coe_toNNReal t ht, laplaceTransform_apply]
  simp_rw [← neg_mul]
  rw [integral_exp_timeMarginal]

/-- **A finite measure on `ℝ≥0 × V` is determined by its spatial slices.** Testing a slice
against a measurable set `B` leaves the Laplace transform of the finite time marginal of the
slab `ℝ≥0 × B` (`TauCeti.representsLaplace_timeMarginal`), and Laplace determinacy pins that
marginal down; measurable rectangles then form a π-system generating the product σ-algebra.

Together with `TauCeti.representsLaplaceFourier_iff_forall_spatialSlice_eq`, this reduces the
Berg--Christensen--Ressel representation to the prescribed-slices problem: the representing
measure is the unique finite measure whose spatial slices are the Bochner measures of the time
slices. -/
theorem Measure.ext_of_forall_spatialSlice_eq {μ ν : Measure (ℝ≥0 × V)} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hslice : ∀ t : ℝ≥0, spatialSlice μ t = spatialSlice ν t) : μ = ν := by
  -- Step 1: Laplace determinacy on `ℝ≥0` identifies every measurable rectangle.
  have hrect : ∀ B : Set V, MeasurableSet B → ∀ A : Set ℝ≥0, MeasurableSet A →
      μ (A ×ˢ B) = ν (A ×ˢ B) := by
    intro B hB
    have hmarg : timeMarginal μ B = timeMarginal ν B := by
      refine TauCeti.Measure.ext_of_forall_integral_exp_neg_mul_eq fun t ht => ?_
      rw [integral_exp_timeMarginal, integral_exp_timeMarginal]
      have hofReal : spatialSlice μ t.toNNReal B = spatialSlice ν t.toNNReal B := by
        rw [hslice]
      rw [spatialSlice_apply_eq_ofReal_integral μ _ hB,
        spatialSlice_apply_eq_ofReal_integral ν _ hB, Real.coe_toNNReal t ht] at hofReal
      have hnonneg : ∀ ρ : Measure (ℝ≥0 × V),
          0 ≤ ∫ y in Prod.snd ⁻¹' B, Real.exp (-t * (y.1 : ℝ)) ∂ρ := fun _ =>
        integral_nonneg fun _ => (Real.exp_pos _).le
      exact (ENNReal.ofReal_eq_ofReal_iff (hnonneg μ) (hnonneg ν)).1 hofReal
    intro A hA
    rw [← timeMarginal_apply μ hA B, ← timeMarginal_apply ν hA B, hmarg]
  -- Step 2: rectangles form a π-system generating the product σ-algebra.
  refine MeasureTheory.ext_of_generate_finite _ _root_.generateFrom_prod.symm
    _root_.isPiSystem_prod ?_ ?_
  · rintro s ⟨A, hA, B, hB, rfl⟩
    exact hrect B hB A hA
  · rw [← Set.univ_prod_univ]
    exact hrect univ MeasurableSet.univ univ MeasurableSet.univ

end Slices

/-! ## Integration against a spatial slice -/

section Integral

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

/-- Integration against a spatial slice reinstates the Laplace weight. -/
theorem integral_spatialSlice (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) {f : V → ℂ}
    (hf : Continuous f) :
    ∫ q, f q ∂(spatialSlice μ t) = ∫ y, (Real.exp (-(t : ℝ) * (y.1 : ℝ)) : ℂ) * f y.2 ∂μ := by
  rw [spatialSlice, Measure.snd, integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul (measurable_laplaceWeight t)]
  refine integral_congr_ae (.of_forall fun y => ?_)
  -- beta-reduce the two integrands left by `integral_congr_ae`
  dsimp only
  rw [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_nonneg _), Complex.real_smul]

end Integral

section Transform

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V]

/-- **The Fourier-convention transform of a spatial slice is the Laplace--Fourier transform.**
Freezing the time variable at `t` turns the two-variable transform into the spatial transform
of the slice at `t`. -/
theorem integral_fourierAtom_spatialSlice (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) (a : V) :
    ∫ q, fourierAtom a q ∂(spatialSlice μ t) = laplaceFourierTransform μ (t, a) := by
  rw [integral_spatialSlice μ t (continuous_fourierAtom a), laplaceFourierTransform_apply]
  refine integral_congr_ae (.of_forall fun y => ?_)
  -- beta-reduce the two integrands and the projections of the pair `(t, a)`
  dsimp only
  rw [laplaceAtom_comm, laplaceAtom_def]

/-- The characteristic function of a spatial slice is the Laplace--Fourier transform, after the
`-2π` rescaling that converts Mathlib's Fourier convention into the characteristic-function
convention. -/
theorem charFun_spatialSlice (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) (a : V) :
    charFun (spatialSlice μ t) ((-2 * Real.pi) • a) = laplaceFourierTransform μ (t, a) := by
  rw [← integral_fourierAtom_eq_charFun_neg_two_pi_smul, integral_fourierAtom_spatialSlice]

end Transform

/-! ## The spatial slices of a representing measure -/

section Bochner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure (ℝ≥0 × V)} {F : ℝ≥0 × V → ℂ}

/-- **The spatial slices of a Berg--Christensen--Ressel representing measure are the Bochner
measures of the time slices.** Bochner's theorem on `V` has a unique representing measure, and
the spatial slice at `t` represents the time slice `F (t, ·)`, so the two coincide. -/
theorem RepresentsLaplaceFourier.spatialSlice_eq (h : RepresentsLaplaceFourier μ F) (t : ℝ≥0) :
    spatialSlice μ t = bochnerMeasure fun a => F (t, a) :=
  have := h.isFiniteMeasure
  eq_bochnerMeasure _ fun a => by
    rw [integral_fourierAtom_spatialSlice, ← h.eq_laplaceFourierTransform (t, a)]

/-- **The converse.** A finite measure whose spatial slices are the Bochner measures of the time
slices of a continuous positive-definite `F` represents `F`. Positive definiteness and
continuity enter through Bochner's theorem, which is what makes those Bochner measures
represent the slices. -/
theorem representsLaplaceFourier_of_forall_spatialSlice_eq (hμ : IsFiniteMeasure μ)
    (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F)
    (h : ∀ t : ℝ≥0, spatialSlice μ t = bochnerMeasure fun a => F (t, a)) :
    RepresentsLaplaceFourier μ F := by
  refine representsLaplaceFourier_iff.mpr ⟨hμ, fun x => ?_⟩
  obtain ⟨hker, hslice⟩ := hFpd.posSemidef_timeSlice_and_continuous hFcont x.1
  rw [← Prod.mk.eta (p := x), ← integral_fourierAtom_spatialSlice, h x.1,
    integral_fourierAtom_bochnerMeasure hslice (IsPositiveDefiniteSub.of_posSemidef hker) x.2]

/-- **The slice criterion for the Berg--Christensen--Ressel representation.** A finite measure
on `ℝ≥0 × V` represents a continuous positive-definite `F` by its Laplace--Fourier transform if
and only if each of its spatial slices is the Bochner measure of the corresponding time slice
of `F`. The existence half of the representation theorem is exactly the problem of producing a
finite measure with these prescribed slices. -/
theorem representsLaplaceFourier_iff_forall_spatialSlice_eq (hμ : IsFiniteMeasure μ)
    (hFpd : IsSemigroupGroupPD F) (hFcont : Continuous F) :
    RepresentsLaplaceFourier μ F ↔
      ∀ t : ℝ≥0, spatialSlice μ t = bochnerMeasure fun a => F (t, a) :=
  ⟨fun h => h.spatialSlice_eq,
    representsLaplaceFourier_of_forall_spatialSlice_eq hμ hFpd hFcont⟩

omit [FiniteDimensional ℝ V] in
/-- The total mass of the spatial slice at `t` is the value of `F` on the time axis. -/
theorem RepresentsLaplaceFourier.spatialSlice_real_univ (h : RepresentsLaplaceFourier μ F)
    (t : ℝ≥0) : (spatialSlice μ t).real univ = (F (t, 0)).re := by
  have := h.isFiniteMeasure
  have hrep := h.eq_laplaceFourierTransform (t, 0)
  rw [← integral_fourierAtom_spatialSlice μ t 0] at hrep
  simp only [fourierAtom_zero_left, integral_const, Complex.real_smul, mul_one] at hrep
  rw [hrep, Complex.ofReal_re]

/-- **The Bochner measures of the time slices have Laplace-transform masses.** Reading
`TauCeti.representsLaplace_timeMarginal` through the identification of the spatial slices with
the Bochner measures: for a represented `F` and a measurable `B ⊆ V`, the mass that the Bochner
measure of the time slice `F (t, ·)` assigns to `B` is, as a function of `t`, the Laplace
transform of a finite measure on `ℝ≥0`. -/
theorem RepresentsLaplaceFourier.representsLaplace_bochnerMeasure
    (h : RepresentsLaplaceFourier μ F) {B : Set V} (hB : MeasurableSet B) :
    RepresentsLaplace (timeMarginal μ B)
      fun t : ℝ => (bochnerMeasure fun a => F (t.toNNReal, a)).real B := by
  have := h.isFiniteMeasure
  simpa only [h.spatialSlice_eq] using representsLaplace_timeMarginal μ hB

end Bochner

end TauCeti
