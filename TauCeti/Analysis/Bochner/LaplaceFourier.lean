/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Bochner.FourierConvention
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace
-- Non-public: `Measure.ext_of_forall_integral_exp_neg_mul_eq` is the time half of the
-- determinacy proof, and no statement below mentions it.
import TauCeti.Probability.Moments.LaplaceDeterminacy
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The Laplace--Fourier transform of a measure on `ℝ≥0 × V`

The Berg--Christensen--Ressel representation writes a bounded continuous positive-definite
function on the involutive semigroup `ℝ≥0 × V` as a finite-measure mixture of the separated atoms
`(p, q) ↦ exp (-t p) * exp (-2πi⟪a, q⟫)`. This file defines that mixture — the *Laplace--Fourier
transform* of a measure on `ℝ≥0 × V` — and proves that it determines the measure: a finite
measure on `ℝ≥0 × V` is the only finite measure with its Laplace--Fourier transform.

This is the uniqueness half of `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C,
Milestone 2 ("BCR semigroup--Bochner"), whose statement asks for a *unique* finite measure. The
existence half consumes Bochner's theorem on `V`; uniqueness is independent of it, and the
statement here is about two arbitrary finite measures, with no positive-definiteness hypothesis.

## The argument

Each coordinate is resolved by a determinacy theorem that is already available, and the two are
glued by a weighted marginal.

Fix a time parameter `t : ℝ≥0` and weight `μ` by the *positive* factor `exp (-t p)`; pushing the
weighted measure forward along `Prod.snd` gives a finite measure `laplaceSpatialMarginal μ t` on
`V`. Its characteristic function is a rescaling of the Laplace--Fourier transform at time `t`, so
Mathlib's `MeasureTheory.Measure.ext_of_charFun` identifies the spatial marginals of `μ` and `ν`
at every time parameter. Weighting first and pushing forward second is what keeps this step
inside the world of positive measures: weighting by the oscillating Fourier factor instead would
produce complex measures.

Evaluating the equal marginals on a measurable set `B ⊆ V` turns that identification into
`∫ z in Prod.snd ⁻¹' B, exp (-t z.1) ∂μ = ∫ z in Prod.snd ⁻¹' B, exp (-t z.1) ∂ν`, valid for
every `t`. The two sides are the Laplace transforms of the time marginals of `μ` and `ν` over
`B`, so `TauCeti.Measure.ext_of_forall_integral_exp_neg_mul_eq` — the Laplace determinacy behind
Bernstein uniqueness — gives `μ (S ×ˢ B) = ν (S ×ˢ B)` for every measurable `S`. Measurable
rectangles are a π-system generating the product σ-algebra, so `μ = ν`.

## Main declarations

* `TauCeti.laplaceFourierTransform`: the Laplace--Fourier transform of a measure on `ℝ≥0 × V`.
* `TauCeti.laplaceSpatialMarginal`: the spatial marginal weighted by the Laplace factor.
* `TauCeti.laplaceFourierTransform_eq_charFun`: the transform is a rescaled characteristic
  function of that marginal.
* `TauCeti.Measure.ext_of_forall_laplaceFourierTransform_eq`: **a finite measure on `ℝ≥0 × V` is
  determined by its Laplace--Fourier transform.**
* `TauCeti.laplaceFourier_unique`, `TauCeti.laplaceFourier_unique'`: the representing measure of
  a Laplace--Fourier representation is unique, in the packaged and the explicit-integrand forms.

## Implementation notes

The spatial factor `V` is only assumed to be a complete second-countable real inner-product
space, which is what `MeasureTheory.Measure.ext_of_charFun` needs; the finite-dimensional `V` of
the roadmap statement is the special case.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13.
-/

public section

noncomputable section

open MeasureTheory

open scoped NNReal ENNReal

namespace TauCeti

variable {V : Type*} [MeasurableSpace V]

section Transform

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## The transform -/

/-- The **Laplace--Fourier transform** of a measure on `ℝ≥0 × V`: the mixture against `μ` of the
Berg--Christensen--Ressel atoms `(p, q) ↦ exp (-t p) * exp (-2πi⟪a, q⟫)`, evaluated at the
parameter `x = (t, a)`. -/
public def laplaceFourierTransform (μ : Measure (ℝ≥0 × V)) (x : ℝ≥0 × V) : ℂ :=
  ∫ z, laplaceAtom z.1 x.1 * fourierAtom x.2 z.2 ∂μ

/-- The Laplace--Fourier transform written out with explicit exponentials. -/
theorem laplaceFourierTransform_apply (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) (a : V) :
    laplaceFourierTransform μ (t, a) =
      ∫ z, (Real.exp (-(t : ℝ) * (z.1 : ℝ)) : ℂ) *
        Complex.exp (-2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ z.2 a : ℝ) : ℂ)) ∂μ := by
  simp only [laplaceFourierTransform, laplaceAtom_def, fourierAtom_apply]

@[simp]
theorem laplaceFourierTransform_zero_measure (x : ℝ≥0 × V) :
    laplaceFourierTransform (0 : Measure (ℝ≥0 × V)) x = 0 := by
  simp [laplaceFourierTransform]

/-- At the identity of the involutive semigroup `ℝ≥0 × V` both atoms are `1`, so the transform
returns the total mass. -/
theorem laplaceFourierTransform_zero (μ : Measure (ℝ≥0 × V)) :
    laplaceFourierTransform μ 0 = (μ.real Set.univ : ℂ) := by
  simp [laplaceFourierTransform, Complex.real_smul]

section Dirac

variable [BorelSpace V] [SecondCountableTopology V]

/-- The Laplace--Fourier transform of a point mass is the Berg--Christensen--Ressel atom at that
point. -/
@[simp]
theorem laplaceFourierTransform_dirac (z x : ℝ≥0 × V) :
    laplaceFourierTransform (Measure.dirac z) x = laplaceAtom z.1 x.1 * fourierAtom x.2 z.2 := by
  refine integral_dirac' _ z ?_
  simp only [laplaceAtom_def]
  exact ((Complex.continuous_ofReal.comp (by fun_prop)).mul
    ((continuous_fourierAtom x.2).comp continuous_snd)).stronglyMeasurable

end Dirac

end Transform

/-! ## The Laplace-weighted spatial marginal -/

/-- The spatial marginal of `μ` weighted by the Laplace factor `exp (-t p)` in time: a finite
positive measure on `V` whose characteristic function carries the Laplace--Fourier transform at
time parameter `t`. -/
public def laplaceSpatialMarginal (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) : Measure V :=
  (μ.withDensity fun z => (Real.toNNReal (Real.exp (-(t : ℝ) * (z.1 : ℝ))) : ℝ≥0∞)).map Prod.snd

private theorem measurable_laplaceWeight (t : ℝ≥0) :
    Measurable fun z : ℝ≥0 × V => Real.toNNReal (Real.exp (-(t : ℝ) * (z.1 : ℝ))) :=
  measurable_real_toNNReal.comp (by fun_prop)

omit [MeasurableSpace V] in
private theorem laplaceWeight_le_one (t : ℝ≥0) (z : ℝ≥0 × V) :
    (Real.toNNReal (Real.exp (-(t : ℝ) * (z.1 : ℝ))) : ℝ≥0∞) ≤ 1 := by
  have hnonpos : -(t : ℝ) * (z.1 : ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg) z.1.coe_nonneg
  refine ENNReal.coe_le_one_iff.mpr ?_
  rw [← Real.toNNReal_one]
  exact Real.toNNReal_mono (Real.exp_le_one_iff.mpr hnonpos)

instance isFiniteMeasure_laplaceSpatialMarginal (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ]
    (t : ℝ≥0) : IsFiniteMeasure (laplaceSpatialMarginal μ t) := by
  refine ⟨?_⟩
  rw [laplaceSpatialMarginal, Measure.map_apply measurable_snd MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ z, (Real.toNNReal (Real.exp (-(t : ℝ) * (z.1 : ℝ))) : ℝ≥0∞) ∂μ
      ≤ ∫⁻ _, 1 ∂μ := lintegral_mono (laplaceWeight_le_one t)
    _ = μ Set.univ := by simp
    _ < ⊤ := measure_lt_top μ Set.univ

/-- Integrating against the Laplace-weighted spatial marginal is integrating the Laplace-weighted
spatial lift against the original measure. -/
theorem integral_laplaceSpatialMarginal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) {g : V → E} (hg : StronglyMeasurable g) :
    ∫ v, g v ∂laplaceSpatialMarginal μ t = ∫ z, Real.exp (-(t : ℝ) * (z.1 : ℝ)) • g z.2 ∂μ := by
  rw [laplaceSpatialMarginal, integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable,
    integral_withDensity_eq_integral_smul (measurable_laplaceWeight t)]
  refine integral_congr_ae (.of_forall fun z => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (Real.exp_nonneg _)]

/-- At time parameter `0` there is no weight, so the marginal is the plain spatial pushforward. -/
theorem laplaceSpatialMarginal_zero (μ : Measure (ℝ≥0 × V)) :
    laplaceSpatialMarginal μ 0 = μ.map Prod.snd := by
  rw [laplaceSpatialMarginal]
  congr 1
  rw [show (fun z : ℝ≥0 × V => (Real.toNNReal (Real.exp (-((0 : ℝ≥0) : ℝ) * (z.1 : ℝ))) : ℝ≥0∞))
      = 1 from funext fun z => by simp]
  exact withDensity_one

/-- The mass a Laplace-weighted spatial marginal gives to a measurable set is the corresponding
weighted time integral over the slab above it. -/
theorem measureReal_laplaceSpatialMarginal (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) {B : Set V}
    (hB : MeasurableSet B) :
    (laplaceSpatialMarginal μ t).real B
      = ∫ z in Prod.snd ⁻¹' B, Real.exp (-(t : ℝ) * (z.1 : ℝ)) ∂μ := by
  have h := integral_laplaceSpatialMarginal μ t (g := B.indicator fun _ => (1 : ℝ))
    (stronglyMeasurable_const.indicator hB)
  rw [integral_indicator_const (1 : ℝ) hB, smul_eq_mul, mul_one] at h
  rw [h, ← integral_indicator (hB.preimage measurable_snd)]
  refine integral_congr_ae (.of_forall fun z => ?_)
  by_cases hz : z.2 ∈ B <;> simp [Set.mem_preimage, hz]

section Determinacy

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [BorelSpace V]

/-- The Laplace--Fourier transform is the characteristic function of the Laplace-weighted spatial
marginal, read through the `2π` Fourier convention. -/
theorem laplaceFourierTransform_eq_charFun (μ : Measure (ℝ≥0 × V)) (t : ℝ≥0) (a : V) :
    laplaceFourierTransform μ (t, a)
      = charFun (laplaceSpatialMarginal μ t) ((-2 * Real.pi) • a) := by
  rw [← integral_fourierAtom_eq_charFun_neg_two_pi_smul,
    integral_laplaceSpatialMarginal μ t (continuous_fourierAtom a).stronglyMeasurable,
    laplaceFourierTransform]
  refine integral_congr_ae (.of_forall fun z => ?_)
  simp [laplaceAtom_def, Complex.real_smul]

variable [SecondCountableTopology V] [CompleteSpace V]

/-- Matching Laplace--Fourier transforms give matching Laplace-weighted spatial marginals at every
time parameter. -/
theorem laplaceSpatialMarginal_eq_of_laplaceFourierTransform_eq {μ ν : Measure (ℝ≥0 × V)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ x, laplaceFourierTransform μ x = laplaceFourierTransform ν x) (t : ℝ≥0) :
    laplaceSpatialMarginal μ t = laplaceSpatialMarginal ν t := by
  have hpi : (-2 * Real.pi) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  refine Measure.ext_of_charFun (funext fun a => ?_)
  have hx := h (t, (-2 * Real.pi)⁻¹ • a)
  rwa [laplaceFourierTransform_eq_charFun, laplaceFourierTransform_eq_charFun,
    smul_inv_smul₀ hpi] at hx

/-- Matching Laplace--Fourier transforms give matching Laplace-weighted time integrals over the
slab above every measurable spatial set. -/
private theorem setIntegral_laplaceWeight_eq {μ ν : Measure (ℝ≥0 × V)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ x, laplaceFourierTransform μ x = laplaceFourierTransform ν x) (t : ℝ≥0) {B : Set V}
    (hB : MeasurableSet B) :
    ∫ z in Prod.snd ⁻¹' B, Real.exp (-(t : ℝ) * (z.1 : ℝ)) ∂μ
      = ∫ z in Prod.snd ⁻¹' B, Real.exp (-(t : ℝ) * (z.1 : ℝ)) ∂ν := by
  rw [← measureReal_laplaceSpatialMarginal μ t hB, ← measureReal_laplaceSpatialMarginal ν t hB,
    laplaceSpatialMarginal_eq_of_laplaceFourierTransform_eq h t]

/-- Matching Laplace--Fourier transforms give matching masses on every measurable rectangle. This
is where the time coordinate is resolved: Laplace determinacy on `ℝ≥0` is applied to the time
marginal of the part of the measure lying above `B`. -/
private theorem measure_prod_eq_of_laplaceFourierTransform_eq {μ ν : Measure (ℝ≥0 × V)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ x, laplaceFourierTransform μ x = laplaceFourierTransform ν x) {S : Set ℝ≥0}
    (hS : MeasurableSet S) {B : Set V} (hB : MeasurableSet B) :
    μ (S ×ˢ B) = ν (S ×ˢ B) := by
  have hmass : ∀ ρ : Measure (ℝ≥0 × V),
      ((ρ.restrict (Prod.snd ⁻¹' B)).map Prod.fst) S = ρ (S ×ˢ B) := fun ρ => by
    rw [Measure.map_apply measurable_fst hS, Measure.restrict_apply (measurable_fst hS),
      Set.prod_eq]
  have hlaplace : ∀ (ρ : Measure (ℝ≥0 × V)) (s : ℝ),
      ∫ p, Real.exp (-s * (p : ℝ)) ∂((ρ.restrict (Prod.snd ⁻¹' B)).map Prod.fst)
        = ∫ z in Prod.snd ⁻¹' B, Real.exp (-s * (z.1 : ℝ)) ∂ρ := fun ρ s =>
    integral_map measurable_fst.aemeasurable
      (by fun_prop : Continuous fun p : ℝ≥0 => Real.exp (-s * (p : ℝ))).aestronglyMeasurable
  have : IsFiniteMeasure (μ.restrict (Prod.snd ⁻¹' B)) :=
    isFiniteMeasure_of_le μ Measure.restrict_le_self
  have : IsFiniteMeasure (ν.restrict (Prod.snd ⁻¹' B)) :=
    isFiniteMeasure_of_le ν Measure.restrict_le_self
  have hmarginal : (μ.restrict (Prod.snd ⁻¹' B)).map Prod.fst
      = (ν.restrict (Prod.snd ⁻¹' B)).map Prod.fst := by
    refine Measure.ext_of_forall_integral_exp_neg_mul_eq fun s hs => ?_
    rw [hlaplace, hlaplace]
    have hs' := setIntegral_laplaceWeight_eq h s.toNNReal hB
    rwa [Real.coe_toNNReal s hs] at hs'
  rw [← hmass μ, ← hmass ν, hmarginal]

/-- **A finite measure on `ℝ≥0 × V` is determined by its Laplace--Fourier transform.**

The spatial coordinate is resolved by Fourier uniqueness for finite measures on an inner-product
space, applied to the Laplace-weighted spatial marginals; the time coordinate is then resolved by
Laplace determinacy on `ℝ≥0`. -/
theorem Measure.ext_of_forall_laplaceFourierTransform_eq {μ ν : Measure (ℝ≥0 × V)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ x, laplaceFourierTransform μ x = laplaceFourierTransform ν x) :
    μ = ν := by
  have hrect : ∀ S : Set ℝ≥0, MeasurableSet S → ∀ B : Set V, MeasurableSet B →
      μ (S ×ˢ B) = ν (S ×ˢ B) := fun _ hS _ hB =>
    measure_prod_eq_of_laplaceFourierTransform_eq h hS hB
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨S, hS, B, hB, rfl⟩
    exact hrect S hS B hB
  · simpa using hrect Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ

/-- **Uniqueness in the Berg--Christensen--Ressel representation.** A function on `ℝ≥0 × V` has at
most one finite representing measure in the Laplace--Fourier form. -/
theorem laplaceFourier_unique {F : ℝ≥0 × V → ℂ} {μ ν : Measure (ℝ≥0 × V)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ x, F x = laplaceFourierTransform μ x)
    (hν : ∀ x, F x = laplaceFourierTransform ν x) :
    μ = ν :=
  Measure.ext_of_forall_laplaceFourierTransform_eq fun x => by rw [← hμ, hν]

/-- The uniqueness statement in the shape the roadmap's Berg--Christensen--Ressel milestone uses:
the representing measure is pinned down by the values of the Laplace--Fourier integral at each
pair `(t, a)`, written with explicit exponentials. -/
theorem laplaceFourier_unique' {F : ℝ≥0 → V → ℂ} {μ ν : Measure (ℝ≥0 × V)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ (t : ℝ≥0) (a : V), F t a = ∫ z, (Real.exp (-(t : ℝ) * (z.1 : ℝ)) : ℂ) *
      Complex.exp (-2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ z.2 a : ℝ) : ℂ)) ∂μ)
    (hν : ∀ (t : ℝ≥0) (a : V), F t a = ∫ z, (Real.exp (-(t : ℝ) * (z.1 : ℝ)) : ℂ) *
      Complex.exp (-2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ z.2 a : ℝ) : ℂ)) ∂ν) :
    μ = ν :=
  laplaceFourier_unique (F := fun x => F x.1 x.2)
    (fun x => by rw [laplaceFourierTransform_apply, hμ])
    fun x => by rw [laplaceFourierTransform_apply, hν]

end Determinacy

end TauCeti
