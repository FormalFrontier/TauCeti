/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import TauCeti.Analysis.CompletelyMonotone.Laplace.Kernel
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.Slice
-- Non-public: the standard-Borel conditional kernel and the time-regularity of the spatial
-- Bochner measures are consumed inside proofs only.
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Time.Slice.Measure

/-!
# Berg--Christensen--Ressel representing measures as time kernels

For any measurable spaces `V` and `Ω`, a measure `μ` on `V` together with a kernel `κ` from `V`
to `Ω` assembles into a measure `TauCeti.timeKernelMeasure μ κ` on `Ω × V`. When `Ω` is standard
Borel, every *finite* measure on `Ω × V` admits such a disintegration over its spatial marginal
(`TauCeti.exists_eq_timeKernelMeasure`); the Markov kernel is not literally unique, only up to
equality almost everywhere for that marginal.

For the Berg--Christensen--Ressel reduction, `V` is a finite-dimensional real inner-product
space and `Ω = ℝ≥0`. The spatial marginal is recovered when `κ` is Markov, and the representation
problem is read through this assembly correspondence.

The point is that the spatial slice of `timeKernelMeasure μ κ` at time `t` is computed by a
*fibrewise Laplace transform*: it is `μ` weighted by the density
`q ↦ ∫⁻ p, exp (-t p) ∂(κ q)` (`TauCeti.spatialSlice_timeKernelMeasure`). Since a finite
measure on `ℝ≥0 × V` represents a function `F` exactly when its spatial slices are the Bochner
measures of the time slices of `F`
(`TauCeti.representsLaplaceFourier_iff_forall_spatialSlice_eq`), and since those Bochner
measures decrease in time and are therefore all absolutely continuous with respect to the one at
time `0` (`TauCeti.bochnerMeasure_timeSlice_absolutelyContinuous`), the existence half of the
representation theorem becomes a *fibrewise* Bernstein problem: find a Markov kernel whose
fibrewise Laplace transforms are the Radon--Nikodym densities
`d(bochnerMeasure (F (t, ·))) / d(bochnerMeasure (F (0, ·)))`
(`TauCeti.representsLaplaceFourier_timeKernelMeasure_of_ae_rnDeriv`). The reduction is exact:
`TauCeti.exists_representsLaplaceFourier_iff_exists_timeKernel` states it as an equivalence, so
nothing is lost in passing from the measure to the kernel.

The time-regularity input that a fibrewise Bernstein argument consumes — antitonicity, the
resulting absolute continuity, continuity and alternating finite differences of the slab
masses — is in `TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Time.Slice.Measure`.

## Main declarations

* `TauCeti.timeKernelMeasure`: the measure on `Ω × V` assembled from a base measure and a kernel,
  with `TauCeti.timeKernelMeasure_prod` evaluating it on measurable rectangles.
* `TauCeti.exists_eq_timeKernelMeasure`: every finite measure with standard-Borel first
  coordinate disintegrates as a `TauCeti.timeKernelMeasure` over its second marginal.
* `TauCeti.spatialSlice_timeKernelMeasure`: **its spatial slices are the fibrewise Laplace
  transforms**, `spatialSlice (timeKernelMeasure μ κ) t = μ.withDensity
  (Kernel.laplaceTransform κ t)`. The measure-level transform `TauCeti.laplaceTransformENN` and
  its identification with the usual real-valued Laplace transform are in the infrastructure under
  `TauCeti.Analysis.CompletelyMonotone.Laplace`.
* `TauCeti.representsLaplaceFourier_timeKernelMeasure`: a kernel whose fibrewise Laplace
  transforms are the densities of the spatial Bochner measures produces a
  Berg--Christensen--Ressel representing measure.
* `TauCeti.representsLaplaceFourier_timeKernelMeasure_of_ae_rnDeriv`: the same criterion phrased
  using Radon--Nikodym derivatives.
* `TauCeti.exists_representsLaplaceFourier_iff_exists_timeKernel`: **the reduction**, as an
  equivalence between the existence of a representing measure and the existence of such a
  Markov kernel.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Theorem 4.1.13.

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Milestone 2
  ("BCR semigroup--Bochner"), the existence half.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti

/-! ## The measure assembled from a spatial measure and a time kernel -/

section Assembly

variable {V Ω : Type*} [MeasurableSpace V] [MeasurableSpace Ω]

/-- The measure on `Ω × V` assembled from a measure `μ` on `V` and a kernel `κ` from `V` to
`Ω`: draw the `V` coordinate from `μ`, then the `Ω` coordinate from `κ`, and swap the pair. -/
def timeKernelMeasure (μ : Measure V) (κ : Kernel V Ω) : Measure (Ω × V) :=
  (μ ⊗ₘ κ).map Prod.swap

/-- The assembled measure is the swap-map of Mathlib's composition-product measure. -/
theorem timeKernelMeasure_def (μ : Measure V) (κ : Kernel V Ω) :
    timeKernelMeasure μ κ = (μ ⊗ₘ κ).map Prod.swap :=
  (rfl)

instance isFiniteMeasure_timeKernelMeasure (μ : Measure V) [IsFiniteMeasure μ]
    (κ : Kernel V Ω) [IsFiniteKernel κ] : IsFiniteMeasure (timeKernelMeasure μ κ) := by
  rw [timeKernelMeasure]
  infer_instance

/-- The mass an assembled measure gives to a measurable rectangle: integrate the kernel mass of
the first-coordinate side over the second-coordinate side. -/
theorem timeKernelMeasure_prod (μ : Measure V) [SFinite μ] (κ : Kernel V Ω)
    [IsSFiniteKernel κ] {A : Set Ω} (hA : MeasurableSet A) {B : Set V} (hB : MeasurableSet B) :
    timeKernelMeasure μ κ (A ×ˢ B) = ∫⁻ q in B, κ q A ∂μ := by
  rw [timeKernelMeasure, Measure.map_apply measurable_swap (hA.prod hB),
    Set.preimage_swap_prod, Measure.compProd_apply_prod hB hA]

/-- Integrating against an assembled measure means first integrating over the kernel fibre and
then over the base measure. -/
theorem lintegral_timeKernelMeasure (μ : Measure V) [SFinite μ] (κ : Kernel V Ω)
    [IsSFiniteKernel κ] {f : Ω × V → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(timeKernelMeasure μ κ) = ∫⁻ q, ∫⁻ p, f (p, q) ∂(κ q) ∂μ := by
  rw [timeKernelMeasure, lintegral_map hf measurable_swap,
    Measure.lintegral_compProd
      (show Measurable (fun z : V × Ω => f z.swap) from hf.comp measurable_swap)]
  simp

/-- **The spatial slices of an assembled measure are its fibrewise Laplace transforms.**
Weighting by `exp (-t p)` and integrating out the time coordinate leaves the spatial measure
weighted by the fibrewise Laplace transform of the kernel. -/
@[simp]
theorem spatialSlice_timeKernelMeasure (μ : Measure V) [SFinite μ] (κ : Kernel V ℝ≥0)
    [IsSFiniteKernel κ] (t : ℝ≥0) :
    spatialSlice (timeKernelMeasure μ κ) t = μ.withDensity (Kernel.laplaceTransform κ t) := by
  refine Measure.ext fun B hB => ?_
  have hw : Measurable fun y : ℝ≥0 × V => ENNReal.ofReal (Real.exp (-(t : ℝ) * (y.1 : ℝ))) := by
    fun_prop
  have hws : Measurable fun z : V × ℝ≥0 =>
      ENNReal.ofReal (Real.exp (-(t : ℝ) * (z.swap.1 : ℝ))) :=
    hw.comp measurable_swap
  rw [spatialSlice_apply _ _ hB]
  simp_rw [ENNReal.ofNNReal_toNNReal]
  rw [← Set.univ_prod, timeKernelMeasure,
    setLIntegral_map (MeasurableSet.univ.prod hB) hw measurable_swap,
    Set.preimage_swap_prod,
    Measure.setLIntegral_compProd hws hB MeasurableSet.univ]
  simp_rw [Measure.restrict_univ]
  rw [withDensity_apply _ hB]
  simp [Kernel.laplaceTransform_apply, laplaceTransformENN_apply]

/-- The spatial marginal of an assembled measure is the spatial measure it was assembled
from. -/
@[simp]
theorem snd_timeKernelMeasure (μ : Measure V) [SFinite μ] (κ : Kernel V Ω) [IsMarkovKernel κ] :
    (timeKernelMeasure μ κ).snd = μ := by
  rw [timeKernelMeasure, Measure.snd_map_swap, Measure.fst_compProd]

/-- **Every finite measure on `Ω × V` is assembled from its second marginal and a Markov
kernel.** The kernel is the conditional distribution of the first coordinate given the second,
which exists because `Ω` is a standard Borel space. -/
theorem exists_eq_timeKernelMeasure [StandardBorelSpace Ω] [Nonempty Ω]
    (μ : Measure (Ω × V)) [IsFiniteMeasure μ] :
    ∃ κ : Kernel V Ω, IsMarkovKernel κ ∧ μ = timeKernelMeasure μ.snd κ := by
  set ρ : Measure (V × Ω) := μ.map Prod.swap with hρ
  have hfin : IsFiniteMeasure ρ := by rw [hρ]; infer_instance
  refine ⟨ρ.condKernel, inferInstance, ?_⟩
  rw [timeKernelMeasure, ← Measure.fst_map_swap (ρ := μ), ← hρ, Measure.disintegrate ρ, hρ,
    Measure.map_map measurable_swap measurable_swap, Prod.swap_swap_eq, Measure.map_id]

end Assembly

/-! ## The reduction of the representation problem to a kernel problem -/

section Reduction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {F : ℝ≥0 × V → ℂ}

/-- **A time kernel with the prescribed fibrewise Laplace transforms represents `F`.** If the
fibrewise Laplace transform of `κ` at every time `t` is a density of the spatial Bochner measure
at `t` against the one at time `0`, then assembling `κ` over that time-`0` measure produces a
Berg--Christensen--Ressel representing measure for `F`. Only the time slices of `F` are
constrained: positive definiteness and continuity are what make the spatial Bochner measures
represent them. -/
theorem representsLaplaceFourier_timeKernelMeasure
    (hFpd : ∀ t : ℝ≥0, IsPositiveDefiniteSub fun a => F (t, a))
    (hFcont : ∀ t : ℝ≥0, Continuous fun a => F (t, a)) (κ : Kernel V ℝ≥0)
    [IsSFiniteKernel κ]
    (hκ : ∀ t : ℝ≥0,
      (bochnerMeasure fun a => F (0, a)).withDensity (Kernel.laplaceTransform κ t)
      = bochnerMeasure fun a => F (t, a)) :
    RepresentsLaplaceFourier (timeKernelMeasure (bochnerMeasure fun a => F (0, a)) κ) F := by
  let μ₀ := bochnerMeasure fun a => F (0, a)
  have hsnd : (timeKernelMeasure μ₀ κ).snd = μ₀ := by
    rw [← spatialSlice_zero, spatialSlice_timeKernelMeasure, hκ 0]
  have hfin : IsFiniteMeasure (timeKernelMeasure μ₀ κ) := by
    refine ⟨?_⟩
    rw [← Measure.snd_univ, hsnd]
    exact measure_lt_top _ _
  exact representsLaplaceFourier_of_forall_spatialSlice_eq hfin hFpd hFcont
    fun t => by rw [spatialSlice_timeKernelMeasure, hκ t]

/-- **The same criterion, phrased with Radon--Nikodym derivatives.** A bounded continuous
positive-definite `F` is represented as soon as some s-finite kernel has, at every time, a
fibrewise Laplace transform equal almost everywhere to the Radon--Nikodym derivative of the
spatial Bochner measure at that time against the one at time `0`. This is the exact form in
which a fibrewise Bernstein argument closes the existence half. -/
theorem representsLaplaceFourier_timeKernelMeasure_of_ae_rnDeriv (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (hFbdd : Bornology.IsBounded (range F)) (κ : Kernel V ℝ≥0)
    [IsSFiniteKernel κ]
    (hκ : ∀ t : ℝ≥0, Kernel.laplaceTransform κ t
      =ᵐ[bochnerMeasure fun a => F (0, a)]
        (bochnerMeasure fun a => F (t, a)).rnDeriv (bochnerMeasure fun a => F (0, a))) :
    RepresentsLaplaceFourier (timeKernelMeasure (bochnerMeasure fun a => F (0, a)) κ) F :=
  representsLaplaceFourier_timeKernelMeasure (fun t => hFpd.isPositiveDefiniteSub_timeSlice t)
    (fun t => hFcont.comp (.prodMk_right t)) κ fun t => by
    rw [withDensity_congr_ae (hκ t),
      withDensity_rnDeriv_bochnerMeasure_timeSlice hFpd hFcont hFbdd t]

/-- **The existence half of the Berg--Christensen--Ressel representation is a kernel problem.**
A function on `ℝ≥0 × V` whose time slices are continuous and positive-definite has a
representing finite measure if and only if there is a Markov kernel from `V` to `ℝ≥0` whose
fibrewise Laplace transform at each time `t` is a density of the spatial Bochner measure at time
`t` against the one at time `0`.

The forward direction disintegrates a representing measure over its spatial marginal, which is
the time-`0` Bochner measure; the backward direction assembles the kernel into a measure and
checks its spatial slices. -/
theorem exists_representsLaplaceFourier_iff_exists_timeKernel
    (hFpd : ∀ t : ℝ≥0, IsPositiveDefiniteSub fun a => F (t, a))
    (hFcont : ∀ t : ℝ≥0, Continuous fun a => F (t, a)) :
    (∃ μ : Measure (ℝ≥0 × V), RepresentsLaplaceFourier μ F) ↔
      ∃ κ : Kernel V ℝ≥0, IsMarkovKernel κ ∧ ∀ t : ℝ≥0,
        (bochnerMeasure fun a => F (0, a)).withDensity (Kernel.laplaceTransform κ t)
          = bochnerMeasure fun a => F (t, a) := by
  refine ⟨fun ⟨μ, hμ⟩ => ?_, fun ⟨κ, _, hκ⟩ =>
    ⟨_, representsLaplaceFourier_timeKernelMeasure hFpd hFcont κ hκ⟩⟩
  have := hμ.isFiniteMeasure
  obtain ⟨κ, hmarkov, hassemble⟩ := exists_eq_timeKernelMeasure μ
  have hsnd : μ.snd = bochnerMeasure fun a => F (0, a) := by
    rw [← spatialSlice_zero, hμ.spatialSlice_eq]
  rw [hsnd] at hassemble
  refine ⟨κ, hmarkov, fun t => ?_⟩
  rw [← spatialSlice_timeKernelMeasure, ← hassemble, hμ.spatialSlice_eq]

end Reduction

end TauCeti

end

end
