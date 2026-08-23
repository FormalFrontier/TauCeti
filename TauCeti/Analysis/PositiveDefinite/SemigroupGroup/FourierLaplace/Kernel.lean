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

Let `V` be a finite-dimensional real inner-product space. A measure `μ` on `V` together with a
Markov kernel `κ` from `V` to `ℝ≥0` assembles into a measure `TauCeti.timeKernelMeasure μ κ` on
`ℝ≥0 × V`, and conversely every *finite* measure on `ℝ≥0 × V` admits such a disintegration over
its spatial marginal (`TauCeti.exists_eq_timeKernelMeasure`); the kernel is not literally unique,
only up to equality almost everywhere for that marginal. This file reads the
Berg--Christensen--Ressel representation through that correspondence.

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

* `TauCeti.timeKernelMeasure`: the measure on `ℝ≥0 × V` assembled from a spatial measure and a
  time kernel, with `TauCeti.timeKernelMeasure_prod` evaluating it on measurable rectangles.
* `TauCeti.spatialSlice_timeKernelMeasure`: **its spatial slices are the fibrewise Laplace
  transforms**, `spatialSlice (timeKernelMeasure μ κ) t = μ.withDensity (kernelLaplaceTransform
  κ t)`. The fibrewise Laplace transform `TauCeti.kernelLaplaceTransform` itself, and its
  identification with the Laplace transform of the fibre
  (`TauCeti.representsLaplace_kernel`), are in the Laplace infrastructure under
  `TauCeti.Analysis.CompletelyMonotone.Laplace`.
* `TauCeti.representsLaplaceFourier_timeKernelMeasure`: a kernel whose fibrewise Laplace
  transforms are the densities of the spatial Bochner measures produces a
  Berg--Christensen--Ressel representing measure.
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

variable {V : Type*} [MeasurableSpace V]

/-- The measure on `ℝ≥0 × V` assembled from a measure `μ` on `V` and a kernel `κ` from `V` to
`ℝ≥0`: draw the spatial coordinate from `μ`, then the time coordinate from `κ`, and record the
pair in the order `(time, space)` that the Berg--Christensen--Ressel semigroup `ℝ≥0 × V`
uses. -/
def timeKernelMeasure (μ : Measure V) (κ : Kernel V ℝ≥0) : Measure (ℝ≥0 × V) :=
  (μ ⊗ₘ κ).map Prod.swap

instance isFiniteMeasure_timeKernelMeasure (μ : Measure V) [IsFiniteMeasure μ]
    (κ : Kernel V ℝ≥0) [IsFiniteKernel κ] : IsFiniteMeasure (timeKernelMeasure μ κ) := by
  rw [timeKernelMeasure]
  infer_instance

/-- The mass an assembled measure gives to a measurable rectangle: integrate the kernel mass of
the time side over the spatial side. -/
theorem timeKernelMeasure_prod (μ : Measure V) [SFinite μ] (κ : Kernel V ℝ≥0)
    [IsSFiniteKernel κ] {A : Set ℝ≥0} (hA : MeasurableSet A) {B : Set V} (hB : MeasurableSet B) :
    timeKernelMeasure μ κ (A ×ˢ B) = ∫⁻ q in B, κ q A ∂μ := by
  have hswap : Prod.swap ⁻¹' (A ×ˢ B) = B ×ˢ A := by
    ext z
    simp
  rw [timeKernelMeasure, Measure.map_apply measurable_swap (hA.prod hB), hswap,
    Measure.compProd_apply (hB.prod hA), ← lintegral_indicator hB]
  refine lintegral_congr fun q => ?_
  by_cases hq : q ∈ B
  · rw [indicator_of_mem hq, mk_preimage_prod_right hq]
  · rw [indicator_of_notMem hq, mk_preimage_prod_right_eq_empty hq, measure_empty]

/-- **The spatial slices of an assembled measure are its fibrewise Laplace transforms.**
Weighting by `exp (-t p)` and integrating out the time coordinate leaves the spatial measure
weighted by the fibrewise Laplace transform of the kernel. -/
theorem spatialSlice_timeKernelMeasure (μ : Measure V) [SFinite μ] (κ : Kernel V ℝ≥0)
    [IsSFiniteKernel κ] (t : ℝ≥0) :
    spatialSlice (timeKernelMeasure μ κ) t = μ.withDensity (kernelLaplaceTransform κ t) := by
  refine Measure.ext fun B hB => ?_
  have hw : Measurable fun y : ℝ≥0 × V => ENNReal.ofReal (Real.exp (-(t : ℝ) * (y.1 : ℝ))) := by
    fun_prop
  have hind := hw.indicator (measurable_snd hB)
  have hswap : Measurable fun z : V × ℝ≥0 =>
      (Prod.snd ⁻¹' B).indicator
        (fun y : ℝ≥0 × V => ENNReal.ofReal (Real.exp (-(t : ℝ) * (y.1 : ℝ)))) z.swap :=
    hind.comp measurable_swap
  rw [spatialSlice_apply _ _ hB]
  simp_rw [ENNReal.ofNNReal_toNNReal]
  rw [← lintegral_indicator (measurable_snd hB), timeKernelMeasure,
    lintegral_map hind measurable_swap, Measure.lintegral_compProd hswap,
    withDensity_apply _ hB, ← lintegral_indicator hB]
  simp_rw [Prod.swap_prod_mk]
  refine lintegral_congr fun q => ?_
  by_cases hq : q ∈ B
  · rw [indicator_of_mem hq, kernelLaplaceTransform_apply]
    exact lintegral_congr fun p =>
      indicator_of_mem (Set.mem_preimage.mpr hq) _
  · rw [indicator_of_notMem hq]
    refine (lintegral_congr (μ := κ q) fun p => ?_).trans lintegral_zero
    exact indicator_of_notMem (fun h => hq (Set.mem_preimage.mp h)) _

/-- The spatial marginal of an assembled measure is the spatial measure it was assembled
from. -/
@[simp]
theorem snd_timeKernelMeasure (μ : Measure V) [SFinite μ] (κ : Kernel V ℝ≥0) [IsMarkovKernel κ] :
    (timeKernelMeasure μ κ).snd = μ := by
  rw [← spatialSlice_zero, spatialSlice_timeKernelMeasure,
    kernelLaplaceTransform_zero_of_isMarkovKernel, withDensity_one]

/-- **Every finite measure on `ℝ≥0 × V` is assembled from its spatial marginal and a Markov
kernel.** The kernel is the conditional distribution of the time coordinate given the spatial
one, which exists because `ℝ≥0` is a standard Borel space. -/
theorem exists_eq_timeKernelMeasure (μ : Measure (ℝ≥0 × V)) [IsFiniteMeasure μ] :
    ∃ κ : Kernel V ℝ≥0, IsMarkovKernel κ ∧ μ = timeKernelMeasure μ.snd κ := by
  set ρ : Measure (V × ℝ≥0) := μ.map Prod.swap with hρ
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
    (hFcont : ∀ t : ℝ≥0, Continuous fun a => F (t, a)) (κ : Kernel V ℝ≥0) [IsFiniteKernel κ]
    (hκ : ∀ t : ℝ≥0, (bochnerMeasure fun a => F (0, a)).withDensity (kernelLaplaceTransform κ t)
      = bochnerMeasure fun a => F (t, a)) :
    RepresentsLaplaceFourier (timeKernelMeasure (bochnerMeasure fun a => F (0, a)) κ) F :=
  representsLaplaceFourier_of_forall_spatialSlice_eq inferInstance hFpd hFcont
    fun t => by rw [spatialSlice_timeKernelMeasure, hκ t]

/-- **The same criterion, phrased with Radon--Nikodym derivatives.** A bounded continuous
positive-definite `F` is represented as soon as some finite kernel has, at every time, a
fibrewise Laplace transform equal almost everywhere to the Radon--Nikodym derivative of the
spatial Bochner measure at that time against the one at time `0`. This is the exact form in
which a fibrewise Bernstein argument closes the existence half. -/
theorem representsLaplaceFourier_timeKernelMeasure_of_ae_rnDeriv (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (hFbdd : Bornology.IsBounded (range F)) (κ : Kernel V ℝ≥0)
    [IsFiniteKernel κ]
    (hκ : ∀ t : ℝ≥0, kernelLaplaceTransform κ t
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
        (bochnerMeasure fun a => F (0, a)).withDensity (kernelLaplaceTransform κ t)
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
