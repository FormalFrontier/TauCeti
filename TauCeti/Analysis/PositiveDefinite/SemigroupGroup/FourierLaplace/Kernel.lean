/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.FourierLaplace.Slice
public import TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Time.Slice.Measure

/-!
# Berg--Christensen--Ressel representing measures as time kernels

Let `V` be a finite-dimensional real inner-product space. A measure on `ℝ≥0 × V` is the same
thing as a measure `μ` on `V` together with a Markov kernel `κ` from `V` to `ℝ≥0`: the pair
`(μ, κ)` assembles into `TauCeti.timeKernelMeasure μ κ`, and every finite measure on `ℝ≥0 × V`
arises this way, by disintegration over its spatial marginal. This file reads the
Berg--Christensen--Ressel representation through that correspondence.

The point is that the spatial slice of `timeKernelMeasure μ κ` at time `t` is computed by a
*fibrewise Laplace transform*: it is `μ` weighted by the density
`q ↦ ∫⁻ p, exp (-t p) ∂(κ q)` (`TauCeti.spatialSlice_timeKernelMeasure`). Since a finite
measure on `ℝ≥0 × V` represents a function `F` exactly when its spatial slices are the Bochner
measures of the time slices of `F`
(`TauCeti.representsLaplaceFourier_iff_forall_spatialSlice_eq`), and since those Bochner
measures decrease in time and are therefore all absolutely continuous with respect to the one at
time `0`, the existence half of the representation theorem becomes a *fibrewise* Bernstein
problem: find a Markov kernel whose fibrewise Laplace transforms are the Radon--Nikodym
densities `d(bochnerMeasure (F (t, ·))) / d(bochnerMeasure (F (0, ·)))`
(`TauCeti.representsLaplaceFourier_timeKernelMeasure_of_ae_rnDeriv`). The reduction is exact:
`TauCeti.exists_representsLaplaceFourier_iff_exists_timeKernel` states it as an equivalence, so
nothing is lost in passing from the measure to the kernel.

The time-regularity input that a fibrewise Bernstein argument consumes — antitonicity,
continuity and alternating finite differences of the slab masses — is in
`TauCeti.Analysis.PositiveDefinite.SemigroupGroup.Time.Slice.Measure`.

## Main declarations

* `TauCeti.kernelLaplaceTransform`: the fibrewise Laplace transform `q ↦ ∫⁻ p, exp (-t p) ∂(κ q)`
  of a kernel from `V` to `ℝ≥0`, with `TauCeti.representsLaplace_kernel` identifying it with the
  Laplace transform of `κ q` in the sense of `TauCeti.RepresentsLaplace`.
* `TauCeti.timeKernelMeasure`: the measure on `ℝ≥0 × V` assembled from a spatial measure and a
  time kernel, with `TauCeti.timeKernelMeasure_prod` evaluating it on measurable rectangles.
* `TauCeti.spatialSlice_timeKernelMeasure`: **its spatial slices are the fibrewise Laplace
  transforms**, `spatialSlice (timeKernelMeasure μ κ) t = μ.withDensity (kernelLaplaceTransform
  κ t)`.
* `TauCeti.representsLaplaceFourier_timeKernelMeasure`: a kernel whose fibrewise Laplace
  transforms are the densities of the spatial Bochner measures produces a
  Berg--Christensen--Ressel representing measure.
* `TauCeti.exists_representsLaplaceFourier_iff_exists_timeKernel`: **the reduction**, as an
  equivalence between the existence of a representing measure and the existence of such a
  Markov kernel.
* `TauCeti.bochnerMeasure_timeSlice_absolutelyContinuous` and
  `TauCeti.withDensity_rnDeriv_bochnerMeasure_timeSlice`: the spatial Bochner measures of a
  bounded continuous positive-definite `F` are absolutely continuous with respect to the one at
  time `0`, so the densities the reduction asks for are Radon--Nikodym derivatives.

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

/-! ## The fibrewise Laplace transform of a kernel -/

section Transform

variable {V : Type*} [MeasurableSpace V]

/-- The **fibrewise Laplace transform** of a kernel `κ` from `V` to `ℝ≥0`: the function
`q ↦ ∫⁻ p, exp (-t p) ∂(κ q)` on `V`. It is the density that turns a spatial measure into the
time-`t` spatial slice of the assembled measure on `ℝ≥0 × V`
(`TauCeti.spatialSlice_timeKernelMeasure`). -/
def kernelLaplaceTransform (κ : Kernel V ℝ≥0) (t : ℝ≥0) (q : V) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (Real.exp (-(t : ℝ) * (p : ℝ))) ∂(κ q)

/-- The defining formula for `TauCeti.kernelLaplaceTransform`. Not `@[simp]`: simp should not
unfold the abstraction into a raw integral. -/
theorem kernelLaplaceTransform_apply (κ : Kernel V ℝ≥0) (t : ℝ≥0) (q : V) :
    kernelLaplaceTransform κ t q = ∫⁻ p, ENNReal.ofReal (Real.exp (-(t : ℝ) * (p : ℝ))) ∂(κ q) :=
  (rfl)

@[fun_prop]
theorem measurable_kernelLaplaceTransform (κ : Kernel V ℝ≥0) (t : ℝ≥0) :
    Measurable (kernelLaplaceTransform κ t) := by
  unfold kernelLaplaceTransform
  fun_prop

/-- At time `0` the exponential weight is trivial, so the fibrewise Laplace transform is the
fibrewise total mass. -/
@[simp]
theorem kernelLaplaceTransform_zero (κ : Kernel V ℝ≥0) (q : V) :
    kernelLaplaceTransform κ 0 q = κ q univ := by
  rw [kernelLaplaceTransform_apply]
  simp

/-- A Markov kernel has fibrewise Laplace transform `1` at time `0`. -/
theorem kernelLaplaceTransform_zero_of_isMarkovKernel (κ : Kernel V ℝ≥0) [IsMarkovKernel κ] :
    kernelLaplaceTransform κ 0 = 1 := by
  funext q
  rw [kernelLaplaceTransform_zero, measure_univ, Pi.one_apply]

/-- The fibrewise Laplace transform is bounded by the fibrewise total mass. -/
theorem kernelLaplaceTransform_le (κ : Kernel V ℝ≥0) (t : ℝ≥0) (q : V) :
    kernelLaplaceTransform κ t q ≤ κ q univ := by
  rw [kernelLaplaceTransform_apply, ← kernelLaplaceTransform_zero κ q,
    kernelLaplaceTransform_apply]
  refine lintegral_mono fun p => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  simpa using mul_nonneg t.coe_nonneg p.coe_nonneg

/-- The fibrewise Laplace transform decreases in time: the weight `exp (-t p)` is nonincreasing
in `t` at every nonnegative frequency `p`. -/
theorem kernelLaplaceTransform_antitone (κ : Kernel V ℝ≥0) (q : V) :
    Antitone fun t : ℝ≥0 => kernelLaplaceTransform κ t q := by
  intro t u htu
  refine lintegral_mono fun p => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  exact mul_le_mul_of_nonneg_right (neg_le_neg (mod_cast htu)) p.coe_nonneg

/-- The fibrewise Laplace transform is finite against a finite kernel. -/
theorem kernelLaplaceTransform_ne_top (κ : Kernel V ℝ≥0) [IsFiniteKernel κ] (t : ℝ≥0) (q : V) :
    kernelLaplaceTransform κ t q ≠ ⊤ :=
  ((kernelLaplaceTransform_le κ t q).trans_lt (measure_lt_top _ _)).ne

/-- The real-valued fibrewise Laplace transform is the Laplace transform of the fibre, in the
sense of `TauCeti.laplaceTransform`. -/
theorem toReal_kernelLaplaceTransform (κ : Kernel V ℝ≥0) [IsFiniteKernel κ] (t : ℝ≥0) (q : V) :
    (kernelLaplaceTransform κ t q).toReal = laplaceTransform (κ q) (t : ℝ) := by
  have h := ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul (κ q) t.coe_nonneg)
    (.of_forall fun p => (Real.exp_pos _).le)
  rw [laplaceTransform_apply, kernelLaplaceTransform_apply]
  simp_rw [neg_mul]
  rw [← h, ENNReal.toReal_ofReal (integral_nonneg fun p => (Real.exp_pos _).le)]

/-- **The fibres of a finite kernel are Laplace-represented by its fibrewise Laplace
transform.** This is the shape in which a Bernstein argument delivers the kernel asked for by
`TauCeti.exists_representsLaplaceFourier_iff_exists_timeKernel`. -/
theorem representsLaplace_kernel (κ : Kernel V ℝ≥0) [IsFiniteKernel κ] (q : V) :
    RepresentsLaplace (κ q) fun t : ℝ => (kernelLaplaceTransform κ t.toNNReal q).toReal := by
  refine representsLaplace_iff.mpr ⟨inferInstance, fun t ht => ?_⟩
  rw [toReal_kernelLaplaceTransform, Real.coe_toNNReal t ht]

end Transform

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
      indicator_of_mem (show (p, q) ∈ Prod.snd ⁻¹' B from hq) _
  · rw [indicator_of_notMem hq]
    refine (lintegral_congr (μ := κ q) fun p => ?_).trans lintegral_zero
    exact indicator_of_notMem (show (p, q) ∉ Prod.snd ⁻¹' B from hq) _

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

/-- **The spatial Bochner measures are absolutely continuous with respect to the one at time
`0`.** They decrease in time, and the time-`0` measure dominates them all. -/
theorem bochnerMeasure_timeSlice_absolutelyContinuous (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (hFbdd : Bornology.IsBounded (range F)) (t : ℝ≥0) :
    (bochnerMeasure fun a => F (t, a)) ≪ bochnerMeasure fun a => F (0, a) :=
  Measure.absolutelyContinuous_of_le
    (bochnerMeasure_timeSlice_antitone hFpd hFcont hFbdd (show (0 : ℝ≥0) ≤ t from zero_le))

/-- The spatial Bochner measure at time `t` is the time-`0` one weighted by a Radon--Nikodym
derivative. These derivatives are the densities the representation problem must realize as
fibrewise Laplace transforms. -/
theorem withDensity_rnDeriv_bochnerMeasure_timeSlice (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (hFbdd : Bornology.IsBounded (range F)) (t : ℝ≥0) :
    (bochnerMeasure fun a => F (0, a)).withDensity
        ((bochnerMeasure fun a => F (t, a)).rnDeriv (bochnerMeasure fun a => F (0, a)))
      = bochnerMeasure fun a => F (t, a) :=
  Measure.withDensity_rnDeriv_eq _ _
    (bochnerMeasure_timeSlice_absolutelyContinuous hFpd hFcont hFbdd t)

/-- **A time kernel with the prescribed fibrewise Laplace transforms represents `F`.** If the
fibrewise Laplace transform of `κ` at every time `t` is a density of the spatial Bochner measure
at `t` against the one at time `0`, then assembling `κ` over that time-`0` measure produces a
Berg--Christensen--Ressel representing measure for `F`. -/
theorem representsLaplaceFourier_timeKernelMeasure (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) (κ : Kernel V ℝ≥0) [IsFiniteKernel κ]
    (hκ : ∀ t : ℝ≥0, (bochnerMeasure fun a => F (0, a)).withDensity (kernelLaplaceTransform κ t)
      = bochnerMeasure fun a => F (t, a)) :
    RepresentsLaplaceFourier (timeKernelMeasure (bochnerMeasure fun a => F (0, a)) κ) F :=
  representsLaplaceFourier_of_forall_spatialSlice_eq inferInstance
    (fun t => hFpd.isPositiveDefiniteSub_timeSlice t)
    (fun t => hFcont.comp (.prodMk_right t))
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
  representsLaplaceFourier_timeKernelMeasure hFpd hFcont κ fun t => by
    rw [withDensity_congr_ae (hκ t),
      withDensity_rnDeriv_bochnerMeasure_timeSlice hFpd hFcont hFbdd t]

/-- **The existence half of the Berg--Christensen--Ressel representation is a kernel problem.**
A bounded continuous positive-definite function on `ℝ≥0 × V` has a representing finite measure
if and only if there is a Markov kernel from `V` to `ℝ≥0` whose fibrewise Laplace transform at
each time `t` is a density of the spatial Bochner measure at time `t` against the one at time
`0`.

The forward direction disintegrates a representing measure over its spatial marginal, which is
the time-`0` Bochner measure; the backward direction assembles the kernel into a measure and
checks its spatial slices. -/
theorem exists_representsLaplaceFourier_iff_exists_timeKernel (hFpd : IsSemigroupGroupPD F)
    (hFcont : Continuous F) :
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
