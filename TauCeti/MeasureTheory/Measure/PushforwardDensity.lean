/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# The density of a set upstairs, seen on the base of a measure-preserving map

Let `f : Ω' → Ω` push a finite measure `ν` forward to `μ`, and let `s ⊆ Ω'` be a set upstairs.
The part of `ν` carried by `s` pushes forward to a measure `≤ μ`, so it has a Radon–Nikodym
density with respect to `μ` taking values in `[0, 1]`. That density is `pushDensity f ν μ s`, and
it is characterised by

`∫ a, pushDensity f ν μ s a * g a ∂μ = ∫ x in s, g (f x) ∂ν`

for every bounded measurable `g : Ω → ℝ` (`integral_pushDensity_mul`). In probabilistic language
it is the conditional probability of `s` given `f`, read as a function on the base: composing it
with `f` gives a version of `ν[s.indicator 1 | comap f]`. Nothing here needs that reading, so the
conditional-expectation machinery is not used; the elementary Radon–Nikodym route is enough.

**Truncation is deliberate.** The definition applies `min 1` to the Radon–Nikodym derivative so
that the `[0, 1]` bounds hold *everywhere*, not merely almost everywhere. Consumers pair this
function against a kernel and need a strict pointwise bound to feed an extremal argument; the
truncation is invisible to every integral statement below, because it changes the derivative only
on a `μ`-null set (`pushDensity_ae_eq_rnDeriv`).

## Main definitions

* `TauCeti.MeasureTheory.pushDensity` — the `[0, 1]`-valued density on the base of the part of `ν`
  carried by a set upstairs.

## Main results

* `TauCeti.MeasureTheory.integral_pushDensity_mul` — the characterising identity: integrating
  against the density downstairs computes the integral over the set upstairs. No measurability of
  the set is needed.
* `TauCeti.MeasureTheory.pushDensity_ae_eq_rnDeriv` — the truncation is a.e. invisible.
* `TauCeti.MeasureTheory.integral_pushDensity` — the density integrates to the measure of the set,
  the case `g = 1`.
* `TauCeti.MeasureTheory.pushDensity_preimage` and `TauCeti.MeasureTheory.pushDensity_univ` — on a
  preimage the density collapses to an indicator, so the construction extends the trivial case.
* `TauCeti.MeasureTheory.pushDensity_prod_fst` — on a product carrier the density of a rectangle
  is a genuinely fractional multiple of an indicator, so no such collapse holds in general.

## References

* Mathlib's `MeasureTheory.toReal_rnDeriv_map` identifies the Radon–Nikodym derivative of a
  pushforward with a conditional expectation; it is the abstract form of the reading above and is
  not needed for any statement here.
-/

public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal

namespace TauCeti

namespace MeasureTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {μ : Measure Ω} {ν : Measure Ω'} {f : Ω' → Ω}

/-- The **density on the base of the part of `ν` carried by `s`**: the Radon–Nikodym derivative of
`(ν.restrict s).map f` with respect to `μ`, truncated to `[0, 1]`.

When `f` pushes `ν` forward to `μ` the truncation is a.e. invisible
(`pushDensity_ae_eq_rnDeriv`) and the function is characterised by
`integral_pushDensity_mul`. The measures are explicit arguments because neither is determined by
the others: `μ` is not forced to be `ν.map f` by the type. -/
def pushDensity (f : Ω' → Ω) (ν : Measure Ω') (μ : Measure Ω) (s : Set Ω') (a : Ω) : ℝ :=
  min 1 (((ν.restrict s).map f).rnDeriv μ a).toReal

/-- The defining formula of `pushDensity`. -/
theorem pushDensity_def (f : Ω' → Ω) (ν : Measure Ω') (μ : Measure Ω) (s : Set Ω') (a : Ω) :
    pushDensity f ν μ s a = min 1 (((ν.restrict s).map f).rnDeriv μ a).toReal := (rfl)

/-- The density is measurable, being a truncated Radon–Nikodym derivative. -/
@[fun_prop]
theorem measurable_pushDensity (f : Ω' → Ω) (ν : Measure Ω') (μ : Measure Ω) (s : Set Ω') :
    Measurable (pushDensity f ν μ s) :=
  measurable_const.min (Measure.measurable_rnDeriv _ _).ennreal_toReal

/-- The density is nonnegative everywhere. -/
theorem pushDensity_nonneg (f : Ω' → Ω) (ν : Measure Ω') (μ : Measure Ω) (s : Set Ω') (a : Ω) :
    0 ≤ pushDensity f ν μ s a :=
  le_min zero_le_one ENNReal.toReal_nonneg

/-- The density is at most `1` everywhere: this is what the truncation buys. -/
theorem pushDensity_le_one (f : Ω' → Ω) (ν : Measure Ω') (μ : Measure Ω) (s : Set Ω') (a : Ω) :
    pushDensity f ν μ s a ≤ 1 :=
  min_le_left _ _

/-- The density is `[0, 1]`-valued everywhere, in the packaged form the extremal arguments of the
cut-norm theory consume. -/
theorem pushDensity_mem_Icc (f : Ω' → Ω) (ν : Measure Ω') (μ : Measure Ω) (s : Set Ω') (a : Ω) :
    pushDensity f ν μ s a ∈ Icc (0 : ℝ) 1 :=
  ⟨pushDensity_nonneg f ν μ s a, pushDensity_le_one f ν μ s a⟩

/-- Pushing forward the part of `ν` carried by `s` gives a measure below `μ`.  This is the whole
reason the density is `[0, 1]`-valued, and it needs no hypothesis on `s`. -/
theorem map_restrict_le_of_measurePreserving (hf : MeasurePreserving f ν μ) (s : Set Ω') :
    (ν.restrict s).map f ≤ μ := by
  rw [← hf.map_eq]
  exact Measure.map_mono Measure.restrict_le_self hf.measurable

/-- The pushforward of the restriction is absolutely continuous with respect to `μ`. -/
theorem map_restrict_absolutelyContinuous (hf : MeasurePreserving f ν μ) (s : Set Ω') :
    (ν.restrict s).map f ≪ μ :=
  Measure.absolutelyContinuous_of_le (map_restrict_le_of_measurePreserving hf s)

/-- **The truncation in `pushDensity` is a.e. invisible.**  The underlying Radon–Nikodym derivative
is already at most `1` almost everywhere, because the measure it differentiates is below `μ`. -/
theorem pushDensity_ae_eq_rnDeriv [IsFiniteMeasure ν] (hf : MeasurePreserving f ν μ) (s : Set Ω') :
    pushDensity f ν μ s =ᵐ[μ] fun a => (((ν.restrict s).map f).rnDeriv μ a).toReal := by
  have hμ : IsFiniteMeasure μ := by
    rw [← hf.map_eq]; exact Measure.isFiniteMeasure_map _ _
  filter_upwards [Measure.rnDeriv_le_one_of_le (map_restrict_le_of_measurePreserving hf s)]
    with a ha
  have h1 : (((ν.restrict s).map f).rnDeriv μ a).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top ha
  exact min_eq_right h1

/-- **The characterising identity of `pushDensity`.**  Integrating a function on the base against
the density computes its integral, composed with `f`, over the set upstairs.

The set is arbitrary: `Measure.restrict` and every step of the computation are insensitive to its
measurability. -/
theorem integral_pushDensity_mul [IsFiniteMeasure ν] (hf : MeasurePreserving f ν μ) (s : Set Ω')
    {g : Ω → ℝ} (hg : Measurable g) :
    ∫ a, pushDensity f ν μ s a * g a ∂μ = ∫ x in s, g (f x) ∂ν := by
  have hμ : IsFiniteMeasure μ := by
    rw [← hf.map_eq]; exact Measure.isFiniteMeasure_map _ _
  have hρ : IsFiniteMeasure ((ν.restrict s).map f) := Measure.isFiniteMeasure_map _ _
  calc ∫ a, pushDensity f ν μ s a * g a ∂μ
      = ∫ a, (((ν.restrict s).map f).rnDeriv μ a).toReal * g a ∂μ :=
        integral_congr_ae (by
          filter_upwards [pushDensity_ae_eq_rnDeriv hf s] with a ha
          rw [ha])
    _ = ∫ a, g a ∂((ν.restrict s).map f) :=
        integral_toReal_rnDeriv_mul (map_restrict_absolutelyContinuous hf s)
    _ = ∫ x in s, g (f x) ∂ν :=
        integral_map hf.measurable.aemeasurable hg.aestronglyMeasurable

/-- The density integrates to the measure of the set it came from: the case `g = 1` of
`integral_pushDensity_mul`. -/
theorem integral_pushDensity [IsFiniteMeasure ν] (hf : MeasurePreserving f ν μ) (s : Set Ω') :
    ∫ a, pushDensity f ν μ s a ∂μ = ν.real s := by
  have h := integral_pushDensity_mul hf s (g := fun _ => (1 : ℝ)) measurable_const
  simpa [Measure.restrict_apply_univ] using h

/-- **On a preimage the density is an indicator.**  Nothing is lost when the set upstairs is
already cut out by a set on the base, so `pushDensity` extends the trivial case rather than
replacing it. -/
theorem pushDensity_preimage [IsFiniteMeasure ν] (hf : MeasurePreserving f ν μ) {t : Set Ω}
    (ht : MeasurableSet t) :
    pushDensity f ν μ (f ⁻¹' t) =ᵐ[μ] t.indicator 1 := by
  have hμ : IsFiniteMeasure μ := by
    rw [← hf.map_eq]; exact Measure.isFiniteMeasure_map _ _
  have hmap : (ν.restrict (f ⁻¹' t)).map f = μ.restrict t := by
    rw [← Measure.restrict_map hf.measurable ht, hf.map_eq]
  have hrn : ((ν.restrict (f ⁻¹' t)).map f).rnDeriv μ =ᵐ[μ] t.indicator 1 := by
    rw [hmap]; exact Measure.rnDeriv_restrict_self μ ht
  filter_upwards [pushDensity_ae_eq_rnDeriv hf (f ⁻¹' t), hrn] with a ha hb
  rw [ha, hb]
  by_cases hat : a ∈ t <;> simp [hat]

/-- The whole carrier upstairs has density `1`. -/
theorem pushDensity_univ [IsFiniteMeasure ν] (hf : MeasurePreserving f ν μ) :
    pushDensity f ν μ univ =ᵐ[μ] 1 := by
  have h := pushDensity_preimage hf (t := univ) MeasurableSet.univ
  simpa using h

/-- **The density genuinely takes fractional values.**  On a product carrier projected to its first
factor, a rectangle `s ×ˢ t` has density `ν.real t · 1_s`: the second factor contributes its mass,
not an indicator.  Together with `pushDensity_preimage` this pins the construction down — an
indicator of a set on the base would be wrong whenever `0 < ν.real t < 1`. -/
theorem pushDensity_prod_fst [IsFiniteMeasure μ] [IsProbabilityMeasure ν] {s : Set Ω}
    (hs : MeasurableSet s) (t : Set Ω') :
    pushDensity Prod.fst (μ.prod ν) μ (s ×ˢ t) =ᵐ[μ] fun a => ν.real t * s.indicator 1 a := by
  have hf : MeasurePreserving (Prod.fst : Ω × Ω' → Ω) (μ.prod ν) μ := measurePreserving_fst
  have hmap : ((μ.prod ν).restrict (s ×ˢ t)).map Prod.fst
      = μ.withDensity (fun a => ν t * s.indicator 1 a) := by
    refine Measure.ext fun A hA => ?_
    have hcut : (Prod.fst : Ω × Ω' → Ω) ⁻¹' A ∩ s ×ˢ t = (A ∩ s) ×ˢ t := by
      ext p; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]; tauto
    rw [Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA), hcut,
      Measure.prod_prod, withDensity_apply _ hA,
      lintegral_const_mul' _ _ (measure_ne_top ν t), lintegral_indicator hs]
    simp [Measure.restrict_apply hs, Set.inter_comm, mul_comm]
  have hrn : (((μ.prod ν).restrict (s ×ˢ t)).map Prod.fst).rnDeriv μ
      =ᵐ[μ] fun a => ν t * s.indicator 1 a := by
    rw [hmap]
    exact Measure.rnDeriv_withDensity μ (measurable_const.mul (measurable_one.indicator hs))
  filter_upwards [pushDensity_ae_eq_rnDeriv hf (s ×ˢ t), hrn] with a ha hb
  rw [ha, hb]
  by_cases has : a ∈ s
  · have hval : (ν t * s.indicator (1 : Ω → ℝ≥0∞) a).toReal = ν.real t := by
      simp [Set.indicator_of_mem has, measureReal_def]
    rw [hval, Set.indicator_of_mem has, Pi.one_apply, mul_one]
  · simp [Set.indicator_of_notMem has]

end MeasureTheory

end TauCeti
