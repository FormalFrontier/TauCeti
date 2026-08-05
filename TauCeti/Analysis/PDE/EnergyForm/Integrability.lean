/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Measurability
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability of pointwise PDE energy densities

The weak-form lane of the PDE roadmap will define the energy bilinear form by integrating the
pointwise scalar density
`x ↦ energyIntegrand (a x) (b x) (c x) (U x) (V x)`.  The preceding finite-dimensional files
give the measurability of this density and the pointwise bound with explicit coefficient
constants.  This file packages the next handoff: bounded measurable coefficient fields and
measurable jet fields whose norm product is integrable produce integrable scalar energy
densities.  In particular, this applies to square-integrable jet fields, and specializes on
finite-measure domains to bounded jet fields.

This remains below the Sobolev-space construction.  The coefficient bounds are stated inline,
matching the roadmap's bounded-measurable-coefficient hypotheses.

## Main declarations

* `TauCeti.PDE.integrable_energyIntegrand_apply₂_of_integrable_norm_mul`: coefficient bounds and
  an integrable product of jet norms give scalar-density integrability.
* `TauCeti.PDE.integrable_energyIntegrand_apply₂_of_memLp_two`: coefficient bounds and
  square-integrable jet fields give scalar-density integrability.
* `TauCeti.PDE.integrable_energyIntegrand_apply₂_of_bounds`: the bounded finite-measure
  specialization.
* `TauCeti.PDE.integrable_energyIntegrand_apply_of_bounds`: the fixed-jet specialization.
* The corresponding `UniformlyEllipticOn.*_on` lemmas replace the raw principal coefficient
  bound by the roadmap's named uniform-ellipticity hypothesis on an a.e.-supported domain.
-/

public section

namespace TauCeti

namespace PDE

open Matrix MeasureTheory
open scoped InnerProductSpace

variable {α n : Type*} [MeasurableSpace α] [Fintype n]
variable {μ : Measure α}

/-- Local classical decidable equality for finite coordinate indices in uniform-ellipticity
wrappers. -/
noncomputable local instance energyFormIntegrabilityDecidableEq : DecidableEq n :=
  Classical.decEq n

/-- Bounded measurable coefficient fields and an integrable product of jet norms give an
integrable scalar energy density. -/
lemma integrable_energyIntegrand_apply₂_of_integrable_norm_mul
    {a : α → Matrix n n ℝ} {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    {U V : α → ℝ × EuclideanSpace ℝ n} {Lam beta gamma : ℝ} (hLam : 0 ≤ Lam)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : AEStronglyMeasurable U μ) (hV : AEStronglyMeasurable V μ)
    (ha_bound : ∀ᵐ x ∂μ, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (hUV : Integrable (fun x => ‖U x‖ * ‖V x‖) μ) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ := by
  refine (hUV.const_mul (Lam + beta + gamma)).mono'
    (aestronglyMeasurable_energyIntegrand_apply₂ ha hb hc hU hV) ?_
  filter_upwards [ha_bound, hb_bound, hc_bound] with x hA hb₀ hc₀
  simpa [mul_assoc] using norm_energyIntegrand_apply_le_of_bounds hLam hA hb₀ hc₀ (U x) (V x)

/-- Bounded measurable coefficient fields and square-integrable jet fields give an integrable
scalar energy density. -/
lemma integrable_energyIntegrand_apply₂_of_memLp_two
    {a : α → Matrix n n ℝ} {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    {U V : α → ℝ × EuclideanSpace ℝ n} {Lam beta gamma : ℝ} (hLam : 0 ≤ Lam)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (ha_bound : ∀ᵐ x ∂μ, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ :=
  integrable_energyIntegrand_apply₂_of_integrable_norm_mul hLam ha hb hc
    hU.aestronglyMeasurable hV.aestronglyMeasurable ha_bound hb_bound hc_bound
    (by
      convert
        (hU.norm.integrable_mul hV.norm :
          Integrable ((fun x => ‖U x‖) * fun x => ‖V x‖) μ) using 1
      ext x
      rw [Pi.mul_apply])

/-- Bounded measurable coefficient fields and bounded measurable jet fields give an integrable
scalar energy density on a finite-measure space. -/
lemma integrable_energyIntegrand_apply₂_of_bounds [IsFiniteMeasure μ]
    {a : α → Matrix n n ℝ} {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    {U V : α → ℝ × EuclideanSpace ℝ n} {Lam beta gamma R S : ℝ} (hLam : 0 ≤ Lam)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : AEStronglyMeasurable U μ) (hV : AEStronglyMeasurable V μ)
    (ha_bound : ∀ᵐ x ∂μ, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (hU_bound : ∀ᵐ x ∂μ, ‖U x‖ ≤ R)
    (hV_bound : ∀ᵐ x ∂μ, ‖V x‖ ≤ S) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ := by
  refine integrable_energyIntegrand_apply₂_of_integrable_norm_mul hLam ha hb hc hU hV ha_bound
    hb_bound hc_bound ?_
  refine Integrable.of_bound (hU.norm.mul hV.norm) (R * S) ?_
  filter_upwards [hU_bound, hV_bound] with x hUx hVx
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hR : 0 ≤ R := (norm_nonneg (U x)).trans hUx
  exact mul_le_mul hUx hVx (norm_nonneg (V x)) hR

/-- Fixed-jet specialization of `integrable_energyIntegrand_apply₂_of_bounds`. -/
lemma integrable_energyIntegrand_apply_of_bounds [IsFiniteMeasure μ]
    {a : α → Matrix n n ℝ} {b : α → EuclideanSpace ℝ n} {c : α → ℝ} {Lam beta gamma : ℝ}
    (hLam : 0 ≤ Lam) (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (ha_bound : ∀ᵐ x ∂μ, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (U V : ℝ × EuclideanSpace ℝ n) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) U V) μ :=
  integrable_energyIntegrand_apply₂_of_bounds (U := fun _ => U) (V := fun _ => V)
    hLam ha hb hc aestronglyMeasurable_const aestronglyMeasurable_const
    ha_bound hb_bound hc_bound (Filter.Eventually.of_forall fun _ => le_rfl)
    (Filter.Eventually.of_forall fun _ => le_rfl)

namespace UniformlyEllipticOn

variable {Ω : Set α} {a : α → Matrix n n ℝ}
variable {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
variable {U V : α → ℝ × EuclideanSpace ℝ n}
variable {lam Lam beta gamma R S : ℝ}

/-- Uniform-ellipticity wrapper for scalar energy-density integrability.

If `μ` is a.e. supported on `Ω`, the named principal coefficient hypothesis
`UniformlyEllipticOn Ω a λ Λ` supplies the a.e. bilinear upper bound required by
`integrable_energyIntegrand_apply₂_of_integrable_norm_mul`. -/
lemma integrable_energyIntegrand_apply₂_of_integrable_norm_mul_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : AEStronglyMeasurable U μ) (hV : AEStronglyMeasurable V μ)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (hUV : Integrable (fun x => ‖U x‖ * ‖V x‖) μ) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ :=
  integrable_energyIntegrand_apply₂_of_integrable_norm_mul h.upper_nonneg ha hb hc hU hV
    (hΩ.mono fun _ hx => h.upper_bound hx) hb_bound hc_bound hUV

/-- Uniform-ellipticity wrapper for the square-integrable-jet energy-density criterion. -/
lemma integrable_energyIntegrand_apply₂_of_memLp_two_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ :=
  integrable_energyIntegrand_apply₂_of_memLp_two h.upper_nonneg ha hb hc hU hV
    (hΩ.mono fun _ hx => h.upper_bound hx) hb_bound hc_bound

/-- Uniform-ellipticity wrapper for bounded measurable jets on a finite-measure space. -/
lemma integrable_energyIntegrand_apply₂_of_bounds_on [IsFiniteMeasure μ]
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : AEStronglyMeasurable U μ) (hV : AEStronglyMeasurable V μ)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (hU_bound : ∀ᵐ x ∂μ, ‖U x‖ ≤ R) (hV_bound : ∀ᵐ x ∂μ, ‖V x‖ ≤ S) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ :=
  integrable_energyIntegrand_apply₂_of_bounds h.upper_nonneg ha hb hc hU hV
    (hΩ.mono fun _ hx => h.upper_bound hx) hb_bound hc_bound hU_bound hV_bound

/-- Fixed-jet specialization of
`UniformlyEllipticOn.integrable_energyIntegrand_apply₂_of_bounds_on`. -/
lemma integrable_energyIntegrand_apply_of_bounds_on [IsFiniteMeasure μ]
    (h : UniformlyEllipticOn Ω a lam Lam) (hΩ : ∀ᵐ x ∂μ, x ∈ Ω)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ) (hc : AEStronglyMeasurable c μ)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta) (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (U V : ℝ × EuclideanSpace ℝ n) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) U V) μ :=
  integrable_energyIntegrand_apply_of_bounds h.upper_nonneg ha hb hc
    (hΩ.mono fun _ hx => h.upper_bound hx) hb_bound hc_bound U V

end UniformlyEllipticOn

end PDE

end TauCeti
