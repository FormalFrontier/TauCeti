/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Complex.Basic

/-!
# The fundamental theorem of calculus along a contour

This file records the elementary arc-FTC step used by the contour-integration roadmap: if
`F' = f` along the image of a raw curve `γ : ℝ → ℂ`, then the contour integral of `f` along `γ`
is the endpoint difference `F (γ b) - F (γ a)`, and hence vanishes for a closed curve. The
statements keep the roadmap's raw-function convention and use the ordinary interval integral
`∫ t in a..b, f (γ t) * γ' t`.

This is the Layer 2 "FTC along an arc" prerequisite for Cauchy's theorem and the later residue
theorems. It is just the chain rule plus Mathlib's interval-integral fundamental theorem of
calculus.

## Main results

* `Contour.integral_comp_mul_eq_sub_of_hasDerivAt` — an explicit-velocity form using a supplied
  derivative `γ'`.
* `Contour.integral_comp_mul_deriv_eq_sub_of_hasDerivAt` — the same statement with `deriv γ`.
* `Contour.integral_comp_mul_eq_zero_of_hasDerivAt_of_closed` and
  `Contour.integral_comp_mul_deriv_eq_zero_of_hasDerivAt_of_closed` — closed-curve corollaries.

## Provenance

This is routine API around Mathlib's
`intervalIntegral.integral_eq_sub_of_hasDerivAt`, following the contour-integral convention in
the Hungerbühler--Wasem contour-integration roadmap. The Layer 2 Arc FTC roadmap item is migrated
and cleaned from the AINTLIB `LeanModularForms` sources
`ForMathlib/GeneralizedResidueTheory/CauchyPrimitive.lean`,
`ForMathlib/GeneralizedResidueTheory/ArcCalculus.lean`, and `ForMathlib/ArcFTC*.lean`; no formal
source is vendored here.
-/

public section

noncomputable section

namespace TauCeti.Contour

open MeasureTheory

variable {γ γ' : ℝ → ℂ} {g G : ℂ → ℂ} {a b : ℝ}

/-- **FTC along a contour, explicit-velocity form.** If `γ' t` is the derivative of the curve
`γ` and `G' = g` at the points `γ t`, then the contour integral of `g` along `γ` is the endpoint
difference `G (γ b) - G (γ a)`. The integrability hypothesis is stated directly on the contour
integrand, so this lemma can be used with any regularity package that supplies it. -/
theorem integral_comp_mul_eq_sub_of_hasDerivAt (hcont : ContinuousOn (G ∘ γ) (Set.uIcc a b))
    (hγ : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt γ (γ' t) t)
    (hG : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => g (γ t) * γ' t) volume a b) :
    ∫ t in a..b, g (γ t) * γ' t = G (γ b) - G (γ a) := by
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont ?_ hint
  intro t ht
  simpa only [Function.comp_apply, smul_eq_mul, mul_comm] using
    ((hG t ht).scomp t (hγ t ht)).hasDerivWithinAt

/-- **FTC along a contour, `deriv` form.** If `G' = g` along the image of a differentiable curve,
then the contour integral written with `deriv γ` is the endpoint difference
`G (γ b) - G (γ a)`. -/
theorem integral_comp_mul_deriv_eq_sub_of_hasDerivAt (hcont : ContinuousOn (G ∘ γ) (Set.uIcc a b))
    (hγ : ∀ t ∈ Set.Ioo (min a b) (max a b), DifferentiableAt ℝ γ t)
    (hG : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => g (γ t) * deriv γ t) volume a b) :
    ∫ t in a..b, g (γ t) * deriv γ t = G (γ b) - G (γ a) :=
  integral_comp_mul_eq_sub_of_hasDerivAt
    (γ' := fun t => deriv γ t) hcont (fun t ht => (hγ t ht).hasDerivAt) hG hint

/-- A contour integral of an exact derivative vanishes on a closed curve, explicit-velocity form. -/
theorem integral_comp_mul_eq_zero_of_hasDerivAt_of_closed
    (hcont : ContinuousOn (G ∘ γ) (Set.uIcc a b))
    (hγ : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt γ (γ' t) t)
    (hG : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => g (γ t) * γ' t) volume a b) (hclosed : γ a = γ b) :
    ∫ t in a..b, g (γ t) * γ' t = 0 := by
  rw [integral_comp_mul_eq_sub_of_hasDerivAt hcont hγ hG hint, hclosed, sub_self]

/-- A contour integral of an exact derivative vanishes on a closed curve, `deriv` form. -/
theorem integral_comp_mul_deriv_eq_zero_of_hasDerivAt_of_closed
    (hcont : ContinuousOn (G ∘ γ) (Set.uIcc a b))
    (hγ : ∀ t ∈ Set.Ioo (min a b) (max a b), DifferentiableAt ℝ γ t)
    (hG : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => g (γ t) * deriv γ t) volume a b) (hclosed : γ a = γ b) :
    ∫ t in a..b, g (γ t) * deriv γ t = 0 := by
  rw [integral_comp_mul_deriv_eq_sub_of_hasDerivAt hcont hγ hG hint, hclosed, sub_self]

end TauCeti.Contour

end
