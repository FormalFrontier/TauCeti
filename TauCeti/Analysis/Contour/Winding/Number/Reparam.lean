/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Curve.Reparam
public import TauCeti.Analysis.Contour.NullHomologous

/-!
# Reparametrization invariance of the generalized winding number

Precomposing a curve `γ` with a `C¹` change of parameter `φ` leaves the generalized winding number
of Hungerbühler–Wasem (Def 2.1) about a point off the curve unchanged, the parameter interval
`[[a, b]]` being replaced by `[[φ a, φ b]]`; null-homology in an ambient set transports the same
way. These are consequences of the reparametrization invariance of the contour integral proved in
`TauCeti/Analysis/Contour/Curve/Reparam.lean`. As there, "`C¹`" is shorthand for ambient pointwise
`HasDerivAt`/`DifferentiableAt` data, and the curve is asked to be `C¹` with no breakpoints — the
piecewise-`C¹` case is a separate increment.

As there, the regularity hypotheses on `γ` are placed on the swept image `φ '' [[a, b]]` rather than
on `[[φ a, φ b]]`: `φ` is not assumed monotone, and `intermediate_value_uIcc` gives
`[[φ a, φ b]] ⊆ φ '' [[a, b]]`, so hypotheses on the image also cover the reparametrized interval.

Only the off-curve case is treated: when `z₀` lies on the curve the winding number is a Cauchy
principal value, whose symmetric excision windows are themselves reparametrized, and transporting
them is a separate argument. This is the case that the roadmap's cycle bookkeeping consumes.

## Main results

* `TauCeti.Contour.windingNumber_comp_reparam` — the generalized winding number about a point off
  the curve is unchanged by a `C¹` reparametrization.
* `TauCeti.Contour.windingNumber_comp_mul_add` — the affine special case `φ t = r * t + s`.
* `TauCeti.Contour.IsNullHomologous.comp_reparam` — null-homology transports along a `C¹`
  reparametrization of a curve lying in the ambient set.

This is Layer 0 of the Hungerbühler–Wasem generalized residue theorem (HW Thm 3.3): the
reparametrization-invariance API that the cycle layer needs in order to treat a closed curve
independently of its parametrization.

## Provenance

This is routine API around the Hungerbühler--Wasem generalized winding number from the contour
integration roadmap; no formal source is vendored.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — Def 2.1.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {φ φ' : ℝ → ℝ} {a b : ℝ} {z₀ : ℂ} {Ω : Set ℂ}

/-- **Reparametrization invariance of the generalized winding number** (HW Def 2.1), for a point
`z₀` off the curve. Precomposing with a change of parameter `φ` that has an ambient derivative
`φ' t` at each `t ∈ [[a, b]]`, with `φ'` continuous, leaves the winding number unchanged, the
parameter interval `[[a, b]]` being replaced by `[[φ a, φ b]]`.

The hypotheses on `γ` are stated on the swept image `φ '' [[a, b]]`, which contains `[[φ a, φ b]]`
by the intermediate value theorem, so `φ` need not be monotone. Off-curve is essential: on the
curve the winding number is a principal value, whose excision windows are themselves
reparametrized. -/
theorem windingNumber_comp_reparam (hφ : ∀ t ∈ Set.uIcc a b, HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' (Set.uIcc a b)) (hγ : ∀ u ∈ φ '' Set.uIcc a b, DifferentiableAt ℝ γ u)
    (hγ' : ContinuousOn (deriv γ) (φ '' Set.uIcc a b))
    (havoid : ∀ u ∈ φ '' Set.uIcc a b, γ u ≠ z₀) :
    windingNumber (γ ∘ φ) a b z₀ = windingNumber γ (φ a) (φ b) z₀ := by
  have hφcont : ContinuousOn φ (Set.uIcc a b) :=
    fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  have hγcont : ContinuousOn γ (φ '' Set.uIcc a b) :=
    fun u hu => (hγ u hu).continuousAt.continuousWithinAt
  have hsub : Set.uIcc (φ a) (φ b) ⊆ φ '' Set.uIcc a b := intermediate_value_uIcc hφcont
  have hmaps : Set.MapsTo φ (Set.uIcc a b) (φ '' Set.uIcc a b) := Set.mapsTo_image φ _
  -- the kernel `(· - z₀)⁻¹` is continuous along the curve, since `γ` avoids `z₀`
  have hker : ContinuousOn (fun z : ℂ => (z - z₀)⁻¹) (γ '' (φ '' Set.uIcc a b)) := by
    refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    rintro _ ⟨u, hu, rfl⟩
    exact sub_ne_zero.mpr (havoid u hu)
  -- the index integrand along the reparametrized curve is continuous, hence integrable
  have hderivcont : ContinuousOn (deriv (γ ∘ φ)) (Set.uIcc a b) :=
    continuousOn_deriv_comp_reparam hφ hφ' hγ hγ'
  have hcompcont : ContinuousOn (γ ∘ φ) (Set.uIcc a b) := hγcont.comp hφcont hmaps
  have hcompavoid : ∀ t ∈ Set.uIcc a b, (γ ∘ φ) t ≠ z₀ := fun t ht => havoid (φ t) ⟨t, ht, rfl⟩
  rw [windingNumber_eq_integral_of_avoidance hcompcont hcompavoid
      (intervalIntegrable_inv_sub_mul_deriv hcompcont hcompavoid hderivcont.intervalIntegrable),
    windingNumber_eq_integral_of_avoidance (hγcont.mono hsub)
      (fun u hu => havoid u (hsub hu))
      (intervalIntegrable_inv_sub_mul_deriv (hγcont.mono hsub) (fun u hu => havoid u (hsub hu))
        (hγ'.mono hsub).intervalIntegrable)]
  congr 1
  -- both index integrands are the contour integrand of the kernel `(· - z₀)⁻¹`, with the two
  -- factors in the opposite order
  have hL : ∫ t in a..b, ((γ ∘ φ) t - z₀)⁻¹ * deriv (γ ∘ φ) t
      = ∫ t in a..b, deriv (γ ∘ φ) t • ((γ ∘ φ) t - z₀)⁻¹ :=
    intervalIntegral.integral_congr fun t _ => by rw [smul_eq_mul, mul_comm]
  have hR : ∫ u in φ a..φ b, (γ u - z₀)⁻¹ * deriv γ u
      = ∫ u in φ a..φ b, deriv γ u • (γ u - z₀)⁻¹ :=
    intervalIntegral.integral_congr fun u _ => by rw [smul_eq_mul, mul_comm]
  rw [hL, hR]
  exact integral_deriv_smul_comp_reparam (f := fun z : ℂ => (z - z₀)⁻¹) hφ hφ' hγ hγ' hker

/-- The affine special case of `windingNumber_comp_reparam`: precomposing a curve with
`t ↦ r * t + s` moves the parameter interval to `[[r * a + s, r * b + s]]` and leaves the winding
number about an off-curve point unchanged. Unlike the general statement this needs no separate
continuity hypothesis on the parameter speed, the derivative being the constant `r`. -/
theorem windingNumber_comp_mul_add {r s : ℝ}
    (hγ : ∀ u ∈ Set.uIcc (r * a + s) (r * b + s), DifferentiableAt ℝ γ u)
    (hγ' : ContinuousOn (deriv γ) (Set.uIcc (r * a + s) (r * b + s)))
    (havoid : ∀ u ∈ Set.uIcc (r * a + s) (r * b + s), γ u ≠ z₀) :
    windingNumber (γ ∘ fun t => r * t + s) a b z₀
      = windingNumber γ (r * a + s) (r * b + s) z₀ := by
  have himg : (fun t => r * t + s) '' Set.uIcc a b = Set.uIcc (r * a + s) (r * b + s) := by
    rw [show (fun t : ℝ => r * t + s) = (fun x => x + s) ∘ (r * ·) from funext fun _ => rfl,
      Set.image_comp, Set.image_const_mul_uIcc, Set.image_add_const_uIcc]
  refine windingNumber_comp_reparam (φ' := fun _ => r)
    (fun t _ => by simpa using ((hasDerivAt_id t).const_mul r).add_const s)
    continuousOn_const ?_ ?_ ?_ <;> rw [himg]
  exacts [hγ, hγ', havoid]

/-- **Null-homology transports along a reparametrization.** If a curve lies in `Ω` and is
null-homologous there, then so is its precomposition with any change of parameter `φ` that has an
ambient derivative `φ' t` at each `t ∈ [[a, b]]`, with `φ'` continuous. -/
theorem IsNullHomologous.comp_reparam (h : IsNullHomologous γ (φ a) (φ b) Ω)
    (hφ : ∀ t ∈ Set.uIcc a b, HasDerivAt φ (φ' t) t) (hφ' : ContinuousOn φ' (Set.uIcc a b))
    (hγ : ∀ u ∈ φ '' Set.uIcc a b, DifferentiableAt ℝ γ u)
    (hγ' : ContinuousOn (deriv γ) (φ '' Set.uIcc a b)) (hγΩ : ∀ u ∈ φ '' Set.uIcc a b, γ u ∈ Ω) :
    IsNullHomologous (γ ∘ φ) a b Ω := by
  rw [isNullHomologous_iff] at h ⊢
  intro z hz
  have havoid : ∀ u ∈ φ '' Set.uIcc a b, γ u ≠ z := by
    intro u hu huz
    exact hz (huz ▸ hγΩ u hu)
  rw [windingNumber_comp_reparam (φ' := φ') hφ hφ' hγ hγ' havoid]
  exact h z hz

end TauCeti.Contour

end
