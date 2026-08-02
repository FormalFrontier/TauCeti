/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Complex.Basic

/-!
# A decay bound for `∫ (γ - w)⁻¹ · g` when `w` is far from the curve

For a curve `γ : ℝ → ℂ` with `‖γ t‖ ≤ R` on the integrating interval and a point `w` with
`R < ‖w‖`, the integral `∫ t in a..b, (γ t - w)⁻¹ * g t` of an interval-integrable weight `g` is
bounded by `(∫ ‖g‖) / (‖w‖ - R)`: the distance lower bound `‖w‖ - R ≤ ‖γ t - w‖` gives
`‖(γ t - w)⁻¹‖ ≤ (‖w‖ - R)⁻¹` pointwise, so the estimate reduces to the `L¹` norm of `g`. This is
the common decay estimate behind the vanishing at infinity of both the generalized winding number
(weight `g = deriv γ`) and Dixon's `dixonH2` (weight `g = f (γ ·) * deriv γ`); using the `L¹` norm
rather than a uniform bound on `g` keeps it applicable to raw curves whose derivative is only
interval-integrable.

## Main results

* `TauCeti.Contour.norm_integral_inv_sub_mul_le` — the `(∫ ‖g‖) / (‖w‖ - R)` decay bound.

## Provenance

Factored from the far-field estimates in the AINTLIB `LeanModularForms` development —
`contourIntegral_inv_norm_le_of_far` in `NullHomologous.lean` (the winding case, weight `deriv γ`)
and `dixonH2_norm_le` in `DixonTheorem.lean` (the Dixon case) — restated for a raw `γ : ℝ → ℂ` on an
oriented interval with an arbitrary interval-integrable weight `g`, and bounding by the `L¹` norm of
`g` rather than a Lipschitz or uniform bound.
-/

public section

open Complex MeasureTheory Set

open scoped Interval

namespace TauCeti.Contour

/-- **Decay bound for a Cauchy-type integral far from the curve.** If `‖γ t‖ ≤ R` on `Ι a b`,
`g` is interval-integrable, and `R < ‖w‖`, then
`‖∫ t in a..b, (γ t - w)⁻¹ * g t‖ ≤ (∫ t in Ι a b, ‖g t‖) / (‖w‖ - R)`. The distance lower bound
`‖w‖ - R ≤ ‖γ t - w‖` makes `‖(γ t - w)⁻¹‖ ≤ (‖w‖ - R)⁻¹` pointwise, and the weight contributes its
`L¹` norm. Only the bound on the half-open interval `Ι a b` matters; the endpoints do not affect the
integral. -/
theorem norm_integral_inv_sub_mul_le {γ g : ℝ → ℂ} {a b R : ℝ} {w : ℂ}
    (hg : IntervalIntegrable g volume a b) (hR : ∀ t ∈ Ι a b, ‖γ t‖ ≤ R) (hw : R < ‖w‖) :
    ‖∫ t in a..b, (γ t - w)⁻¹ * g t‖ ≤ (∫ t in Ι a b, ‖g t‖) / (‖w‖ - R) := by
  have hpos : 0 < ‖w‖ - R := by linarith
  have h_dist_lb : ∀ t ∈ Ι a b, ‖w‖ - R ≤ ‖γ t - w‖ := fun t ht => by
    have h := norm_sub_norm_le w (γ t)
    rw [norm_sub_rev] at h
    linarith [hR t ht]
  have h_ae : ∀ᵐ t ∂volume.restrict (Ι a b),
      ‖(γ t - w)⁻¹ * g t‖ ≤ (‖w‖ - R)⁻¹ * ‖g t‖ := by
    refine ae_restrict_of_forall_mem measurableSet_uIoc fun t ht => ?_
    rw [norm_mul, norm_inv]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hpos (h_dist_lb t ht)) (norm_nonneg _)
  calc ‖∫ t in a..b, (γ t - w)⁻¹ * g t‖
      ≤ ∫ t in Ι a b, ‖(γ t - w)⁻¹ * g t‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ t in Ι a b, (‖w‖ - R)⁻¹ * ‖g t‖ :=
        integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _)
          (hg.norm.const_mul _).def' h_ae
    _ = (‖w‖ - R)⁻¹ * ∫ t in Ι a b, ‖g t‖ := integral_const_mul _ _
    _ = (∫ t in Ι a b, ‖g t‖) / (‖w‖ - R) := inv_mul_eq_div _ _

end TauCeti.Contour
