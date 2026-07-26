/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic

/-!
# The generalized winding number (Hungerbühler–Wasem Def 2.1)

For a curve `γ : ℝ → ℂ` on `[a, b]` and a point `z₀`, the **generalized winding number**
`windingNumber γ a b z₀` is the principal-value normalization of the index integral
`(2πi)⁻¹ · PV ∮_γ dz/(z − z₀)` (Hungerbühler–Wasem Def 2.1); see
`windingNumber_eq_integral_of_avoidance` for its reduction to the ordinary index integral under the
hypotheses stated there. As an unconditional `limUnder`-based value it is junk when the principal
value does not exist.

## Main definitions

* `TauCeti.Contour.windingNumber` — the generalized winding number.
* `TauCeti.Contour.IsNullHomologous` — a curve whose winding number vanishes outside a set `Ω`.

## Main results

* `TauCeti.Contour.windingNumber_eq_cauchyPVAt` — characteristic value lemma for the raw
  `cauchyPVAt` defining value.
* `TauCeti.Contour.windingNumber_eq_of_hasCauchyPVAt` — evaluate `windingNumber` from a Cauchy
  principal-value witness, without unfolding the definition.
* `TauCeti.Contour.windingNumber_congr_curve_ae` — the winding number is unchanged when the curves
  agree almost everywhere on the integration interval and their derivatives agree almost everywhere
  where the curve misses `z₀`;
  `TauCeti.Contour.windingNumber_congr_curve` — the pointwise corollary, needing agreement only on
  the open interval `Set.uIoo a b`. This is what lets a piecewise contour be evaluated one piece
  at a time.
* `TauCeti.Contour.windingNumber_same` — the generalized winding number on `[a, a]` is `0`.
* `TauCeti.Contour.isNullHomologous_iff` — restates `IsNullHomologous` as its vanishing condition,
  so consumers use the predicate without unfolding its hidden body.
* `TauCeti.Contour.windingNumber_eq_integral_of_avoidance` — reduces `windingNumber` to the ordinary
  index integral `(2πi)⁻¹ · ∮_γ dz/(z − z₀)` under the continuity, avoidance, and integrability
  hypotheses stated there.

This is Layer 0 of the Hungerbühler–Wasem generalized residue theorem (HW Thm 3.3).

## Provenance

Adapted from the AINTLIB `LeanModularForms` project, file
`ForMathlib/GeneralizedWindingNumber.lean`, specialised to the raw-function
(`γ : ℝ → ℂ` on `[a, b]`) design of the contour-integration roadmap.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

/-- **Generalized winding number** (HW Def 2.1): `n_{z₀}(γ) = (2πi)⁻¹ · PV ∮_γ dz/(z − z₀)`, the
principal-value normalization of the index integral for a curve `γ : ℝ → ℂ` on `[a, b]` and any
point `z₀`. See `windingNumber_eq_integral_of_avoidance` for its reduction to the ordinary index
integral; as a `limUnder`-based value it is junk when the principal value does not exist. -/
def windingNumber (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * cauchyPVAt γ a b (fun z => (z - z₀)⁻¹) z₀

/-- **Characteristic value lemma.** The generalized winding number is the normalized raw
single-point principal-value value. This is the public, module-safe form of the definition for
value-level rewrites. -/
theorem windingNumber_eq_cauchyPVAt {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} :
    windingNumber γ a b z₀ =
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * cauchyPVAt γ a b (fun z => (z - z₀)⁻¹) z₀ :=
  (rfl)

/-- **Characteristic value lemma.** From a Cauchy principal-value witness for `(· − z₀)⁻¹` along
`γ`, the generalized winding number is the normalized value `(2πi)⁻¹ · L`. This evaluates
`windingNumber` through the `HasCauchyPVAt` predicate without unfolding the definition. -/
theorem windingNumber_eq_of_hasCauchyPVAt {γ : ℝ → ℂ} {a b : ℝ} {z₀ L : ℂ}
    (h : HasCauchyPVAt γ a b (fun z => (z - z₀)⁻¹) z₀ L) :
    windingNumber γ a b z₀ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * L := by
  rw [windingNumber_eq_cauchyPVAt, h.cauchyPVAt_eq]

/-- The generalized winding number over a zero-length interval is `0`. -/
@[simp]
theorem windingNumber_same (γ : ℝ → ℂ) (a : ℝ) (z₀ : ℂ) :
    windingNumber γ a a z₀ = 0 := by
  rw [windingNumber_eq_of_hasCauchyPVAt
    (HasCauchyPVAt.refl γ a (fun z : ℂ => (z - z₀)⁻¹) z₀)]
  ring

/-- **The generalized winding number is unchanged when the curves agree almost everywhere and
their derivatives agree almost everywhere off `z₀`.** Derivative agreement is only needed where
the curve misses `z₀`: the `ε`-truncation deletes the integrand at `z₀` for every positive `ε`.
Curve equality alone does not suffice — the index integrand contains `deriv γ`. -/
theorem windingNumber_congr_curve_ae {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (h_eq : γ₁ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] γ₂)
    (h_deriv : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc a b),
      γ₁ t ≠ z₀ → deriv γ₁ t = deriv γ₂ t) :
    windingNumber γ₁ a b z₀ = windingNumber γ₂ a b z₀ := by
  unfold windingNumber
  rw [cauchyPVAt_congr_curve_ae h_eq h_deriv]

/-- **The generalized winding number depends on the curve only through its values on the open
interval between `a` and `b`.** Agreement on the open interval suffices even though the index
integrand involves `deriv γ`, since an open set is a neighbourhood of each of its points. This is
what lets a piecewise contour be evaluated one piece at a time: on each piece the assembled curve
agrees with the simple curve computing that piece's contribution. -/
theorem windingNumber_congr_curve {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (h_eq : Set.EqOn γ₁ γ₂ (Set.uIoo a b)) :
    windingNumber γ₁ a b z₀ = windingNumber γ₂ a b z₀ := by
  unfold windingNumber
  rw [cauchyPVAt_congr_curve h_eq]

/-- If the two endpoints are equal, the generalized winding number is `0`. -/
theorem windingNumber_eq_zero_of_eq (γ : ℝ → ℂ) {a b : ℝ} (hab : a = b) (z₀ : ℂ) :
    windingNumber γ a b z₀ = 0 := by
  subst b
  exact windingNumber_same γ a z₀

/-- A curve `γ` on `[a, b]` is **null-homologous** in `Ω` when its generalized winding number
about every point outside `Ω` vanishes — the hypothesis of the homology form of Cauchy's theorem
and of the Hungerbühler–Wasem residue theorem (HW Thm 3.3). -/
def IsNullHomologous (γ : ℝ → ℂ) (a b : ℝ) (Ω : Set ℂ) : Prop :=
  ∀ w ∉ Ω, windingNumber γ a b w = 0

/-- Restatement of `IsNullHomologous` as its defining vanishing condition, so consumers can use the
predicate without unfolding its hidden body. -/
theorem isNullHomologous_iff {γ : ℝ → ℂ} {a b : ℝ} {Ω : Set ℂ} :
    IsNullHomologous γ a b Ω ↔ ∀ w ∉ Ω, windingNumber γ a b w = 0 :=
  Iff.rfl

/-- **Integrability of the index integrand for a point off the curve.** If `γ` is continuous on
`Set.uIcc a b` and avoids `w` there (so `(γ · - w)⁻¹` is continuous) and `deriv γ` is
interval-integrable, then `(γ t - w)⁻¹ * deriv γ t` is interval-integrable, being a continuous
factor times an integrable one. -/
theorem intervalIntegrable_inv_sub_mul_deriv {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ}
    (hγ_cont : ContinuousOn γ (Set.uIcc a b)) (hoff : ∀ t ∈ Set.uIcc a b, γ t ≠ w)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) MeasureTheory.volume a b) :
    IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) MeasureTheory.volume a b :=
  hderiv_int.continuousOn_mul ((hγ_cont.sub continuousOn_const).inv₀
    fun t ht ↦ sub_ne_zero.mpr (hoff t ht))

/-- If `γ` is continuous on `[a, b]`, avoids `z₀` there, and the index integrand is
interval-integrable, the generalized winding number is the ordinary index integral: the principal
value collapses to `(2πi)⁻¹ · ∮_γ dz/(z − z₀)`. -/
theorem windingNumber_eq_integral_of_avoidance {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (h_cont : ContinuousOn γ (Set.uIcc a b))
    (h_avoid : ∀ t ∈ Set.uIcc a b, γ t ≠ z₀)
    (hf_int : IntervalIntegrable (fun t => (γ t - z₀)⁻¹ * deriv γ t) MeasureTheory.volume a b) :
    windingNumber γ a b z₀
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t :=
  windingNumber_eq_of_hasCauchyPVAt (HasCauchyPVAt.of_avoidance h_cont h_avoid hf_int)

end TauCeti.Contour

end
