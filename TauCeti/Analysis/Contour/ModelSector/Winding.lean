/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Model-sector generalized winding numbers (Hungerbühler–Wasem §2)

This file computes the **generalized winding number of a circular arc**: for the arc
`γ θ = z₀ + r·e^{iθ}` about its centre `z₀`, traversed over an angular interval `[a, b]`, the
value of `(2πi)⁻¹ ∮_γ dz/(z − z₀)` is the signed angular extent `(b − a) / 2π`
(Hungerbühler–Wasem, arXiv:1808.00997, (2.4)). Because `z₀` is the *centre* — off the arc — the
contour integral is an ordinary interval integral, and the computation is elementary: the
integrand `γ̇ / (γ − z₀)` is constantly `i` on the arc.

These arc values are the per-indentation contributions that the valence formula sums. They are
stated here on the raw index integral `(2πi)⁻¹ ∫ γ̇/(γ − z₀)`, which
`TauCeti.Contour.windingNumber` packages as a principal value; keeping them on the raw integral
avoids threading a principal-value existence hypothesis through an elementary computation.

The `[0, π]` and `[0, π/3]` specializations record the elliptic-point coefficients of the valence
formula: at a *smooth* boundary point of the fundamental domain (such as `i`) the valence contour
indents by a **semicircle** (`[0, π]`, winding `½`); at a `π/3` corner (such as `ρ`) it indents by
a **`π/3` arc** (winding `1/6`). The full circle (`[0, 2π]`, winding `1`) is the closed-curve
normalization; its value also follows from Mathlib's `circleIntegral.integral_sub_center_inv`.

## Main results

* `windingNumber_modelSector_interval` — the arc over an arbitrary `[a, b]` has winding number
  `(b − a) / 2π`; the general statement the others specialize.
* `windingNumber_modelSector` — the arc over `[0, α]` has winding number `α / 2π`.
* `windingNumber_at_i` — the semicircle (`[0, π]`) specialization: winding `½` (the coefficient of
  `ord_i(f)` in the valence formula).
* `windingNumber_at_rho` — the `[0, π/3]` specialization: winding `1/6` (the per-corner `ord_ρ(f)`
  coefficient).
* `windingNumber_circle` — the full circle (`[0, 2π]`) normalization: winding `1`.

The `windingNumber_modelSector`, `windingNumber_at_i`, `windingNumber_at_rho`, and
`windingNumber_circle` corollaries are the named Layer 1 targets of
`ContourIntegration/Suggested.lean`, derived from the general arbitrary-interval statement.

## Provenance

Migrated and adapted from the AINTLIB `LeanModularForms` project (the sector-geometry material of
`ForMathlib/HungerbuhlerWasem/Crossing.lean`), specialised to the raw-function
(`γ : ℝ → ℂ` on `[a, b]`) design of the contour-integration roadmap.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997, (2.4).
-/

public section

noncomputable section

open Complex intervalIntegral

namespace TauCeti.Contour

/-- **The circular-arc index integral** (Hungerbühler–Wasem (2.4)), on an arbitrary angular
interval. For the circular arc `γ θ = z₀ + r·e^{iθ}` about its centre `z₀`, traversed over `[a, b]`,
the normalized index integral is the signed angular extent over `2π`:
`(2πi)⁻¹ ∫_a^b (γ̇ / (γ − z₀)) dθ = (b − a) / 2π`. The centre is off the arc, so the integrand
`γ̇ / (γ − z₀)` is constantly `i` and the value is elementary. This is the general
arbitrary-interval statement; the roadmap-facing `windingNumber_modelSector` (`a = 0`),
`windingNumber_at_i`, `windingNumber_at_rho`, and `windingNumber_circle` are derived from it. -/
theorem windingNumber_modelSector_interval {z₀ : ℂ} {r : ℝ} (hr : r ≠ 0) (a b : ℝ) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ in a..b, deriv (circleMap z₀ r) θ / (circleMap z₀ r θ - z₀)
      = ((b - a : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) := by
  have hint : ∀ θ : ℝ, deriv (circleMap z₀ r) θ / (circleMap z₀ r θ - z₀) = Complex.I := by
    intro θ
    have hne : circleMap (0 : ℂ) r θ ≠ 0 := circleMap_ne_center hr
    rw [deriv_circleMap, circleMap_sub_center, mul_comm (circleMap 0 r θ) Complex.I,
      mul_div_assoc, div_self hne, mul_one]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp_rw [hint]
  rw [intervalIntegral.integral_const, Complex.real_smul]
  field_simp

/-- **The model-sector winding number** (Hungerbühler–Wasem (2.4)). The circular arc
`γ θ = z₀ + r·e^{iθ}` about its centre `z₀`, traversed over `[0, α]`, has normalized index integral
`(2πi)⁻¹ ∫_0^α (γ̇ / (γ − z₀)) dθ = α / 2π`: a counterclockwise arc of opening angle `α` contributes
generalized winding number `α/2π`. The `α = π`, `α = π/3`, and `α = 2π` specializations are
`windingNumber_at_i`, `windingNumber_at_rho`, and `windingNumber_circle`. -/
theorem windingNumber_modelSector {z₀ : ℂ} {r : ℝ} (hr : r ≠ 0) (α : ℝ) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..α, deriv (circleMap z₀ r) θ / (circleMap z₀ r θ - z₀)
      = (α : ℂ) / (2 * (Real.pi : ℂ)) := by
  rw [windingNumber_modelSector_interval hr]
  push_cast
  ring

/-- **The winding number `½` at `i`** — the coefficient of `ord_i(f)` in the valence formula. The
semicircle (`[0, π]`) specialization of `windingNumber_modelSector` (`π / 2π = ½`): `i` is a
*smooth* boundary point of the fundamental domain, so the valence contour indents around it by a
**semicircle** (opening angle `α = π`). The statement is the generic arc computation; the point `i`
names its downstream valence-formula role. -/
theorem windingNumber_at_i {z₀ : ℂ} {r : ℝ} (hr : r ≠ 0) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..Real.pi, deriv (circleMap z₀ r) θ / (circleMap z₀ r θ - z₀)
      = 1 / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [windingNumber_modelSector hr]
  field_simp

/-- **The winding number `1/6` at `ρ`** — the per-corner coefficient in the valence formula. The
`[0, π/3]` specialization of `windingNumber_modelSector` (`(π/3) / 2π = 1/6`): `ρ` is a `π/3` corner
of the fundamental domain, so the contour indents around it by a `π/3` arc, and the two such corners
(`ρ` and `ρ+1`) each contribute `1/6`, summing to the `1/3` coefficient of `ord_ρ(f)`. The statement
is the generic arc computation; the point `ρ` names its downstream valence-formula role. -/
theorem windingNumber_at_rho {z₀ : ℂ} {r : ℝ} (hr : r ≠ 0) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..(Real.pi / 3), deriv (circleMap z₀ r) θ / (circleMap z₀ r θ - z₀)
      = 1 / 6 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [windingNumber_modelSector hr]
  push_cast
  field_simp
  ring

/-- **A full circle (`[0, 2π]`) has winding number `1`** — the closed-curve normalization, the
`[0, 2π]` specialization of `windingNumber_modelSector` (`2π / 2π = 1`). Its value also follows from
Mathlib's `circleIntegral.integral_sub_center_inv`; this is the raw-index-integral form of that
normalization used as a Layer-1 target. -/
theorem windingNumber_circle {c : ℂ} {r : ℝ} (hr : r ≠ 0) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), deriv (circleMap c r) θ / (circleMap c r θ - c)
      = 1 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [windingNumber_modelSector hr]
  push_cast
  field_simp

end TauCeti.Contour

end
