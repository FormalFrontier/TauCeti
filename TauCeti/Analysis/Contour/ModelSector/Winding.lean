/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Circle

/-!
# The valence-formula winding values

The generic circular-arc index integrals — `indexIntegral_arc_interval`, `indexIntegral_arc` and
`windingNumber_circle` — are `circleMap` results rather than model-sector ones and live in
`TauCeti.Analysis.Contour.Winding.Number.Circle`, which this module re-exports so that imports of
this path keep working.

What remains here are the two arc values the valence formula names by their points. Their
*statements* are the generic arc computation at `α = π` and `α = π/3`; the names record the role
each value plays downstream, which is why they sit here rather than in the generic circle module.

## Main results

* `TauCeti.Contour.windingNumber_at_i` — the semicircle value `½`, the coefficient of `ord_i f`.
* `TauCeti.Contour.windingNumber_at_rho` — the `π/3`-arc value `1/6`, per corner.

`TauCeti/Analysis/Contour/ModelSector/` retains the genuinely model-sector material:
`Corner.lean` (the two-ray corner) and `Closed.lean` (the assembled sector and its winding number).

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

namespace TauCeti.Contour

open Complex Metric

/-- **The winding number `½` at `i`** — the coefficient of `ord_i(f)` in the valence formula. The
semicircle (`[0, π]`) specialization of `indexIntegral_arc` (`π / 2π = ½`): `i` is a
*smooth* boundary point of the fundamental domain, so the valence contour indents around it by a
**semicircle** (opening angle `α = π`). The statement is the generic arc computation; the point `i`
names its downstream valence-formula role. -/
theorem windingNumber_at_i {z₀ : ℂ} {r : ℝ} (hr : r ≠ 0) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..Real.pi, deriv (circleMap z₀ r) θ / (circleMap z₀ r θ - z₀)
      = 1 / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [indexIntegral_arc hr]
  field_simp

/-- **The winding number `1/6` at `ρ`** — the per-corner coefficient in the valence formula. The
`[0, π/3]` specialization of `indexIntegral_arc` (`(π/3) / 2π = 1/6`): `ρ` is a `π/3` corner
of the fundamental domain, so the contour indents around it by a `π/3` arc, and the two such corners
(`ρ` and `ρ+1`) each contribute `1/6`, summing to the `1/3` coefficient of `ord_ρ(f)`. The statement
is the generic arc computation; the point `ρ` names its downstream valence-formula role. -/
theorem windingNumber_at_rho {z₀ : ℂ} {r : ℝ} (hr : r ≠ 0) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..(Real.pi / 3), deriv (circleMap z₀ r) θ / (circleMap z₀ r θ - z₀)
      = 1 / 6 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [indexIntegral_arc hr]
  push_cast
  field_simp
  ring

end TauCeti.Contour

end

end
