/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.NullHomologous

/-!
# Concatenation API for the generalized winding number

This file records the additivity of `Contour.windingNumber` over adjacent parameter intervals.
The contour-integration roadmap uses finite decompositions of a curve into an avoiding part and
model sectors in Hungerbühler--Wasem Proposition 2.2; those decompositions need to add the
corresponding generalized winding numbers after the principal values on the pieces have been
constructed.

The results here are deliberately conditional on the relevant pointwise principal-value
existence statements. The generalized winding number is a `limUnder`-based value, so without those
witnesses it is a junk value; the characteristic lemmas below keep the additivity statement tied to
honest principal values.

## Main results

* `Contour.windingNumber_eq_add_of_hasCauchyPVAt` — additivity from explicit principal-value
  witnesses on two adjacent intervals.
* `Contour.windingNumber_concat` — additivity from principal-value existence on the two adjacent
  intervals, using the canonical `cauchyPVAt` values.
* `Contour.IsNullHomologous.concat` — if a curve is null-homologous on both adjacent intervals and
  the exterior pointwise principal values exist on those intervals, then it is null-homologous on
  their concatenation.
* `Contour.IsNullHomologous.concat_of_avoidance` — the same conclusion in the common case where
  both curve pieces lie in the domain, so exterior points are avoided and the principal values are
  ordinary integrals.

## Provenance

This is routine API around the Hungerbühler--Wasem generalized winding number from the contour
integration roadmap; no formal source is vendored.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Topology

variable {γ : ℝ → ℂ} {a b c : ℝ} {z₀ : ℂ} {Ω : Set ℂ}

/-- The kernel integrand used to define the generalized winding number about `z₀`. This local
abbreviation keeps the concatenation statements readable. -/
local notation "κ[" z "]" => (fun w : ℂ => (w - z)⁻¹)

/-- **Additivity of the generalized winding number from explicit principal-value witnesses.**
If the index-integrand principal values about `z₀` on `[a, b]` and `[b, c]` are `L₁` and `L₂`,
then the winding number over `[a, c]` is the sum of the two winding numbers. -/
theorem windingNumber_eq_add_of_hasCauchyPVAt {L₁ L₂ : ℂ} (h_ab : HasCauchyPVAt γ a b κ[z₀] z₀ L₁)
    (h_bc : HasCauchyPVAt γ b c κ[z₀] z₀ L₂) :
    windingNumber γ a c z₀ = windingNumber γ a b z₀ + windingNumber γ b c z₀ := by
  rw [windingNumber_eq_of_hasCauchyPVAt (h_ab.concat h_bc),
    windingNumber_eq_of_hasCauchyPVAt h_ab, windingNumber_eq_of_hasCauchyPVAt h_bc]
  ring

/-- **Additivity of the generalized winding number over adjacent intervals.** It is enough to know
that the principal values defining the two summand winding numbers exist; the principal value on
the concatenated interval is then supplied by `HasCauchyPVAt.concat`. -/
theorem windingNumber_concat (h_ab : CauchyPVExistsAt γ a b κ[z₀] z₀)
    (h_bc : CauchyPVExistsAt γ b c κ[z₀] z₀) :
    windingNumber γ a c z₀ = windingNumber γ a b z₀ + windingNumber γ b c z₀ := by
  exact windingNumber_eq_add_of_hasCauchyPVAt
    h_ab.hasCauchyPVAt_cauchyPVAt h_bc.hasCauchyPVAt_cauchyPVAt

/-- If the winding numbers about `z₀` vanish on two adjacent intervals, and the two corresponding
principal values exist, then the winding number about `z₀` also vanishes on the concatenated
interval. -/
theorem windingNumber_eq_zero_concat (h_ab : windingNumber γ a b z₀ = 0)
    (h_bc : windingNumber γ b c z₀ = 0) (hpv_ab : CauchyPVExistsAt γ a b κ[z₀] z₀)
    (hpv_bc : CauchyPVExistsAt γ b c κ[z₀] z₀) :
    windingNumber γ a c z₀ = 0 := by
  rw [windingNumber_concat hpv_ab hpv_bc, h_ab, h_bc, add_zero]

/-- Null-homology is preserved by concatenating adjacent parameter intervals, provided the
pointwise principal values defining the exterior winding numbers exist on the two pieces. This is
the form used by finite decomposition arguments: after proving the exterior winding numbers vanish
piecewise, they vanish on the concatenation. -/
theorem IsNullHomologous.concat (h_ab : IsNullHomologous γ a b Ω) (h_bc : IsNullHomologous γ b c Ω)
    (hpv_ab : ∀ z ∉ Ω, CauchyPVExistsAt γ a b κ[z] z)
    (hpv_bc : ∀ z ∉ Ω, CauchyPVExistsAt γ b c κ[z] z) :
    IsNullHomologous γ a c Ω := by
  rw [isNullHomologous_iff] at h_ab h_bc ⊢
  intro z hz
  exact windingNumber_eq_zero_concat (h_ab z hz) (h_bc z hz) (hpv_ab z hz) (hpv_bc z hz)

/-- Null-homology is preserved by concatenating adjacent intervals in the ordinary avoided-pole
case. If both pieces of the curve lie in `Ω`, then every exterior point is avoided; under
continuity and interval-integrability of the exterior index integrands, the needed principal values
are supplied by `cauchyPVExistsAt_of_avoidance`. -/
theorem IsNullHomologous.concat_of_avoidance (h_ab : IsNullHomologous γ a b Ω)
    (h_bc : IsNullHomologous γ b c Ω) (hγ_ab : ∀ t ∈ Set.uIcc a b, γ t ∈ Ω)
    (hγ_bc : ∀ t ∈ Set.uIcc b c, γ t ∈ Ω) (hcont_ab : ContinuousOn γ (Set.uIcc a b))
    (hcont_bc : ContinuousOn γ (Set.uIcc b c)) (hint_ab : ∀ z ∉ Ω,
      IntervalIntegrable (fun t => (γ t - z)⁻¹ * deriv γ t) MeasureTheory.volume a b)
    (hint_bc : ∀ z ∉ Ω,
      IntervalIntegrable (fun t => (γ t - z)⁻¹ * deriv γ t) MeasureTheory.volume b c) :
    IsNullHomologous γ a c Ω := by
  refine h_ab.concat h_bc ?_ ?_
  · intro z hz
    refine cauchyPVExistsAt_of_avoidance hcont_ab ?_ (hint_ab z hz)
    intro t ht htz
    exact hz (htz ▸ hγ_ab t ht)
  · intro z hz
    refine cauchyPVExistsAt_of_avoidance hcont_bc ?_ (hint_bc z hz)
    intro t ht htz
    exact hz (htz ▸ hγ_bc t ht)

end TauCeti.Contour

end
