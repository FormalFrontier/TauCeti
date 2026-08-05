/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.NullHomologous

/-!
# Orientation reversal for contour winding numbers

This file records the basic orientation-reversal API for the generalized winding number.
Reversing the interval orientation negates the single-point Cauchy principal value defining
`Contour.windingNumber`, so the winding number itself changes sign.

These lemmas are bookkeeping for the roadmap's curve and cycle layer. Cycles are oriented formal
combinations of curves, and finite decompositions of curves into avoiding pieces and model sectors
need both concatenation and orientation reversal.

## Main results

* `Contour.windingNumber_symm` — the generalized winding number changes sign when the interval is
  reversed.
* `Contour.IsNullHomologous.symm`, `Contour.IsNullHomologous.symm_of_avoidance` — null-homology is
  preserved by reversing orientation, under the same honest principal-value existence hypotheses
  used elsewhere in the winding-number API.

## Provenance

This is routine API around the Hungerbühler--Wasem generalized winding number from the contour
integration roadmap; no formal source is vendored.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {Ω : Set ℂ}

/-- The kernel integrand used to define the generalized winding number about `z₀`. This local
abbreviation keeps the orientation-reversal statements readable. -/
local notation "κ[" z "]" => (fun w : ℂ => (w - z)⁻¹)

/-- The generalized winding number changes sign when the interval orientation is reversed,
provided the principal value defining the original winding number exists. -/
theorem windingNumber_symm (h : CauchyPVExistsAt γ a b κ[z₀] z₀) :
    windingNumber γ b a z₀ = -windingNumber γ a b z₀ := by
  rw [windingNumber_eq_of_hasCauchyPVAt h.hasCauchyPVAt_cauchyPVAt.symm,
    windingNumber_eq_of_hasCauchyPVAt h.hasCauchyPVAt_cauchyPVAt]
  ring

/-- Pointwise vanishing of a winding number is preserved by reversing the interval orientation,
under the principal-value existence hypothesis that makes the two winding-number values honest. -/
theorem windingNumber_eq_zero_symm (hzero : windingNumber γ a b z₀ = 0)
    (hpv : CauchyPVExistsAt γ a b κ[z₀] z₀) :
    windingNumber γ b a z₀ = 0 := by
  rw [windingNumber_symm hpv, hzero, neg_zero]

/-- Null-homology is preserved by reversing orientation, provided the pointwise principal values
defining the exterior winding numbers exist. -/
theorem IsNullHomologous.symm (h : IsNullHomologous γ a b Ω)
    (hpv : ∀ z ∉ Ω, CauchyPVExistsAt γ a b κ[z] z) :
    IsNullHomologous γ b a Ω := by
  rw [isNullHomologous_iff] at h ⊢
  intro z hz
  exact windingNumber_eq_zero_symm (h z hz) (hpv z hz)

/-- Null-homology is preserved by reversing orientation in the ordinary avoided-pole case. If the
curve lies in `Ω`, every exterior point is avoided, so the required principal values are ordinary
integrals. -/
theorem IsNullHomologous.symm_of_avoidance (h : IsNullHomologous γ a b Ω)
    (hγ : ∀ t ∈ Set.uIcc a b, γ t ∈ Ω) (hcont : ContinuousOn γ (Set.uIcc a b)) (hint : ∀ z ∉ Ω,
      IntervalIntegrable (fun t => (γ t - z)⁻¹ * deriv γ t) MeasureTheory.volume a b) :
    IsNullHomologous γ b a Ω := by
  refine h.symm ?_
  intro z hz
  refine cauchyPVExistsAt_of_avoidance hcont ?_ (hint z hz)
  intro t ht htz
  exact hz (htz ▸ hγ t ht)

end TauCeti.Contour

end
