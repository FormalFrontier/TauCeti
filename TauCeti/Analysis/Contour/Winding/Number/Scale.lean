/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.NullHomologous

/-!
# Scaling invariance for contour winding numbers

This file records the basic nonzero-scaling API for the generalized winding number. Multiplying
both the curve and the distinguished point by the same nonzero complex number leaves the index
principal value unchanged, so the winding number and null-homology are invariant. Scaling only
reindexes the excision radius by the order-isomorphism `ε ↦ ε / ‖c‖`, so no principal-value
existence hypothesis is needed.

These lemmas are bookkeeping for the roadmap's curve and cycle layer. The geometry of the
generalized winding number is local at a crossing or sector; after translating the crossing point
to the origin, finite-decomposition arguments also rescale the local model before applying the
sector computation.

## Main results

* `Contour.hasCauchyPVAt_inv_sub_const_mul` /
  `Contour.cauchyPVExistsAt_inv_sub_const_mul` — the index principal value transports under
  nonzero scaling of the curve and base point; these are exposed so downstream normalization steps
  can obtain the scaled `HasCauchyPVAt` / `CauchyPVExistsAt` fact and chain further
  principal-value APIs.
* `Contour.windingNumber_const_mul` — multiplying the curve and base point by the same nonzero
  complex number preserves the generalized winding number.
* `Contour.IsNullHomologous.const_mul` — null-homology is preserved by nonzero complex scaling of
  both the curve and the ambient set.

## Provenance

This is routine API around the Hungerbühler--Wasem generalized winding number from the contour
integration roadmap; no formal source is vendored.
-/

public section

noncomputable section

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {a b : ℝ} {z₀ c : ℂ} {Ω : Set ℂ}

/-- The kernel integrand used to define the generalized winding number about `z₀`. This local
abbreviation keeps the scaling statements readable. -/
local notation "κ[" z "]" => (fun w : ℂ => (w - z)⁻¹)

private lemma inv_sub_const_mul_eq (hc : c ≠ 0) (w : ℂ) :
    c⁻¹ * (c⁻¹ * (c * w) - z₀)⁻¹ = (c * w - c * z₀)⁻¹ := by
  simp only [inv_mul_cancel_left₀ hc]
  rw [← mul_sub, mul_inv]

/-- **Index principal value under nonzero scaling.** Multiplying the curve and the base point by a
nonzero complex number `c` transports the single-point Cauchy principal value of the winding kernel
`κ[z₀]` about `z₀` to that of `κ[c * z₀]` about `c * z₀`, with the same value. This specializes the
general `HasCauchyPVAt.const_mul_curve` to the winding kernel, where the rescaled integrand
`z ↦ c⁻¹ * κ[z₀] (c⁻¹ * z)` agrees with `κ[c * z₀]` along the scaled curve. Exposed so downstream
normalization steps can chain further principal-value APIs from the scaled fact. -/
theorem hasCauchyPVAt_inv_sub_const_mul (h : HasCauchyPVAt γ a b κ[z₀] z₀ L) (hc : c ≠ 0) :
    HasCauchyPVAt (fun t => c * γ t) a b κ[c * z₀] (c * z₀) L := by
  refine (h.const_mul_curve hc).congr_along_curve fun t _ => ?_
  exact inv_sub_const_mul_eq (z₀ := z₀) hc (γ t)

/-- Existence form of `hasCauchyPVAt_inv_sub_const_mul`: nonzero scaling of the curve and base
point preserves existence of the index principal value, exposed for the same downstream chaining. -/
theorem cauchyPVExistsAt_inv_sub_const_mul (h : CauchyPVExistsAt γ a b κ[z₀] z₀) (hc : c ≠ 0) :
    CauchyPVExistsAt (fun t => c * γ t) a b κ[c * z₀] (c * z₀) :=
  let ⟨_, hL⟩ := cauchyPVExistsAt_iff.mp h
  CauchyPVExistsAt.intro (hasCauchyPVAt_inv_sub_const_mul hL hc)

/-- The generalized winding number is invariant under simultaneous multiplication of the curve
and the base point by a nonzero complex number. -/
theorem windingNumber_const_mul (hc : c ≠ 0) :
    windingNumber (fun t => c * γ t) a b (c * z₀) = windingNumber γ a b z₀ := by
  rw [windingNumber_eq_cauchyPVAt, windingNumber_eq_cauchyPVAt]
  congr 1
  rw [cauchyPVAt_congr_along_curve (γ := fun t => c * γ t)
    (f := κ[c * z₀]) (g := fun z => c⁻¹ * κ[z₀] (c⁻¹ * z)) (z₀ := c * z₀)]
  · exact cauchyPVAt_const_mul_curve (γ := γ) (a := a) (b := b) (f := κ[z₀]) (z₀ := z₀) hc
  · intro t _
    exact (inv_sub_const_mul_eq (z₀ := z₀) hc (γ t)).symm

/-- Pointwise vanishing of a winding number is preserved by simultaneous multiplication of the
curve and base point by a nonzero complex number. -/
private theorem windingNumber_eq_zero_const_mul (hzero : windingNumber γ a b z₀ = 0) (hc : c ≠ 0) :
    windingNumber (fun t => c * γ t) a b (c * z₀) = 0 := by
  rw [windingNumber_const_mul hc, hzero]

/-- Null-homology is preserved by nonzero complex scaling of both the curve and the ambient set. -/
theorem IsNullHomologous.const_mul (h : IsNullHomologous γ a b Ω) (hc : c ≠ 0) :
    IsNullHomologous (fun t => c * γ t) a b ((fun z => c * z) '' Ω) := by
  rw [isNullHomologous_iff] at h ⊢
  intro z hz
  have hpre_not_mem : c⁻¹ * z ∉ Ω := by
    intro hzΩ
    exact hz ⟨c⁻¹ * z, hzΩ, by field_simp [hc]⟩
  have hz_eq : z = c * (c⁻¹ * z) := by field_simp [hc]
  rw [hz_eq]
  exact windingNumber_eq_zero_const_mul (h (c⁻¹ * z) hpre_not_mem) hc

end TauCeti.Contour

end
