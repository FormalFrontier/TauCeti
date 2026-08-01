/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Scale
public import TauCeti.Analysis.Contour.Winding.Number.Translate

/-!
# Affine coordinate changes for contour winding numbers

This file packages the translation and nonzero-scaling invariance of the generalized winding
number into the affine-coordinate form used by local contour geometry. A sector or crossing is
typically normalized by sending its distinguished point to the origin and rescaling the tangent
direction; the results here let downstream finite-decomposition arguments use the single map
`z ↦ c * z + d` rather than manually alternating the separate translation and scaling lemmas.

## Main results

* `Contour.windingNumber_affine` — simultaneous affine change of the curve and base point
  preserves the generalized winding number when the linear coefficient is nonzero.
* `Contour.windingNumber_affine_preimage` — the same statement with an arbitrary target point,
  pulled back through the inverse affine map.
* `Contour.IsNullHomologous.affine` — null-homology is preserved by affine image of the curve and
  ambient set.
* `Contour.isNullHomologous_affine_iff` — the corresponding equivalence for nondegenerate affine
  coordinate changes.

## Provenance

This is routine API around the Hungerbühler--Wasem generalized winding number from the contour
integration roadmap; no formal source is vendored. It combines the existing Tau Ceti translation
and scaling invariance lemmas.
-/

public section

noncomputable section

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {a b : ℝ} {z₀ z c d : ℂ} {Ω : Set ℂ}

/-- The kernel integrand used to define the generalized winding number about `z₀`. This local
abbreviation keeps the affine principal-value statements readable. -/
local notation "κ[" z "]" => (fun w : ℂ => (w - z)⁻¹)

private lemma affine_apply_preimage (hc : c ≠ 0) (z d : ℂ) :
    c * (c⁻¹ * (z - d)) + d = z := by
  have hmul : c * (c⁻¹ * (z - d)) = z - d := by
    field_simp [hc]
  rw [hmul]
  ring

/-- **Index principal value under an affine coordinate change.** If `c ≠ 0`, applying
`z ↦ c * z + d` to both the curve and the distinguished point transports the single-point Cauchy
principal value of the winding kernel without changing its value. This is the composed
translation/scaling form of `hasCauchyPVAt_inv_sub_const_mul`. -/
theorem hasCauchyPVAt_inv_sub_affine (h : HasCauchyPVAt γ a b κ[z₀] z₀ L) (hc : c ≠ 0) :
    HasCauchyPVAt (fun t => c * γ t + d) a b κ[c * z₀ + d] (c * z₀ + d) L := by
  refine ((hasCauchyPVAt_inv_sub_const_mul (c := c) h hc).translate d).congr_along_curve ?_
  intro t _ht
  congr 1
  ring

/-- Existence form of `hasCauchyPVAt_inv_sub_affine`: affine coordinate changes with nonzero
linear coefficient preserve existence of the index principal value. -/
theorem cauchyPVExistsAt_inv_sub_affine (h : CauchyPVExistsAt γ a b κ[z₀] z₀) (hc : c ≠ 0) :
    CauchyPVExistsAt (fun t => c * γ t + d) a b κ[c * z₀ + d] (c * z₀ + d) :=
  let ⟨_, hL⟩ := cauchyPVExistsAt_iff.mp h
  CauchyPVExistsAt.intro (hasCauchyPVAt_inv_sub_affine (d := d) hL hc)

/-- The generalized winding number is invariant under simultaneous affine coordinate change of
the curve and base point, provided the linear coefficient is nonzero. -/
theorem windingNumber_affine (hc : c ≠ 0) :
    windingNumber (fun t => c * γ t + d) a b (c * z₀ + d) = windingNumber γ a b z₀ := by
  calc
    windingNumber (fun t => c * γ t + d) a b (c * z₀ + d)
        = windingNumber (fun t => c * γ t) a b (c * z₀) := by
          exact windingNumber_translate (γ := fun t => c * γ t) (a := a) (b := b)
            (z₀ := c * z₀) d
    _ = windingNumber γ a b z₀ := windingNumber_const_mul (γ := γ) (a := a) (b := b)
      (z₀ := z₀) hc

/-- Pulling the base point back through a nondegenerate affine map gives the value of the winding
number of the affine image about an arbitrary point. -/
theorem windingNumber_affine_preimage (hc : c ≠ 0) :
    windingNumber (fun t => c * γ t + d) a b z =
      windingNumber γ a b (c⁻¹ * (z - d)) := by
  have hz : z = c * (c⁻¹ * (z - d)) + d := (affine_apply_preimage hc z d).symm
  calc
    windingNumber (fun t => c * γ t + d) a b z
        = windingNumber (fun t => c * γ t + d) a b (c * (c⁻¹ * (z - d)) + d) := by
          exact congrArg (fun w => windingNumber (fun t => c * γ t + d) a b w) hz
    _ = windingNumber γ a b (c⁻¹ * (z - d)) :=
      windingNumber_affine (γ := γ) (a := a) (b := b) (z₀ := c⁻¹ * (z - d)) hc

/-- Null-homology is preserved by affine coordinate change of the curve and ambient set, provided
the linear coefficient is nonzero. -/
theorem IsNullHomologous.affine (h : IsNullHomologous γ a b Ω) (hc : c ≠ 0) :
    IsNullHomologous (fun t => c * γ t + d) a b ((fun z => c * z + d) '' Ω) := by
  simpa [Set.image_image, Function.comp_def] using (h.const_mul hc).translate d

/-- If the affine image of a curve is null-homologous in the affine image of a set, then the
original curve is null-homologous in the original set. -/
theorem IsNullHomologous.of_affine
    (h : IsNullHomologous (fun t => c * γ t + d) a b ((fun z => c * z + d) '' Ω)) (hc : c ≠ 0) :
    IsNullHomologous γ a b Ω := by
  rw [isNullHomologous_iff] at h ⊢
  intro z hz
  have himage_not_mem : c * z + d ∉ (fun z => c * z + d) '' Ω := by
    rintro ⟨w, hwΩ, hw⟩
    have hcz : c * z = c * w := by
      exact (add_right_cancel hw).symm
    exact hz ((mul_left_cancel₀ hc hcz).symm ▸ hwΩ)
  have hzero := h (c * z + d) himage_not_mem
  rwa [windingNumber_affine (γ := γ) (a := a) (b := b) (z₀ := z) hc] at hzero

/-- A nondegenerate affine coordinate change preserves and reflects null-homology. -/
theorem isNullHomologous_affine_iff (hc : c ≠ 0) :
    IsNullHomologous (fun t => c * γ t + d) a b ((fun z => c * z + d) '' Ω)
      ↔ IsNullHomologous γ a b Ω :=
  ⟨fun h => h.of_affine hc, fun h => h.affine hc⟩

end TauCeti.Contour

end
