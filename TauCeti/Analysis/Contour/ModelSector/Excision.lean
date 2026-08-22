/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Crossing.Excision
public import TauCeti.Analysis.Contour.ModelSector.Closed

/-!
# Excising the corner of a model sector

`TauCeti.Contour.exciseCrossing` deletes a parameter window from a curve and caps it with a
circular arc, and `TauCeti.Contour.windingNumber_eq_exciseCrossing_add` accounts exactly for the
winding number that the surgery moves. This file runs that surgery on the one crossing whose
geometry is completely known: the corner of the model sector `TauCeti.Contour.modelSector` of
radius `r` and opening angle `α`, whose two rays leave the corner at the angles `φ + α` and `φ`.

Deleting the window `[-ε, ε]` about the corner and capping it with the arc of the circle of radius
`ε` running from angle `φ + α` back to angle `φ` leaves a closed curve of winding number `0`
(`TauCeti.Contour.windingNumber_eq_zero_exciseCrossing_modelSector`). Equivalently, the sector's
entire index `α / 2π` is the local contribution of its crossing — the model case of the
identification that Hungerbühler–Wasem Proposition 2.2 asserts for a general immersion, and hence
an acceptance test for the surgery.

## Main results

* `TauCeti.Contour.windingNumber_eq_zero_exciseCrossing_modelSector` — excising the corner of a
  model sector leaves winding number `0`.

## Provenance

No formalization is vendored; the statement is a direct application of
`TauCeti.Contour.windingNumber_eq_exciseCrossing_add` to the model sector already in the tree.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — Proposition 2.2, and the model sector of their equation (2.4).
-/

public section

namespace TauCeti.Contour

open Set

/-- **Excising the corner of a model sector leaves nothing.** The model sector of radius `r` and
opening angle `α` crosses its own corner along two straight radii; deleting the window `[-ε, ε]`
and capping it with the arc from angle `φ + α` back to angle `φ` produces a closed curve of winding
number `0`.

Equivalently, the sector's entire index `α / 2π` is the local contribution of its crossing, which is
the model case of the identification that HW Proposition 2.2 asserts for a general immersion. -/
theorem windingNumber_eq_zero_exciseCrossing_modelSector {z₀ : ℂ} {r ε φ α : ℝ} (hε : 0 < ε)
    (hεr : ε < r) (hα : 0 ≤ α) :
    windingNumber (exciseCrossing (modelSector z₀ r φ α) z₀ ε (-ε) ε (φ + α) φ)
      (-r) (r + α) z₀ = 0 := by
  have hr : 0 < r := hε.trans hεr
  set U : ℂ := Complex.exp ((φ + α : ℝ) * Complex.I) with hU
  set V : ℂ := Complex.exp ((φ : ℝ) * Complex.I) with hV
  have hVnorm : ‖V‖ = 1 := by rw [hV, Complex.norm_exp_ofReal_mul_I]
  have hUnorm : ‖U‖ = 1 := by rw [hU, Complex.norm_exp_ofReal_mul_I]
  have hUV : ‖U‖ = ‖V‖ := by rw [hUnorm, hVnorm]
  -- on the corner interval the sector is its two-ray corner
  have hcorner : EqOn (twoRayCorner z₀ U V) (modelSector z₀ r φ α) (uIoo (-ε) ε) := by
    intro t ht
    refine modelSector_eqOn_corner z₀ hr.le φ α ?_
    rw [uIoo_of_le (by linarith : -ε ≤ ε)] at ht
    rw [uIoo_of_le (by linarith : -r ≤ r)]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- off the window the sector misses its corner
  have havoid : ∀ t ∈ Icc (-r) (r + α), t ∉ Ioo (-ε) ε → modelSector z₀ r φ α t ≠ z₀ := by
    intro t _ ht
    have habs : ε ≤ |t| := by
      rcases le_or_gt t 0 with h | h
      · rw [abs_of_nonpos h]
        by_contra hcon
        exact ht ⟨by linarith [not_le.mp hcon], by linarith⟩
      · rw [abs_of_pos h]
        by_contra hcon
        exact ht ⟨by linarith, not_le.mp hcon⟩
    rcases le_or_gt t r with hle | hgt
    · rw [modelSector_of_le hle, ← sub_ne_zero, ← norm_ne_zero_iff, norm_twoRayCorner_sub hUV,
        hVnorm, mul_one]
      exact fun h => absurd (h ▸ habs) (by simpa using hε)
    · rw [modelSector_of_lt hgt]
      exact circleMap_ne_center hr.ne'
  -- the corner's own index vanishes, and its principal value exists
  have hpv : CauchyPVExistsAt (modelSector z₀ r φ α) (-ε) ε (fun z => (z - z₀)⁻¹) z₀ :=
    (cauchyPVExistsAt_inv_sub_twoRayCorner hUV ε).congr_curve hcorner
  have hzero : windingNumber (modelSector z₀ r φ α) (-ε) ε z₀ = 0 := by
    rw [← windingNumber_congr_curve hcorner]
    exact windingNumber_eq_zero_twoRayCorner hUV ε
  have hmain := windingNumber_eq_exciseCrossing_add (θ := φ + α) (θ' := φ)
    (isPiecewiseC1On_modelSector hr.le φ α) (by linarith : -r < -ε) (by linarith : -ε < ε)
    (by linarith : ε < r + α) hε.ne' havoid hpv
  rw [windingNumber_closedModelSector hr φ hα, hzero] at hmain
  have hcast : ((φ - (φ + α) : ℝ) : ℂ) = -(α : ℂ) := by push_cast; ring
  rw [hcast] at hmain
  linear_combination -hmain

end TauCeti.Contour

end
