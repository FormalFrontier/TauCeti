/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.ModelSector.Corner
public import TauCeti.Analysis.Contour.Winding.Number.Circle
public import TauCeti.Analysis.Contour.Winding.Number.Concat
public import TauCeti.Analysis.Contour.Winding.Number.Reparam

/-!
# The Hungerbühler–Wasem model sector

The model sector of opening angle `α` at `z₀` is the closed curve made of a radial segment
inward to `z₀` along direction `φ + α`, a radial segment back out along direction `φ`, and a
circular arc of radius `r` sweeping `α` from `φ` round to `φ + α`, which closes the curve at the
point it started from. Both radii are traversed before the arc — the parameterization on
`[-r, r + α]` puts the corner at `0` and the arc on `(r, r + α]` — so the curve is traversed
from the far end of the incoming radius, not from the corner.

The geometry and closure hold for `0 ≤ r` and `0 ≤ α`, with `r = 0` and `α = 0` degenerate rather
than ill-formed; only the winding number needs `0 < r`, so that the arc avoids its centre. For
negative `r` or `α` the two parameter intervals reverse and this description does not apply.

Its generalized winding number about its own corner is `α / 2π` — the value HW (2.4) attaches
to a corner of interior angle `α` **when `0 < α < 2π`**, and the source of the `½` at a smooth
crossing and the `1/6` at a `π/3` corner. Outside that range the formula still holds but the
corner reading does not: at `α = 0` the two radii coincide, and for `α ≥ 2π` the arc wraps, so
the curve is a multi-turn swept arc rather than a sector.

The two radial segments are packaged as a single `twoRayCorner`, since neither has a principal
value on its own; the arc is a reparametrised `circleMap`.

## Main definitions

* `TauCeti.Contour.modelSector` — the model sector, on `[-r, r + α]` with the corner at parameter
  `0`; closed when `0 ≤ r` and `0 ≤ α`. The winding number needs `0 < r`, so that the arc
  avoids its centre.

## Main results

* `TauCeti.Contour.windingNumber_closedModelSector` — its winding number about `z₀`
  is `α / 2π`, for every `0 ≤ α`. This is the roadmap's acceptance criterion.
* `TauCeti.Contour.windingNumber_closedModelSector_eq_half` and
  `TauCeti.Contour.windingNumber_closedModelSector_eq_one_div_six` — the `½` at a smooth crossing
  and the `1/6` at a `π/3` corner, the two values the valence formula consumes.

This is Layer 1 of the Hungerbühler–Wasem generalized residue theorem (HW Thm 3.3).

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — (2.4).
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- **The Hungerbühler–Wasem model sector** of radius `r` and opening angle `α` at `z₀`, with the
incoming radius at angle `φ + α` and the outgoing one at angle `φ`.

For `0 ≤ r` and `0 ≤ α`: on `[-r, r]` it is the two-ray corner through `z₀`, running from
`z₀ + r e^{i(φ+α)}` in to `z₀` and back out to `z₀ + r e^{iφ}`; on `[r, r + α]` it is the arc of
radius `r` from angle `φ` to `φ + α`, returning to the start. At `r = 0` or `α = 0` the
corresponding piece degenerates to a point. For negative `r` or `α` the two intervals reverse and
the branches no longer line up that way. -/
def modelSector (z₀ : ℂ) (r φ α : ℝ) : ℝ → ℂ :=
  fun t =>
    if t ≤ r then
      twoRayCorner z₀ (Complex.exp ((φ + α : ℝ) * Complex.I)) (Complex.exp ((φ : ℝ) * Complex.I)) t
    else circleMap z₀ r (φ + (t - r))

/-- Pointwise value of the model sector on the corner interval. -/
@[simp]
theorem modelSector_of_le {z₀ : ℂ} {r φ α t : ℝ} (ht : t ≤ r) :
    modelSector z₀ r φ α t =
      twoRayCorner z₀ (Complex.exp ((φ + α : ℝ) * Complex.I))
        (Complex.exp ((φ : ℝ) * Complex.I)) t := if_pos ht

/-- Pointwise value of the model sector on the arc interval. -/
@[simp]
theorem modelSector_of_lt {z₀ : ℂ} {r φ α t : ℝ} (ht : r < t) :
    modelSector z₀ r φ α t = circleMap z₀ r (φ + (t - r)) := if_neg (not_le.mpr ht)

/-- The model sector starts at the outer end of the incoming radius. -/
-- Not a `simp` lemma: `modelSector_of_le` rewrites the left-hand side to its `twoRayCorner`
-- branch first, so this is not in simp normal form (simpNF rejects the attribute).
theorem modelSector_neg (z₀ : ℂ) {r : ℝ} (hr : 0 ≤ r) (φ α : ℝ) :
    modelSector z₀ r φ α (-r) = circleMap z₀ r (φ + α) := by
  rcases eq_or_lt_of_le hr with rfl | hpos
  · simp [neg_zero, circleMap]
  · rw [modelSector_of_le (by linarith), twoRayCorner_of_neg (by linarith)]
    simp [circleMap]

/-- The model sector ends at the outer end of the incoming radius, the same point it started
from. -/
@[simp]
theorem modelSector_add (z₀ : ℂ) {r : ℝ} (hr : 0 ≤ r) (φ : ℝ) {α : ℝ} (hα : 0 ≤ α) :
    modelSector z₀ r φ α (r + α) = circleMap z₀ r (φ + α) := by
  rcases eq_or_lt_of_le hα with rfl | hpos
  · rw [add_zero, modelSector_of_le le_rfl, twoRayCorner_of_nonneg hr]
    simp [circleMap]
  · rw [modelSector_of_lt (by linarith)]
    ring_nf

/-- **The model sector is a closed curve** for `0 ≤ r` and `0 ≤ α`. -/
theorem modelSector_closed (z₀ : ℂ) {r : ℝ} (hr : 0 ≤ r) (φ : ℝ) {α : ℝ} (hα : 0 ≤ α) :
    modelSector z₀ r φ α (-r) = modelSector z₀ r φ α (r + α) := by
  rw [modelSector_neg z₀ hr φ α, modelSector_add z₀ hr φ hα]

/-- On the corner interval the model sector is its two-ray corner. -/
theorem modelSector_eqOn_corner (z₀ : ℂ) {r : ℝ} (hr : 0 ≤ r) (φ α : ℝ) :
    EqOn (twoRayCorner z₀ (Complex.exp ((φ + α : ℝ) * Complex.I))
        (Complex.exp ((φ : ℝ) * Complex.I))) (modelSector z₀ r φ α) (uIoo (-r) r) := by
  intro t ht
  rw [Set.uIoo_of_le (by linarith), Set.mem_Ioo] at ht
  simp [modelSector, ht.2.le]

/-- On the arc interval the model sector is the reparametrised circle map. -/
theorem modelSector_eqOn_arc (z₀ : ℂ) (r φ : ℝ) {α : ℝ} (hα : 0 ≤ α) :
    EqOn (circleMap z₀ r ∘ fun t => 1 * t + (φ - r)) (modelSector z₀ r φ α) (uIoo r (r + α)) := by
  intro t ht
  rw [Set.uIoo_of_le (by linarith), Set.mem_Ioo] at ht
  have : ¬ t ≤ r := not_le.mpr ht.1
  simp only [modelSector, if_neg this, Function.comp_apply, one_mul]
  ring_nf

/-- The two ray directions of the model sector have equal (unit) length. -/
private theorem norm_modelSector_dirs (φ α : ℝ) :
    ‖Complex.exp ((φ + α : ℝ) * Complex.I)‖ = ‖Complex.exp ((φ : ℝ) * Complex.I)‖ := by
  rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]

/-- **The swept-arc curve has winding number `α / 2π` about its corner.** The two radial segments
contribute nothing and the arc contributes its swept angle.

This holds for every `0 ≤ α`, and is the roadmap's acceptance criterion. The curve is the
Hungerbühler–Wasem model sector of *interior angle* `α` only for `0 < α < 2π`: at `α = 0` the two
radii coincide, and at `α ≥ 2π` the arc wraps — `α = 4π` traverses the circle twice, giving winding
`2`. At both ends the formula stands; it is the corner reading that lapses. -/
@[simp]
theorem windingNumber_closedModelSector {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (φ : ℝ) {α : ℝ} (hα : 0 ≤ α) :
    windingNumber (modelSector z₀ r φ α) (-r) (r + α) z₀ = (α : ℂ) / (2 * (Real.pi : ℂ)) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have hcorner := modelSector_eqOn_corner z₀ hr.le φ α
  have harc := modelSector_eqOn_arc z₀ r φ hα
  have hcirc_diff : ∀ u ∈ uIcc (1 * r + (φ - r)) (1 * (r + α) + (φ - r)),
      DifferentiableAt ℝ (circleMap z₀ r) u := fun u _ => differentiable_circleMap z₀ r u
  have hcirc_deriv : ContinuousOn (deriv (circleMap z₀ r))
      (uIcc (1 * r + (φ - r)) (1 * (r + α) + (φ - r))) := by
    have hd : deriv (circleMap z₀ r) = fun θ => circleMap 0 r θ * Complex.I :=
      funext fun θ => deriv_circleMap z₀ r θ
    rw [hd]
    exact ((continuous_circleMap 0 r).mul continuous_const).continuousOn
  have hcirc_avoid : ∀ u ∈ uIcc (1 * r + (φ - r)) (1 * (r + α) + (φ - r)),
      circleMap z₀ r u ≠ z₀ := fun _ _ => circleMap_ne_center hrne
  have hpv_corner : CauchyPVExistsAt (modelSector z₀ r φ α) (-r) r (fun z => (z - z₀)⁻¹) z₀ :=
    (cauchyPVExistsAt_inv_sub_twoRayCorner (norm_modelSector_dirs φ α) r).congr_curve hcorner
  have hpv_arc : CauchyPVExistsAt (modelSector z₀ r φ α) r (r + α) (fun z => (z - z₀)⁻¹) z₀ :=
    (cauchyPVExistsAt_circleMap_comp_affine 1 (φ - r) r (r + α)).congr_curve harc
  rw [windingNumber_concat hpv_corner hpv_arc, ← windingNumber_congr_curve hcorner,
    ← windingNumber_congr_curve harc,
    windingNumber_eq_zero_twoRayCorner (norm_modelSector_dirs φ α) r,
    windingNumber_comp_mul_add hcirc_diff hcirc_deriv hcirc_avoid,
    windingNumber_circleMap_center hrne]
  push_cast
  ring

/-- **A smooth crossing contributes winding `½`** — the `α = π` model sector (HW (2.4)). This is
the coefficient of `ord_i f` in the valence formula: at the smooth boundary point `i` the contour
indents by a semicircle. -/
theorem windingNumber_closedModelSector_eq_half {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (φ : ℝ) :
    windingNumber (modelSector z₀ r φ Real.pi) (-r) (r + Real.pi) z₀ = 1 / 2 := by
  rw [windingNumber_closedModelSector hr φ Real.pi_nonneg]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- **A `π/3` corner contributes winding `1/6`** — the `α = π/3` model sector (HW (2.4)). The two
such corners `ρ` and `ρ + 1` of the fundamental domain sum to the `1/3` coefficient of
`ord_ρ f`. -/
theorem windingNumber_closedModelSector_eq_one_div_six {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (φ : ℝ) :
    windingNumber (modelSector z₀ r φ (Real.pi / 3)) (-r) (r + Real.pi / 3) z₀ = 1 / 6 := by
  rw [windingNumber_closedModelSector hr φ (by positivity)]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

end TauCeti.Contour

end

end
