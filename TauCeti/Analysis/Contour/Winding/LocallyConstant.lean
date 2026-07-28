/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Analysis.Contour.PiecewiseC1On
import TauCeti.Analysis.Contour.Curve.Distance
import TauCeti.Analysis.Contour.Winding.Continuity
import TauCeti.Analysis.Contour.Winding.Integer

/-!
# The winding number is locally constant off a closed curve

For a closed curve `γ` (so `γ a = γ b`) that is continuous on `Set.uIcc a b`, differentiable off a
countable set, with interval-integrable derivative, the generalized winding number
`fun w ↦ windingNumber γ a b w`, viewed as a function on the points off the curve, is locally
constant (`isLocallyConstant_windingNumber_of_closed`). It is the ingredient Dixon's argument uses
for the homology form of Cauchy's theorem (roadmap `homologyCauchyTheorem`). As a corollary,
the winding number is constant on every connected component of the curve complement. Also,
`exists_ball_windingNumber_zero` packages the local matching data Dixon needs: around an off-curve
point where the winding number vanishes, it vanishes on a whole ball that stays off the curve.

## Main results

* `TauCeti.Contour.isLocallyConstant_windingNumber_of_closed` — the winding number is locally
  constant on the complement of a closed curve.
* `TauCeti.Contour.windingNumber_eq_of_mem_connectedComponentIn` — the winding number is constant
  on each connected component of the curve complement.
* `TauCeti.Contour.IsPiecewiseC1On.windingNumber_eq_of_mem_connectedComponentIn` — the direct
  piecewise-`C¹` form.
* `TauCeti.Contour.exists_ball_windingNumber_zero` — around an off-curve point where the winding
  number vanishes, it vanishes on a whole ball that stays off the curve.

## Provenance

Adapted from `generalizedWindingNumber_locally_const_of_closed` in `WindingArgDiff.lean` of the
AINTLIB `LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on an oriented interval with
endpoints `a` and `b`.
-/

public section

open Complex MeasureTheory Set

open scoped Topology

namespace TauCeti.Contour

/-- **The winding number is locally constant off a closed curve.** Let `γ` be a closed curve
(`γ a = γ b`), differentiable off a countable set `P`, continuous on `Set.uIcc a b`, with
interval-integrable derivative. Then, as a function of the point ranging over the complement of the
curve, the generalized winding number `fun w ↦ windingNumber γ a b w` is locally constant. -/
theorem isLocallyConstant_windingNumber_of_closed {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) :
    IsLocallyConstant
      (fun w : {w : ℂ // ∀ t ∈ uIcc a b, γ t ≠ w} ↦ windingNumber γ a b w.1) := by
  -- The index integrand about any off-curve point is interval-integrable: a continuous factor
  -- `(γ · - w)⁻¹` times the integrable derivative.
  have hII : ∀ w : ℂ, (∀ t ∈ uIcc a b, γ t ≠ w) →
      IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b := fun w hw ↦
    intervalIntegrable_inv_sub_mul_deriv hγ_cont hw hderiv_int
  rw [IsLocallyConstant.iff_eventually_eq]
  rintro ⟨w₀, hw₀⟩
  -- A uniform lower bound `ρ ≤ ‖γ t - w₀‖`; on `ball w₀ (ρ / 2)` every point stays off `γ`, so the
  -- winding number about it is an integer (closed curve).
  obtain ⟨ρ, hρ_pos, h_dist⟩ := exists_curve_dist_lower_bound hγ_cont hw₀
  have key : ∀ w'' : ℂ, dist w'' w₀ < ρ / 2 → ∃ n : ℤ, windingNumber γ a b w'' = n := by
    intro w'' hw''
    rw [Complex.dist_eq] at hw''
    have h_avoid'' : ∀ t ∈ uIcc a b, γ t ≠ w'' := by
      intro t ht heq
      have hle := h_dist t ht
      rw [heq] at hle
      linarith
    exact exists_int_windingNumber_of_closed hclosed hP hγ_cont hγ_diff h_avoid''
      (hII w'' h_avoid'')
  obtain ⟨n₀, hn₀⟩ := key w₀ (by rw [dist_self]; exact half_pos hρ_pos)
  -- Continuity of the winding number at `w₀` gives a tolerance-`1 / 2` ball.
  have h_cont := continuousAt_windingNumber_of_avoidance hγ_cont hw₀ (hII w₀ hw₀)
  rw [Metric.continuousAt_iff] at h_cont
  obtain ⟨ε, hε_pos, h_close⟩ := h_cont (1 / 2) (by norm_num)
  -- On the smaller ball both winding numbers are integers within `1 / 2`, hence equal; so the
  -- winding number is eventually constant near `w₀`.
  have hball : ∀ᶠ w in 𝓝 w₀, windingNumber γ a b w = windingNumber γ a b w₀ := by
    filter_upwards [Metric.ball_mem_nhds w₀ (lt_min hε_pos (half_pos hρ_pos))] with w' hw'
    rw [Metric.mem_ball] at hw'
    obtain ⟨n', hn'⟩ := key w' (hw'.trans_le (min_le_right _ _))
    have h_dist_int : dist (n' : ℂ) (n₀ : ℂ) < 1 / 2 := by
      rw [← hn', ← hn₀]; exact h_close (hw'.trans_le (min_le_left _ _))
    have h_int_eq : n' = n₀ := by
      by_contra hne
      have h1 : (1 : ℝ) ≤ dist (n' : ℂ) (n₀ : ℂ) := by
        rw [Complex.isometry_intCast.dist_eq]; exact Int.pairwise_one_le_dist hne
      linarith
    rw [hn', hn₀, h_int_eq]
  -- Transport the neighbourhood statement to the subtype of off-curve points.
  have hval : Filter.Tendsto (Subtype.val : {w : ℂ // ∀ t ∈ uIcc a b, γ t ≠ w} → ℂ)
      (𝓝 ⟨w₀, hw₀⟩) (𝓝 w₀) := continuous_subtype_val.continuousAt
  exact hval.eventually hball

/-- The points avoided by `γ` on `[[a, b]]` are exactly the complement of its image there. -/
private theorem setOf_forall_ne_eq_compl_image {γ : ℝ → ℂ} {a b : ℝ} :
    {w : ℂ | ∀ t ∈ uIcc a b, γ t ≠ w} = (γ '' uIcc a b)ᶜ := by
  ext w
  simp only [mem_setOf_eq, mem_compl_iff, mem_image, not_exists, not_and]

/-- **The winding number is constant on a connected component of the curve complement.**
For a closed curve that is continuous on `[[a, b]]`, differentiable away from a countable set,
and has interval-integrable derivative, two points in the same connected component of
`ℂ \ γ '' [[a, b]]` have the same winding number.

This is the connected-component form of homotopy invariance in the point: it follows from local
constancy of the integer-valued winding number off the curve. -/
theorem windingNumber_eq_of_mem_connectedComponentIn {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    {w₀ w₁ : ℂ} (hw₀ : w₀ ∈ (γ '' uIcc a b)ᶜ)
    (hw₁ : w₁ ∈ connectedComponentIn ((γ '' uIcc a b)ᶜ) w₀) :
    windingNumber γ a b w₁ = windingNumber γ a b w₀ := by
  rw [← setOf_forall_ne_eq_compl_image] at hw₀ hw₁
  rw [connectedComponentIn_eq_image hw₀] at hw₁
  obtain ⟨w₁, hw₁, rfl⟩ := hw₁
  exact
    (isLocallyConstant_windingNumber_of_closed hclosed hP hγ_cont hγ_diff
      hderiv_int).apply_eq_of_isPreconnected isPreconnected_connectedComponent hw₁
        mem_connectedComponent

/-- **Piecewise-`C¹` form of componentwise constancy.** For a closed piecewise-`C¹` curve, two
points in the same connected component of the curve complement have the same winding number. -/
theorem IsPiecewiseC1On.windingNumber_eq_of_mem_connectedComponentIn
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    {w₀ w₁ : ℂ} (hw₀ : w₀ ∈ (γ '' uIcc a b)ᶜ)
    (hw₁ : w₁ ∈ connectedComponentIn ((γ '' uIcc a b)ᶜ) w₀) :
    windingNumber γ a b w₁ = windingNumber γ a b w₀ := by
  obtain ⟨P, hP, hγ_diff⟩ := hγ.exists_countable_differentiableAt
  exact TauCeti.Contour.windingNumber_eq_of_mem_connectedComponentIn hclosed hP
    hγ.continuousOn hγ_diff hγ.intervalIntegrable_deriv hw₀ hw₁

/-- **The winding number vanishes on a ball around an off-curve null point.** For a closed curve
`γ` (differentiable off a countable set, continuous on `uIcc a b`, with interval-integrable
derivative), if the winding number about an off-curve point `w` is `0`, then it is `0` throughout a
ball around `w` that stays off the curve. This is the local matching input for Dixon's argument: the
off-curve set is open, so the subtype-open set on which local constancy pins the winding number to
`0` pushes forward, along the open inclusion `Subtype.val`, to a `ℂ`-ball. -/
theorem exists_ball_windingNumber_zero {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) (hw_zero : windingNumber γ a b w = 0) :
    ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
      (∀ t ∈ uIcc a b, γ t ≠ w') ∧ windingNumber γ a b w' = 0 := by
  obtain ⟨ε₁, hε₁, h_dist⟩ := exists_ball_dist_curve_lower_bound hγ_cont hoff
  -- The off-curve set is open: it is the complement of the compact curve image.
  have hSopen : IsOpen {z : ℂ | ∀ t ∈ uIcc a b, γ t ≠ z} := by
    have hset : {z : ℂ | ∀ t ∈ uIcc a b, γ t ≠ z} = (γ '' uIcc a b)ᶜ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and, ne_eq]
    rw [hset]
    exact (isCompact_uIcc.image_of_continuousOn hγ_cont).isClosed.isOpen_compl
  -- The winding number is locally constant off the curve, so it is `0` on a subtype-open set
  -- around `w`; push that set forward along the open inclusion to a `ℂ`-ball.
  have hlc := isLocallyConstant_windingNumber_of_closed hclosed hP hγ_cont hγ_diff hderiv_int
  obtain ⟨V, hV_open, hwV, hV_const⟩ := hlc.exists_open ⟨w, hoff⟩
  have hVℂ : IsOpen (Subtype.val '' V) := hSopen.isOpenMap_subtype_val V hV_open
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.isOpen_iff.mp hVℂ w ⟨⟨w, hoff⟩, hwV, rfl⟩
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun w' hw' ↦ ⟨fun t ht ↦ ?_, ?_⟩⟩
  · exact sub_ne_zero.mp (norm_pos_iff.mp (lt_of_lt_of_le hε₁
      (h_dist w' (Metric.ball_subset_ball (min_le_left _ _) hw') t ht)))
  · obtain ⟨p, hpV, hpeq⟩ := hball₂ (Metric.ball_subset_ball (min_le_right _ _) hw')
    rw [← hpeq, hV_const p hpV]
    exact hw_zero

end TauCeti.Contour
