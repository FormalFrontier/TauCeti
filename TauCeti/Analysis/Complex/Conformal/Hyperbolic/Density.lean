/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.Hyperbolic.Distance
public import TauCeti.Analysis.SpecialFunctions.Artanh

/-!
# The infinitesimal density of the Poincaré metric

`Hyperbolic/Distance.lean` defines the hyperbolic (Poincaré) distance on the complex open unit
disc in closed form, `hyperbolicDist z w = Real.artanh (pseudoHyperbolicExpr z w)`, and its
docstring asserts that this normalisation "agrees with the infinitesimal Poincaré metric
`|dz| / (1 - |z| ^ 2)`". Nothing in the disc files proved that assertion: the closed form and
the conformal density were never connected. This file connects them, in the two ways the
statement is normally read.

*Differentially.* Along any approach to a point `z` of the disc, the ratio of hyperbolic to
Euclidean distance tends to `(1 - ‖z‖ ^ 2)⁻¹`
(`TauCeti.tendsto_hyperbolicDist_div_norm_sub`). The proof factors the ratio as

`hyperbolicDist z w / ‖w - z‖ = (artanh p / p) * ‖1 - conj w * z‖⁻¹`

for `p = pseudoHyperbolicExpr z w`, which is legitimate off the diagonal because `p` is
exactly `‖w - z‖ / ‖1 - conj w * z‖`. As
`w → z` the first factor tends to `1` — this is `Real.tendsto_artanh_div_nhdsNE_zero`,
the derivative of `Real.artanh` at the origin read as a limit of slopes — while the Moebius
denominator tends to `1 - ‖z‖ ^ 2`, which is where the density comes from.

*Integrally.* The hyperbolic distance from the origin along a radius is the integral of the
density over that radius, `∫ t in (0)..r, (1 - t ^ 2)⁻¹ = hyperbolicDist 0 (r * u)` for a unit
vector `u` (`TauCeti.integral_one_sub_sq_inv_eq_hyperbolicDist_zero`): the hyperbolic distance
to a point is the length, in the density, of the radius joining it to the origin — and
`Poincare/Geodesic.lean` shows those radii to be the geodesics through the origin. Only radii
are treated here. Neither the density-weighted length of a general curve nor the infimum of
such lengths between two arbitrary points is defined anywhere in the tree, so nothing below
identifies `hyperbolicDist` as the length metric induced by the density; that identification
would need those definitions first.

Bounding the density between its values at the endpoints of a radius also gives the two-sided
comparison of the hyperbolic distance with the pseudo-hyperbolic expression,
`p ≤ hyperbolicDist ≤ p / (1 - p ^ 2)`; the lower bound sharpens the crude Euclidean estimate
`‖z - w‖ ≤ 2 * p` of `Poincare/Topology.lean` into `‖z - w‖ / ‖1 - conj w * z‖ ≤ hyperbolicDist`.

## Main declarations

* `TauCeti.pseudoHyperbolicExpr_le_hyperbolicDist` and
  `TauCeti.hyperbolicDist_le_pseudoHyperbolicExpr_div_one_sub_sq` — the two-sided comparison of the
  hyperbolic distance with the pseudo-hyperbolic expression.
* `TauCeti.tendsto_hyperbolicDist_div_norm_sub` — the infinitesimal Poincaré density
  `(1 - ‖z‖ ^ 2)⁻¹` at a point `z` of the disc.
* `TauCeti.tendsto_hyperbolicDist_zero_div_norm` — the density at the origin is `1`, so the
  hyperbolic and Euclidean metrics are infinitesimally equal there.
* `TauCeti.integral_one_sub_sq_inv_eq_hyperbolicDist_zero` — the radial form of the density.

This carries the conformal-mapping roadmap's L2 target "the hyperbolic / Poincaré metric on
`𝔻`" (see `ConformalMapping/README.md`) onto its infinitesimal side, and reuses Tau Ceti's
pseudo-hyperbolic and hyperbolic-distance API throughout. As with the rest of the L0--L3
conformal-mapping material, it is coordinated with the upstream Mathlib Riemann mapping effort
leanprover-community/mathlib4#33505 and should be refactored to upstream API if that work lands
a human-curated Poincaré metric; Mathlib's preceding human-curated work in
`Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean` is neither
duplicated nor extended here. Mathlib has the hyperbolic metric on the upper half-plane
(`Analysis/Complex/UpperHalfPlane/Metric.lean`), but records no density statement for it
either.
-/

public section

namespace TauCeti

open Filter Metric Set

open scoped ComplexConjugate Topology

/-! ### Comparison with the pseudo-hyperbolic expression -/

/-- The hyperbolic distance dominates the pseudo-hyperbolic expression: `Real.artanh` moves
`[0, 1)` upwards because the Poincaré density is at least `1`.

All that is needed is that the pseudo-hyperbolic expression lies below `1`; for two points of
the open unit disc that is `TauCeti.pseudoHyperbolicExpr_lt_one_of_norm_lt_one`. -/
theorem pseudoHyperbolicExpr_le_hyperbolicDist {z w : ℂ} (h : pseudoHyperbolicExpr z w < 1) :
    pseudoHyperbolicExpr z w ≤ hyperbolicDist z w := by
  rw [hyperbolicDist_def]
  exact Real.self_le_artanh (pseudoHyperbolicExpr_nonneg z w) h

/-- The hyperbolic distance is bounded above by `p / (1 - p ^ 2)`, where `p` is the
pseudo-hyperbolic expression: the Poincaré density on `[0, p]` is at most its value at `p`.

As for the lower bound, only `p < 1` is needed, which holds for two points of the open unit
disc by `TauCeti.pseudoHyperbolicExpr_lt_one_of_norm_lt_one`. -/
theorem hyperbolicDist_le_pseudoHyperbolicExpr_div_one_sub_sq {z w : ℂ}
    (h : pseudoHyperbolicExpr z w < 1) :
    hyperbolicDist z w ≤ pseudoHyperbolicExpr z w / (1 - pseudoHyperbolicExpr z w ^ 2) := by
  rw [hyperbolicDist_def]
  exact Real.artanh_le_self_div_one_sub_sq (pseudoHyperbolicExpr_nonneg z w) h

/-- The Euclidean distance divided by the Moebius denominator is a lower bound for the
hyperbolic distance, sharpening the crude estimate `‖z - w‖ ≤ 2 * pseudoHyperbolicExpr z w`. -/
theorem norm_sub_div_norm_one_sub_conj_mul_le_hyperbolicDist {z w : ℂ}
    (h : pseudoHyperbolicExpr z w < 1) :
    ‖z - w‖ / ‖1 - (starRingEnd ℂ) w * z‖ ≤ hyperbolicDist z w := by
  rw [← pseudoHyperbolicExpr_eq_norm_div_norm]
  exact pseudoHyperbolicExpr_le_hyperbolicDist h

/-! ### The infinitesimal density -/

/-- The pseudo-hyperbolic expression `pseudoHyperbolicExpr z w`, viewed as a function of its
second argument, is continuous at any point `w` of the disc: the joint continuity
`TauCeti.continuousOn_pseudoHyperbolicExpr` restricted to a slice of the open product. -/
private lemma continuousAt_pseudoHyperbolicExpr_right {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ContinuousAt (fun v : ℂ => pseudoHyperbolicExpr z v) w := by
  have hjoint : ContinuousAt (fun p : ℂ × ℂ => pseudoHyperbolicExpr p.1 p.2) (z, w) :=
    continuousOn_pseudoHyperbolicExpr.continuousAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds
        ⟨mem_ball_zero_iff.2 hz, mem_ball_zero_iff.2 hw⟩)
  exact hjoint.comp (continuousAt_const.prodMk continuousAt_id)

/-- **The infinitesimal Poincaré density.** At a point `z` of the open unit disc the ratio of
the hyperbolic distance to the Euclidean distance tends to `(1 - ‖z‖ ^ 2)⁻¹`.

This is the precise sense in which `TauCeti.hyperbolicDist` has infinitesimal density
`|dz| / (1 - |z| ^ 2)`: the closed form `Real.artanh` of the pseudo-hyperbolic expression is
only a reparametrisation, and the density it produces at `z` is read off from the Moebius
denominator `1 - conj z * z`. It is a statement about the first order behaviour at `z` alone;
calling `hyperbolicDist` the distance *induced* by that density would need the density-weighted
length of a curve, which is defined nowhere in the tree (see the module docstring). -/
theorem tendsto_hyperbolicDist_div_norm_sub {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun w => hyperbolicDist z w / ‖w - z‖) (𝓝[≠] z) (𝓝 (1 - ‖z‖ ^ 2)⁻¹) := by
  have hzB : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.2 hz
  have hfilter : 𝓝[≠] z = 𝓝[{z}ᶜ ∩ ball (0 : ℂ) 1] z :=
    nhdsWithin_restrict' _ (isOpen_ball.mem_nhds hzB)
  have hdenval : ‖1 - (starRingEnd ℂ) z * z‖ = 1 - ‖z‖ ^ 2 :=
    norm_one_sub_conj_mul_self_of_norm_le_one hz.le
  have hdenpos : (0 : ℝ) < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  -- the pseudo-hyperbolic expression tends to `0` through nonzero values
  have hP : Tendsto (fun w => pseudoHyperbolicExpr z w) (𝓝[{z}ᶜ ∩ ball (0 : ℂ) 1] z)
      (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, eventually_nhdsWithin_of_forall fun w hw => ?_⟩
    · have h := (continuousAt_pseudoHyperbolicExpr_right hz hz).tendsto
      rw [pseudoHyperbolicExpr_self] at h
      exact h.mono_left nhdsWithin_le_nhds
    · have hne : z ≠ w := fun h => hw.1 h.symm
      simpa [pseudoHyperbolicExpr_eq_zero_iff_of_mem_ball hzB hw.2] using hne
  -- the first factor of the product decomposition
  have hquot : Tendsto
      (fun w => Real.artanh (pseudoHyperbolicExpr z w) / pseudoHyperbolicExpr z w)
      (𝓝[{z}ᶜ ∩ ball (0 : ℂ) 1] z) (𝓝 1) :=
    Real.tendsto_artanh_div_nhdsNE_zero.comp hP
  -- the second factor of the product decomposition
  have hinv : Tendsto (fun w : ℂ => ‖1 - (starRingEnd ℂ) w * z‖⁻¹)
      (𝓝[{z}ᶜ ∩ ball (0 : ℂ) 1] z) (𝓝 (1 - ‖z‖ ^ 2)⁻¹) := by
    have hden : Tendsto (fun v : ℂ => ‖1 - (starRingEnd ℂ) v * z‖) (𝓝 z) (𝓝 (1 - ‖z‖ ^ 2)) := by
      rw [← hdenval]
      exact (continuous_const.sub (Complex.continuous_conj.mul continuous_const)).norm.tendsto z
    exact (hden.inv₀ hdenpos.ne').mono_left nhdsWithin_le_nhds
  have hmul := hquot.mul hinv
  rw [one_mul] at hmul
  -- the product decomposition itself, at a point of the disc
  have hpt : ∀ w ∈ ball (0 : ℂ) 1,
      Real.artanh (pseudoHyperbolicExpr z w) / pseudoHyperbolicExpr z w *
        ‖1 - (starRingEnd ℂ) w * z‖⁻¹ = hyperbolicDist z w / ‖w - z‖ := by
    intro w hwB
    have hdne : ‖1 - (starRingEnd ℂ) w * z‖ ≠ 0 :=
      norm_ne_zero_iff.2 (one_sub_conj_mul_ne_zero_of_mem_ball hzB hwB)
    have hfac : pseudoHyperbolicExpr z w * ‖1 - (starRingEnd ℂ) w * z‖ = ‖w - z‖ := by
      rw [pseudoHyperbolicExpr_eq_norm_div_norm, div_mul_cancel₀ _ hdne, norm_sub_rev]
    rw [hyperbolicDist_def, ← hfac, ← div_div]
    exact (div_eq_mul_inv _ _).symm
  rw [hfilter]
  exact Tendsto.congr' (eventually_nhdsWithin_of_forall fun w hw => hpt w hw.2) hmul

/-- **The Poincaré density at the origin is `1`.** The hyperbolic and Euclidean metrics of the
disc agree to first order at the centre. -/
theorem tendsto_hyperbolicDist_zero_div_norm :
    Tendsto (fun w : ℂ => hyperbolicDist 0 w / ‖w‖) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
  simpa using tendsto_hyperbolicDist_div_norm_sub (z := (0 : ℂ)) (by simp)

/-! ### The radial form of the density -/

/-- **The hyperbolic distance along a radius is the integral of the density.** For a unit
vector `u` and a radius `r` in `[0, 1)`, the hyperbolic distance from the origin to `r * u` is
`∫ t in (0)..r, (1 - t ^ 2)⁻¹`.

This is the radial case of the agreement between `TauCeti.hyperbolicDist` and the density
`|dz| / (1 - |z| ^ 2)`, and only that case: the radii through the origin are geodesics of the
Poincaré disc (`TauCeti.PoincareDisc.isometry_radialGeodesic`), but the density-weighted length
of a general curve is not defined here, so this does not identify `hyperbolicDist` with the
length metric of the density between arbitrary points. -/
theorem integral_one_sub_sq_inv_eq_hyperbolicDist_zero {u : ℂ} (hu : ‖u‖ = 1) {r : ℝ}
    (hr : 0 ≤ r) (hr₁ : r < 1) :
    (∫ t in (0 : ℝ)..r, (1 - t ^ 2)⁻¹) = hyperbolicDist ((r : ℂ) * u) 0 := by
  rw [Real.integral_one_sub_sq_inv_eq_artanh ⟨by linarith, hr₁⟩, hyperbolicDist_zero_right,
    norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

end TauCeti
