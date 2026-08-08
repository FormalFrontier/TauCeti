/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Crosscut.Basic
import Mathlib.Geometry.Euclidean.Basic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arccos
import TauCeti.Topology.Circle.Metric

/-!
# The endpoints of a circular crosscut

For a point `ζ` on `sphere c r` and a radius `ρ` with `0 < ρ < 2 * r`, the circle
`sphere ζ ρ` cuts the disc `ball c r` in one open arc. This file identifies that arc, its closed
companion, and its two endpoints exactly. If

* `α = arg (c - ζ)` is the direction from `ζ` to the centre, and
* `φ = arccos (ρ / (2 * r))` is the half-angle of the crosscut,

then the open and closed arcs are the images under `circleMap ζ ρ` of `(α - φ, α + φ)` and
`[α - φ, α + φ]`, while the two bounding circles meet at the images of the endpoints. Since
`φ < π / 2`, a crosscut spans less than a half turn, and the chord length along it is therefore
unimodal about any one of its points; that is what makes a crosscut *locally connected at its own
endpoints*, the last statement below.

This is the source-side endpoint interface needed by layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`, the Jordan-domain case of Carathéodory boundary
correspondence. `Conformal/ShortCrosscut.lean` makes the image of the *open* arc arbitrarily short,
and `Conformal/CutDiameter.lean` asks local connectedness of the image boundary to join the two
ends by a small boundary set. The results here name those two ends and package the open arc together
with its closure; they do not assert the continuous boundary extension itself.

## Main results

* `TauCeti.arccos_div_two_mul_pos` and `TauCeti.arccos_div_two_mul_lt_pi_div_two` bound the
  half-angle: it is positive, and below `π / 2`. These two facts are the standing hypotheses of
  almost every argument along a crosscut — they are what make the angular window nondegenerate and
  shorter than a period — and every crosscut file routes through them rather than re-deriving them
  from `Real.arccos_pos` and `Real.arccos_lt_pi_div_two`.
* `TauCeti.ball_inter_sphere_eq_circleMap_image_Ioo` and
  `TauCeti.closedBall_inter_sphere_eq_circleMap_image_Icc` identify the open and closed crosscut
  arcs.
* `TauCeti.sphere_inter_sphere_eq_pair_circleMap` identifies their two distinct endpoints.
* `TauCeti.isPathConnected_ball_inter_sphere` and
  `TauCeti.closure_ball_inter_sphere` give the corresponding topological packaging, and
  `TauCeti.nonempty_frontier_ball_inter_closure_ball_inter_sphere` records that a crosscut reaches
  the frontier of the disc.
* `TauCeti.isPreconnected_ball_inter_sphere_inter_ball` — a ball centred at a point of the closed
  crosscut meets the crosscut in a subarc: a crosscut spans less than a half turn, so along it the
  chord distance to a fixed one of its points falls and then rises, and the angles it keeps below a
  threshold form an interval. That last step is
  `TauCeti.ordConnected_inter_setOf_dist_circleMap_lt` and the chord length it runs on is measured
  by `TauCeti.dist_circleMap_eq_two_mul_abs_sin`; both live in
  `TauCeti/Topology/Circle/Metric.lean`, since neither mentions the disc. This is the
  local connectedness of a crosscut at its own endpoints,
  which `Conformal/Crosscut/Image.lean` spends to make the cluster set of a conformal map at an end
  of an image crosscut a continuum.

The half-width `arccos (ρ / (2 * r))` is read off the cosine criterion of
`TauCeti/Topology/Circle/Metric.lean` through `Real.lt_cos_iff_mem_Ioo` and
`Real.le_cos_iff_mem_Icc`, the arccosine description of the angles at which the cosine exceeds a
threshold, in `TauCeti/Analysis/SpecialFunctions/Trigonometric/Arccos.lean`.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort. Mathlib supplies `circleMap`, its periodicity and
injectivity on one period, inverse trigonometric functions, and the generic fact that two circles in
the plane meet in at most two points; none of the crosscut descriptions below is present there.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open Complex Metric Set Topology
open scoped Real

variable {c ζ : ℂ} {r ρ : ℝ}

/-! ## The half-angle -/

/-- **The half-angle of a genuine circular crosscut is positive**, so the crosscut occupies a
nondegenerate arc of angles. This is `Real.arccos_pos` at `ρ / (2 * r)`, the argument being below
`1` exactly because `ρ < 2 * r`. -/
theorem arccos_div_two_mul_pos (hr : 0 < r) (hρr : ρ < 2 * r) :
    0 < Real.arccos (ρ / (2 * r)) :=
  Real.arccos_pos.mpr ((div_lt_one (by linarith)).mpr hρr)

/-- **A genuine circular crosscut spans less than a half turn**: its half-angle is below `π / 2`.
This is `Real.arccos_lt_pi_div_two` at `ρ / (2 * r)`, the argument being positive exactly because
`0 < ρ`.

The bound is what makes the chord distance along a crosscut unimodal
(`TauCeti.isPreconnected_ball_inter_sphere_inter_ball`) and what keeps the closed arc of angles
inside one period, so that `TauCeti.circleMap` is injective on it. -/
theorem arccos_div_two_mul_lt_pi_div_two (hρ : 0 < ρ) (hr : 0 < r) :
    Real.arccos (ρ / (2 * r)) < π / 2 :=
  Real.arccos_lt_pi_div_two.mpr (div_pos hρ (by linarith))

/-! ## Metric and angular descriptions -/

/-- A point of `sphere ζ ρ`, in angular coordinates, lies in `closedBall c r` exactly when its
angle satisfies the weak cosine inequality complementary to
`TauCeti.circleMap_mem_ball_iff`.

This is the general criterion `TauCeti.circleMap_mem_closedBall_iff_sq` at `dist ζ c = r`, where
the two squared radii cancel and the surviving condition
`ρ ^ 2 ≤ 2 * ρ * r * cos (θ - arg (c - ζ))` may be divided by `ρ > 0`. -/
theorem circleMap_mem_closedBall_iff (hζ : dist ζ c = r) (hρ : 0 < ρ) (θ : ℝ) :
    circleMap ζ ρ θ ∈ closedBall c r ↔
      ρ ≤ 2 * r * Real.cos (θ - (c - ζ).arg) := by
  rw [circleMap_mem_closedBall_iff_sq (hζ ▸ dist_nonneg) ρ θ, hζ]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- The `simp`-normal form of `TauCeti.circleMap_mem_closedBall_iff`. -/
@[simp]
theorem dist_circleMap_le_iff (hζ : dist ζ c = r) (hρ : 0 < ρ) (θ : ℝ) :
    dist (circleMap ζ ρ θ) c ≤ r ↔
      ρ ≤ 2 * r * Real.cos (θ - (c - ζ).arg) :=
  circleMap_mem_closedBall_iff hζ hρ θ

/-- A point of `sphere ζ ρ`, in angular coordinates, lies on `sphere c r` exactly when its angle
satisfies the corresponding cosine equality. -/
theorem circleMap_mem_sphere_iff (hζ : dist ζ c = r) (hρ : 0 < ρ) (θ : ℝ) :
    circleMap ζ ρ θ ∈ sphere c r ↔
      ρ = 2 * r * Real.cos (θ - (c - ζ).arg) := by
  rw [mem_sphere, eq_iff_le_not_lt, dist_circleMap_le_iff hζ hρ,
    dist_circleMap_lt_iff hζ hρ, eq_iff_le_not_lt]

/-- The `simp`-normal form of `TauCeti.circleMap_mem_sphere_iff`. -/
@[simp]
theorem dist_circleMap_eq_iff (hζ : dist ζ c = r) (hρ : 0 < ρ) (θ : ℝ) :
    dist (circleMap ζ ρ θ) c = r ↔
      ρ = 2 * r * Real.cos (θ - (c - ζ).arg) :=
  circleMap_mem_sphere_iff hζ hρ θ

/-! ## The open and closed arcs -/

/-- A genuine circular crosscut is exactly one open angular arc. -/
theorem ball_inter_sphere_eq_circleMap_image_Ioo (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) :
    ball c r ∩ sphere ζ ρ =
      circleMap ζ ρ '' Ioo
        ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
        ((c - ζ).arg + Real.arccos (ρ / (2 * r))) := by
  have hr : 0 < r := by linarith
  have hx0 : 0 < ρ / (2 * r) := div_pos hρ (by positivity)
  ext z
  constructor
  · rintro ⟨hzball, hzsphere⟩
    obtain ⟨t, ht, rfl⟩ := exists_mem_Icc_circleMap_eq (c - ζ).arg hzsphere
    rw [circleMap_mem_ball_iff hζ hρ] at hzball
    have hcos : ρ / (2 * r) < Real.cos t := by
      rw [div_lt_iff₀ (by positivity)]
      simpa only [add_sub_cancel_left, mul_comm] using hzball
    have ht' := (Real.lt_cos_iff_mem_Ioo (by linarith) ht).mp hcos
    exact ⟨(c - ζ).arg + t, by constructor <;> linarith [ht'.1, ht'.2], rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨?_, circleMap_mem_sphere ζ hρ.le θ⟩
    rw [circleMap_mem_ball_iff hζ hρ]
    have ht : θ - (c - ζ).arg ∈ Icc (-π) π := by
      have hφπ2 := arccos_div_two_mul_lt_pi_div_two hρ hr
      constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
    have hcos := (Real.lt_cos_iff_mem_Ioo (by linarith) ht).mpr
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    simpa only [mul_comm] using ((div_lt_iff₀ (by positivity)).mp hcos)

/-- The closure-side companion of
`TauCeti.ball_inter_sphere_eq_circleMap_image_Ioo`: a genuine circular crosscut together with its
two endpoints is one closed angular arc. -/
theorem closedBall_inter_sphere_eq_circleMap_image_Icc (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) :
    closedBall c r ∩ sphere ζ ρ =
      circleMap ζ ρ '' Icc
        ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
        ((c - ζ).arg + Real.arccos (ρ / (2 * r))) := by
  have hr : 0 < r := by linarith
  have hx0 : 0 < ρ / (2 * r) := div_pos hρ (by positivity)
  have hx1 : ρ / (2 * r) < 1 := (div_lt_one (by positivity)).mpr hρr
  ext z
  constructor
  · rintro ⟨hzball, hzsphere⟩
    obtain ⟨t, ht, rfl⟩ := exists_mem_Icc_circleMap_eq (c - ζ).arg hzsphere
    rw [circleMap_mem_closedBall_iff hζ hρ] at hzball
    have hcos : ρ / (2 * r) ≤ Real.cos t := by
      rw [div_le_iff₀ (by positivity)]
      simpa only [add_sub_cancel_left, mul_comm] using hzball
    have ht' := (Real.le_cos_iff_mem_Icc hx1.le ht).mp hcos
    exact ⟨(c - ζ).arg + t, by constructor <;> linarith [ht'.1, ht'.2], rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨?_, circleMap_mem_sphere ζ hρ.le θ⟩
    rw [circleMap_mem_closedBall_iff hζ hρ]
    have ht : θ - (c - ζ).arg ∈ Icc (-π) π := by
      have hφπ2 := arccos_div_two_mul_lt_pi_div_two hρ hr
      constructor <;> linarith [hθ.1, hθ.2, Real.pi_pos]
    have hcos := (Real.le_cos_iff_mem_Icc hx1.le ht).mpr
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    simpa only [mul_comm] using ((div_le_iff₀ (by positivity)).mp hcos)

/-! ## The endpoints and topological packaging -/

/-- The two angular endpoints of a genuine circular crosscut are distinct. -/
theorem circleMap_crosscut_endpoints_ne (hρ : 0 < ρ) (hρr : ρ < 2 * r) (c ζ : ℂ) :
    circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r))) ≠
      circleMap ζ ρ ((c - ζ).arg + Real.arccos (ρ / (2 * r))) := by
  have hr : 0 < r := by linarith
  have hφ0 := arccos_div_two_mul_pos hr hρr
  have hφπ2 := arccos_div_two_mul_lt_pi_div_two hρ hr
  intro h
  have heq := eq_of_circleMap_eq hρ.ne'
    (by rw [abs_lt]; constructor <;> linarith [Real.pi_pos]) h
  linarith

/-- The two circles bounding a genuine circular crosscut meet at exactly its two angular
endpoints. -/
theorem sphere_inter_sphere_eq_pair_circleMap (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) :
    sphere c r ∩ sphere ζ ρ =
      {circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r))),
        circleMap ζ ρ ((c - ζ).arg + Real.arccos (ρ / (2 * r)))} := by
  have hr : 0 < r := by linarith
  let φ := Real.arccos (ρ / (2 * r))
  let p := circleMap ζ ρ ((c - ζ).arg - φ)
  let q := circleMap ζ ρ ((c - ζ).arg + φ)
  have hx0 : 0 < ρ / (2 * r) := div_pos hρ (by positivity)
  have hx1 : ρ / (2 * r) < 1 := (div_lt_one (by positivity)).mpr hρr
  have hcos : Real.cos φ = ρ / (2 * r) := Real.cos_arccos (by linarith) hx1.le
  have hpζ : p ∈ sphere ζ ρ := circleMap_mem_sphere ζ hρ.le _
  have hqζ : q ∈ sphere ζ ρ := circleMap_mem_sphere ζ hρ.le _
  have hpc : p ∈ sphere c r := by
    rw [circleMap_mem_sphere_iff hζ hρ]
    dsimp [p, φ]
    rw [sub_sub_cancel_left, Real.cos_neg, hcos]
    field_simp
  have hqc : q ∈ sphere c r := by
    rw [circleMap_mem_sphere_iff hζ hρ]
    dsimp [q, φ]
    rw [add_sub_cancel_left, hcos]
    field_simp
  have hpq : p ≠ q := circleMap_crosscut_endpoints_ne hρ hρr c ζ
  ext z
  constructor
  · rintro ⟨hzc, hzζ⟩
    have hne : c ≠ ζ := by
      intro h
      rw [h, dist_self] at hζ
      linarith
    have hz := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
      (P := ℂ) (V := ℂ) (by norm_num) hne hpq hpc hqc hzc hpζ hqζ hzζ
    simpa only [mem_insert_iff, mem_singleton_iff] using hz
  · simp only [mem_insert_iff, mem_singleton_iff]
    rintro (rfl | rfl)
    · exact ⟨hpc, hpζ⟩
    · exact ⟨hqc, hqζ⟩

/-- A genuine circular crosscut is path connected: it is the image of an open real interval under
the continuous circle parametrization. -/
theorem isPathConnected_ball_inter_sphere (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) : IsPathConnected (ball c r ∩ sphere ζ ρ) := by
  rw [ball_inter_sphere_eq_circleMap_image_Ioo hζ hρ hρr]
  have hne : (Ioo ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
      ((c - ζ).arg + Real.arccos (ρ / (2 * r)))).Nonempty := by
    rw [nonempty_Ioo]
    linarith [arccos_div_two_mul_pos (show (0 : ℝ) < r by linarith) hρr]
  exact ((convex_Ioo _ _).isPathConnected hne).image (continuous_circleMap ζ ρ)

/-- A genuine circular crosscut together with its endpoints is path connected. -/
theorem isPathConnected_closedBall_inter_sphere (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) : IsPathConnected (closedBall c r ∩ sphere ζ ρ) := by
  rw [closedBall_inter_sphere_eq_circleMap_image_Icc hζ hρ hρr]
  exact ((convex_Icc _ _).isPathConnected (nonempty_Icc.2 (by
    linarith [arccos_div_two_mul_pos (show (0 : ℝ) < r by linarith) hρr]))).image
    (continuous_circleMap ζ ρ)

/-- Closing a genuine open circular crosscut adds exactly its two endpoints. -/
theorem closure_ball_inter_sphere (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r) :
    closure (ball c r ∩ sphere ζ ρ) = closedBall c r ∩ sphere ζ ρ := by
  rw [ball_inter_sphere_eq_circleMap_image_Ioo hζ hρ hρr,
    closedBall_inter_sphere_eq_circleMap_image_Icc hζ hρ hρr]
  have hφ0 := arccos_div_two_mul_pos (show (0 : ℝ) < r by linarith) hρr
  let a := (c - ζ).arg - Real.arccos (ρ / (2 * r))
  let b := (c - ζ).arg + Real.arccos (ρ / (2 * r))
  have hab : a < b := by dsimp [a, b]; linarith
  apply le_antisymm
  · exact closure_minimal (image_mono Ioo_subset_Icc_self)
      (isCompact_Icc.image (continuous_circleMap ζ ρ)).isClosed
  · rintro z ⟨θ, hθ, rfl⟩
    exact mem_closure_image (continuous_circleMap ζ ρ).continuousAt
      (by rwa [closure_Ioo hab.ne])

/-- **A circular crosscut of a disc reaches the boundary of the disc.** A crosscut spanning less
than a half turn has two endpoints (`TauCeti.sphere_inter_sphere_eq_pair_circleMap`), and either of
them lies on `sphere c r`, the frontier of the disc, and in the closure of the crosscut
(`TauCeti.closure_ball_inter_sphere`).

This is the form in which `Conformal/Crosscut/Image.lean`, whose statements are about an arbitrary
domain, asks a cut to leave the domain at all. -/
theorem nonempty_frontier_ball_inter_closure_ball_inter_sphere (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) :
    (frontier (ball c r) ∩ closure (ball c r ∩ sphere ζ ρ)).Nonempty := by
  have hr : 0 < r := by linarith
  have hmem : circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
      ∈ sphere c r ∩ sphere ζ ρ := by
    rw [sphere_inter_sphere_eq_pair_circleMap hζ hρ hρr]
    exact Or.inl rfl
  refine ⟨circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r))), ?_, ?_⟩
  · rw [frontier_ball c hr.ne']
    exact hmem.1
  · rw [closure_ball_inter_sphere hζ hρ hρr]
    exact ⟨sphere_subset_closedBall hmem.1, hmem.2⟩

/-- **A ball centred at a point of the closed crosscut meets the crosscut in a subarc.** A genuine
circular crosscut spans an angle `2 * arccos (ρ / (2 * r)) < π`, so along it the chord distance to
a fixed one of its points is unimodal; the part of the crosscut inside any ball centred at such a
point is therefore the image of an interval of angles, and in particular preconnected.

This is the local connectedness of a crosscut *at its own endpoints*, which is what the cluster set
of a map along a crosscut needs in order to be a continuum
(`TauCeti.isConnected_clusterSetOn`). The radius `δ` is arbitrary: for large `δ` the trace is the
whole crosscut. -/
theorem isPreconnected_ball_inter_sphere_inter_ball (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) {e : ℂ} (he : e ∈ closedBall c r ∩ sphere ζ ρ) (δ : ℝ) :
    IsPreconnected (ball c r ∩ sphere ζ ρ ∩ ball e δ) := by
  have hφπ2 := arccos_div_two_mul_lt_pi_div_two hρ (show (0 : ℝ) < r by linarith)
  obtain ⟨θ₀, hθ₀, rfl⟩ := (closedBall_inter_sphere_eq_circleMap_image_Icc hζ hρ hρr).le he
  rw [ball_inter_sphere_eq_circleMap_image_Ioo hζ hρ hρr, ← image_inter_preimage]
  refine IsPreconnected.image ?_ _ (continuous_circleMap ζ ρ).continuousOn
  have hpre : circleMap ζ ρ ⁻¹' ball (circleMap ζ ρ θ₀) δ
      = {θ | dist (circleMap ζ ρ θ) (circleMap ζ ρ θ₀) < δ} := by
    ext θ
    simp [Metric.mem_ball]
  rw [hpre]
  refine (ordConnected_inter_setOf_dist_circleMap_lt ζ ρ ordConnected_Ioo ?_).isPreconnected
  rintro u ⟨hu1, hu2⟩
  exact ⟨by linarith [hθ₀.2], by linarith [hθ₀.1]⟩

end TauCeti
