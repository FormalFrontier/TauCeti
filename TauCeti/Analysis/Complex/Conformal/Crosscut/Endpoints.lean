/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Crosscut.Basic
import Mathlib.Geometry.Euclidean.Basic

/-!
# The endpoints of a circular crosscut

For a point `ζ` on `sphere c r` and a radius `ρ` with `0 < ρ < 2 * r`, the circle
`sphere ζ ρ` cuts the disc `ball c r` in one open arc. This file identifies that arc, its closed
companion, and its two endpoints exactly. If

* `α = arg (c - ζ)` is the direction from `ζ` to the centre, and
* `φ = arccos (ρ / (2 * r))` is the half-angle of the crosscut,

then the open and closed arcs are the images under `circleMap ζ ρ` of `(α - φ, α + φ)` and
`[α - φ, α + φ]`, while the two bounding circles meet at the images of the endpoints.

This is the source-side endpoint interface needed by layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`, the Jordan-domain case of Carathéodory boundary
correspondence. `Conformal/ShortCrosscut.lean` makes the image of the *open* arc arbitrarily short,
and `Conformal/CutDiameter.lean` asks local connectedness of the image boundary to join the two
ends by a small boundary set. The results here name those two ends and package the open arc together
with its closure; they do not assert the continuous boundary extension itself.

## Main results

* `TauCeti.ball_inter_sphere_eq_circleMap_image_Ioo` and
  `TauCeti.closedBall_inter_sphere_eq_circleMap_image_Icc` identify the open and closed crosscut
  arcs.
* `TauCeti.sphere_inter_sphere_eq_pair_circleMap` identifies their two distinct endpoints.
* `TauCeti.isPathConnected_ball_inter_sphere` and
  `TauCeti.closure_ball_inter_sphere` give the corresponding topological packaging.

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

/-! ## Metric and angular descriptions -/

/-- The squared distance from a point on `sphere ζ ρ` to `c`, in angular coordinates based at the
direction from `ζ` to `c`. This is the cosine rule in the form underlying circular crosscuts. -/
private theorem dist_circleMap_sq (hζ : dist ζ c = r) (hρ : 0 < ρ) (θ : ℝ) :
    dist (circleMap ζ ρ θ) c ^ 2 =
      ρ ^ 2 + r ^ 2 - 2 * ρ * r * Real.cos (θ - (c - ζ).arg) := by
  have hnorm : ‖c - ζ‖ = r := by rw [← dist_eq_norm, dist_comm, hζ]
  have hpolar : c - ζ = (r : ℂ) * exp (((c - ζ).arg : ℂ) * I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (c - ζ)]
    rw [hnorm]
  have hsub : circleMap ζ ρ θ - c =
      (ρ : ℂ) * exp ((θ : ℂ) * I) - (c - ζ) := by
    simp only [circleMap]
    ring
  have hu : normSq ((ρ : ℂ) * exp ((θ : ℂ) * I)) = ρ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      norm_real, Real.norm_of_nonneg hρ.le]
  have ha : normSq (c - ζ) = r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, hnorm]
  have hare : (c - ζ).re = r * Real.cos (c - ζ).arg := by
    calc
      (c - ζ).re = ((r : ℂ) * exp (((c - ζ).arg : ℂ) * I)).re :=
        congrArg Complex.re hpolar
      _ = r * Real.cos (c - ζ).arg := by simp [Complex.mul_re]
  have haim : (c - ζ).im = r * Real.sin (c - ζ).arg := by
    calc
      (c - ζ).im = ((r : ℂ) * exp (((c - ζ).arg : ℂ) * I)).im :=
        congrArg Complex.im hpolar
      _ = r * Real.sin (c - ζ).arg := by simp [Complex.mul_im]
  have hcross :
      (((ρ : ℂ) * exp ((θ : ℂ) * I)) * (starRingEnd ℂ) (c - ζ)).re =
        ρ * r * Real.cos (θ - (c - ζ).arg) := by
    calc
      (((ρ : ℂ) * exp ((θ : ℂ) * I)) * (starRingEnd ℂ) (c - ζ)).re =
          (ρ * Real.cos θ) * (c - ζ).re + (ρ * Real.sin θ) * (c - ζ).im := by
            simp [Complex.mul_re, Complex.mul_im]
            ring
      _ = ρ * r * Real.cos (θ - (c - ζ).arg) := by
        rw [hare, haim, Real.cos_sub]
        ring
  rw [dist_eq_norm, ← Complex.normSq_eq_norm_sq, hsub, Complex.normSq_sub, hu, ha, hcross]
  ring

/-- A point of `sphere ζ ρ`, in angular coordinates, lies in `closedBall c r` exactly when its
angle satisfies the weak cosine inequality complementary to
`TauCeti.circleMap_mem_ball_iff`. -/
theorem circleMap_mem_closedBall_iff (hζ : dist ζ c = r) (hρ : 0 < ρ) (θ : ℝ) :
    circleMap ζ ρ θ ∈ closedBall c r ↔
      ρ ≤ 2 * r * Real.cos (θ - (c - ζ).arg) := by
  rw [mem_closedBall]
  have hr : 0 ≤ r := hζ ▸ dist_nonneg
  have hd := dist_circleMap_sq hζ hρ θ
  constructor
  · intro h
    have hsq : dist (circleMap ζ ρ θ) c ^ 2 ≤ r ^ 2 := by
      nlinarith [dist_nonneg (x := circleMap ζ ρ θ) (y := c)]
    have hprod : ρ * (ρ - 2 * r * Real.cos (θ - (c - ζ).arg)) ≤ 0 := by
      nlinarith
    apply le_of_sub_nonpos
    by_contra hnot
    exact (not_lt_of_ge hprod) (mul_pos hρ (lt_of_not_ge hnot))
  · intro h
    have hprod : ρ * (ρ - 2 * r * Real.cos (θ - (c - ζ).arg)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hρ.le (sub_nonpos.mpr h)
    nlinarith [dist_nonneg (x := circleMap ζ ρ θ) (y := c)]

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
  rw [mem_sphere]
  have hr : 0 ≤ r := hζ ▸ dist_nonneg
  have hd := dist_circleMap_sq hζ hρ θ
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith [dist_nonneg (x := circleMap ζ ρ θ) (y := c)]

/-- The `simp`-normal form of `TauCeti.circleMap_mem_sphere_iff`. -/
@[simp]
theorem dist_circleMap_eq_iff (hζ : dist ζ c = r) (hρ : 0 < ρ) (θ : ℝ) :
    dist (circleMap ζ ρ θ) c = r ↔
      ρ = 2 * r * Real.cos (θ - (c - ζ).arg) :=
  circleMap_mem_sphere_iff hζ hρ θ

/-! ## The open and closed arcs -/

/-- On the principal period, comparison with the cosine of an arccosine is equivalent to lying
strictly between the two symmetric angles. -/
private theorem div_lt_cos_iff_mem_Ioo {x t : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (ht : t ∈ Icc (-π) π) :
    x < Real.cos t ↔ t ∈ Ioo (-Real.arccos x) (Real.arccos x) := by
  have hφ0 : 0 < Real.arccos x := Real.arccos_pos.mpr hx1
  have hφπ : Real.arccos x < π := Real.arccos_lt_pi.mpr (by linarith)
  have hat : |t| ∈ Icc (0 : ℝ) π := ⟨abs_nonneg _, (abs_le.mpr ht).trans' le_rfl⟩
  have hφ : Real.arccos x ∈ Icc (0 : ℝ) π := ⟨hφ0.le, hφπ.le⟩
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos (by linarith) hx1.le
  constructor
  · intro h
    have h' : Real.cos (Real.arccos x) < Real.cos |t| := by simpa [hcos, Real.cos_abs] using h
    exact abs_lt.mp ((Real.strictAntiOn_cos.lt_iff_gt hφ hat).mp h')
  · intro h
    have h' := (Real.strictAntiOn_cos.lt_iff_gt hφ hat).mpr (abs_lt.mpr h)
    simpa [hcos, Real.cos_abs] using h'

/-- The weak companion of `div_lt_cos_iff_mem_Ioo`. -/
private theorem div_le_cos_iff_mem_Icc {x t : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (ht : t ∈ Icc (-π) π) :
    x ≤ Real.cos t ↔ t ∈ Icc (-Real.arccos x) (Real.arccos x) := by
  have hφ0 : 0 < Real.arccos x := Real.arccos_pos.mpr hx1
  have hφπ : Real.arccos x < π := Real.arccos_lt_pi.mpr (by linarith)
  have hat : |t| ∈ Icc (0 : ℝ) π := ⟨abs_nonneg _, (abs_le.mpr ht).trans' le_rfl⟩
  have hφ : Real.arccos x ∈ Icc (0 : ℝ) π := ⟨hφ0.le, hφπ.le⟩
  have hcos : Real.cos (Real.arccos x) = x := Real.cos_arccos (by linarith) hx1.le
  constructor
  · intro h
    have h' : Real.cos (Real.arccos x) ≤ Real.cos |t| := by simpa [hcos, Real.cos_abs] using h
    exact abs_le.mp ((Real.strictAntiOn_cos.le_iff_ge hφ hat).mp h')
  · intro h
    have h' := (Real.strictAntiOn_cos.le_iff_ge hφ hat).mpr (abs_le.mpr h)
    simpa [hcos, Real.cos_abs] using h'

/-- Every point of a positive-radius circle has an angular representative in the period of length
`2 * π` centred at any prescribed angle. -/
theorem exists_mem_Icc_circleMap_eq (α : ℝ) (hρ : 0 < ρ) {z : ℂ}
    (hz : z ∈ sphere ζ ρ) :
    ∃ t ∈ Icc (-π) π, circleMap ζ ρ (α + t) = z := by
  have hmem : z ∈ circleMap ζ ρ '' Icc (α - π) (α - π + 2 * π) := by
    rw [(periodic_circleMap ζ ρ).image_Icc Real.two_pi_pos, range_circleMap, abs_of_pos hρ]
    exact hz
  obtain ⟨θ, hθ, rfl⟩ := hmem
  refine ⟨θ - α, ?_, by congr 1; ring⟩
  constructor
  · linarith [hθ.1]
  · linarith [hθ.2]

/-- A genuine circular crosscut is exactly one open angular arc. -/
theorem ball_inter_sphere_eq_circleMap_image_Ioo (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) :
    ball c r ∩ sphere ζ ρ =
      circleMap ζ ρ '' Ioo
        ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
        ((c - ζ).arg + Real.arccos (ρ / (2 * r))) := by
  have hr : 0 < r := by linarith
  have hx0 : 0 < ρ / (2 * r) := div_pos hρ (by positivity)
  have hx1 : ρ / (2 * r) < 1 := (div_lt_one (by positivity)).mpr hρr
  ext z
  constructor
  · rintro ⟨hzball, hzsphere⟩
    obtain ⟨t, ht, rfl⟩ := exists_mem_Icc_circleMap_eq (c - ζ).arg hρ hzsphere
    rw [circleMap_mem_ball_iff hζ hρ] at hzball
    have hcos : ρ / (2 * r) < Real.cos t := by
      rw [div_lt_iff₀ (by positivity)]
      simpa only [add_sub_cancel_left, mul_comm] using hzball
    have ht' := (div_lt_cos_iff_mem_Ioo hx0 hx1 ht).mp hcos
    exact ⟨(c - ζ).arg + t, by constructor <;> linarith [ht'.1, ht'.2], rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨?_, circleMap_mem_sphere ζ hρ.le θ⟩
    rw [circleMap_mem_ball_iff hζ hρ]
    have ht : θ - (c - ζ).arg ∈ Icc (-π) π := by
      have hφπ := Real.arccos_lt_pi.mpr (by linarith : -1 < ρ / (2 * r))
      constructor <;> linarith [hθ.1, hθ.2]
    have hcos := (div_lt_cos_iff_mem_Ioo hx0 hx1 ht).mpr
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
    obtain ⟨t, ht, rfl⟩ := exists_mem_Icc_circleMap_eq (c - ζ).arg hρ hzsphere
    rw [circleMap_mem_closedBall_iff hζ hρ] at hzball
    have hcos : ρ / (2 * r) ≤ Real.cos t := by
      rw [div_le_iff₀ (by positivity)]
      simpa only [add_sub_cancel_left, mul_comm] using hzball
    have ht' := (div_le_cos_iff_mem_Icc hx0 hx1 ht).mp hcos
    exact ⟨(c - ζ).arg + t, by constructor <;> linarith [ht'.1, ht'.2], rfl⟩
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨?_, circleMap_mem_sphere ζ hρ.le θ⟩
    rw [circleMap_mem_closedBall_iff hζ hρ]
    have ht : θ - (c - ζ).arg ∈ Icc (-π) π := by
      have hφπ := Real.arccos_lt_pi.mpr (by linarith : -1 < ρ / (2 * r))
      constructor <;> linarith [hθ.1, hθ.2]
    have hcos := (div_le_cos_iff_mem_Icc hx0 hx1 ht).mpr
      ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    simpa only [mul_comm] using ((div_le_iff₀ (by positivity)).mp hcos)

/-! ## The endpoints and topological packaging -/

/-- The two angular endpoints of a genuine circular crosscut are distinct. -/
theorem circleMap_crosscut_endpoints_ne (hρ : 0 < ρ) (hρr : ρ < 2 * r) (c ζ : ℂ) :
    circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r))) ≠
      circleMap ζ ρ ((c - ζ).arg + Real.arccos (ρ / (2 * r))) := by
  have hr : 0 < r := by linarith
  have hφ0 : 0 < Real.arccos (ρ / (2 * r)) :=
    Real.arccos_pos.mpr ((div_lt_one (by positivity)).mpr hρr)
  have hφπ : Real.arccos (ρ / (2 * r)) < π :=
    Real.arccos_lt_pi.mpr (by
      have hx : 0 < ρ / (2 * r) := div_pos hρ (by positivity)
      linarith)
  intro h
  have heq := eq_of_circleMap_eq hρ.ne' (by rw [abs_lt]; constructor <;> linarith) h
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
    have hr : 0 < r := by linarith
    have hφ := Real.arccos_pos.mpr ((div_lt_one (by positivity)).mpr hρr)
    linarith
  exact ((convex_Ioo _ _).isPathConnected hne).image (continuous_circleMap ζ ρ)

/-- A genuine circular crosscut together with its endpoints is path connected. -/
theorem isPathConnected_closedBall_inter_sphere (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρr : ρ < 2 * r) : IsPathConnected (closedBall c r ∩ sphere ζ ρ) := by
  rw [closedBall_inter_sphere_eq_circleMap_image_Icc hζ hρ hρr]
  exact ((convex_Icc _ _).isPathConnected (nonempty_Icc.2 (by
    have hr : 0 < r := by linarith
    have hφ := Real.arccos_pos.mpr ((div_lt_one (by positivity)).mpr hρr)
    linarith))).image (continuous_circleMap ζ ρ)

/-- Closing a genuine open circular crosscut adds exactly its two endpoints. -/
theorem closure_ball_inter_sphere (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r) :
    closure (ball c r ∩ sphere ζ ρ) = closedBall c r ∩ sphere ζ ρ := by
  rw [ball_inter_sphere_eq_circleMap_image_Ioo hζ hρ hρr,
    closedBall_inter_sphere_eq_circleMap_image_Icc hζ hρ hρr]
  have hφ0 : 0 < Real.arccos (ρ / (2 * r)) := by
    have hr : 0 < r := by linarith
    exact Real.arccos_pos.mpr ((div_lt_one (by positivity)).mpr hρr)
  let a := (c - ζ).arg - Real.arccos (ρ / (2 * r))
  let b := (c - ζ).arg + Real.arccos (ρ / (2 * r))
  have hab : a < b := by dsimp [a, b]; linarith
  apply le_antisymm
  · exact closure_minimal (image_mono Ioo_subset_Icc_self)
      (isCompact_Icc.image (continuous_circleMap ζ ρ)).isClosed
  · rintro z ⟨θ, hθ, rfl⟩
    exact mem_closure_image (continuous_circleMap ζ ρ).continuousAt
      (by rwa [closure_Ioo hab.ne])

end TauCeti
