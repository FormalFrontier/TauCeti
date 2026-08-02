/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The chord and the arc on the unit circle

Mathlib's `Circle` carries both a metric, from the inclusion into `ℂ`, and an arc-length API:
`Circle.exp` parametrizes it by angles and `Circle.angleDiff x y` is the length of the arc running
counterclockwise from `x` to `y`. This file relates the two, comparing the *chord* `dist x y` with
the *arc* separating `x` from `y` in both directions.

## Main results

* `TauCeti.dist_circleExp_eq_two_mul_abs_sin` — the chord subtended by an arc of angle `θ` of the
  unit circle has length `2 * |sin (θ / 2)|`.
* `TauCeti.lipschitzWith_one_circleExp` and `TauCeti.diam_circleExp_image_Icc_le` — the chord is at
  most the arc, so an arc of angles of length `b - a` has image of diameter at most `b - a`.
* `TauCeti.min_angleDiff_le_dist` — the shorter of the two arcs joining two points of the circle has
  length at most `π / 2` times their distance.

## The argument

The first two are Mathlib's estimates for the normalized chord `‖exp (I * θ) - 1‖`, read off the
factorization `exp a - exp b = (exp (a - b) - 1) * exp b`: the chord formula is
`Complex.norm_exp_I_mul_ofReal_sub_one` and the Lipschitz bound is
`Real.norm_exp_I_mul_ofReal_sub_one_le`, so neither is derived from the other. The converse
comparison `TauCeti.min_angleDiff_le_dist` is Jordan's inequality `Real.mul_le_sin` applied to the
chord formula; it is the direction that turns a hypothesis about the ambient metric into a bound on
an arc, and so the one a transport argument such as
`TauCeti/Topology/JordanCurve/SmallArc.lean` consumes.
-/

public section

namespace TauCeti

open Metric Set

open scoped Real

/-- The chord of the circle between the angles `a` and `b`, normalized: factoring the unimodular
`Circle.exp b` out of the difference reduces it to the chord from angle `a - b` to angle `0`, which
is the quantity Mathlib's `Complex.norm_exp_I_mul_ofReal_sub_one` and
`Real.norm_exp_I_mul_ofReal_sub_one_le` describe. Both the chord formula
`TauCeti.dist_circleExp_eq_two_mul_abs_sin` and the Lipschitz bound
`TauCeti.lipschitzWith_one_circleExp` are those two Mathlib facts read through this identity, so
neither is derived from the other. -/
private lemma dist_circleExp_eq_norm_exp_sub_one (a b : ℝ) :
    dist (Circle.exp a) (Circle.exp b) = ‖Complex.exp (Complex.I * (a - b : ℝ)) - 1‖ := by
  have hsplit : Circle.exp a = Circle.exp (a - b) * Circle.exp b := by
    rw [← Circle.exp_add]
    ring_nf
  have hfactor : ((Circle.exp a : ℂ) - (Circle.exp b : ℂ)) =
      ((Circle.exp (a - b) : ℂ) - 1) * (Circle.exp b : ℂ) := by
    rw [hsplit, Circle.coe_mul]
    ring
  have hdist : dist (Circle.exp a) (Circle.exp b)
      = ‖(Circle.exp a : ℂ) - (Circle.exp b : ℂ)‖ := by
    rw [← Complex.dist_eq]
    exact Subtype.dist_eq _ _
  rw [hdist, hfactor, norm_mul, Circle.norm_coe, mul_one, Circle.coe_exp,
    mul_comm ((a - b : ℝ) : ℂ) Complex.I]

/-- **The chord formula for the unit circle**: two points of the circle at angles `a` and `b` are at
distance `2 * |sin ((a - b) / 2)|`.

This is Mathlib's `Complex.norm_exp_I_mul_ofReal_sub_one` at the angle `a - b`, read through the
normalized chord `TauCeti.dist_circleExp_eq_norm_exp_sub_one`. -/
theorem dist_circleExp_eq_two_mul_abs_sin (a b : ℝ) :
    dist (Circle.exp a) (Circle.exp b) = 2 * |Real.sin ((a - b) / 2)| := by
  rw [dist_circleExp_eq_norm_exp_sub_one, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_mul]
  norm_num

/-- **The chord is at most the arc**: `Circle.exp` is `1`-Lipschitz. This is Mathlib's
`Real.norm_exp_I_mul_ofReal_sub_one_le` read through the normalized chord
`TauCeti.dist_circleExp_eq_norm_exp_sub_one`. -/
theorem lipschitzWith_one_circleExp : LipschitzWith 1 Circle.exp :=
  LipschitzWith.mk_one fun a b => by
    rw [Real.dist_eq, dist_circleExp_eq_norm_exp_sub_one, ← Real.norm_eq_abs]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- An arc of the circle spanning the angles `Set.Icc a b` has diameter at most `b - a`: the
`1`-Lipschitz map `TauCeti.lipschitzWith_one_circleExp` does not increase the diameter
`Real.diam_Icc` of the interval of angles. -/
theorem diam_circleExp_image_Icc_le {a b : ℝ} (hab : a ≤ b) :
    Metric.diam (Circle.exp '' Icc a b) ≤ b - a := by
  simpa only [NNReal.coe_one, one_mul, Real.diam_Icc hab] using
    lipschitzWith_one_circleExp.diam_image_le (Icc a b) (isBounded_Icc a b)

/-- **The shorter arc is controlled by the chord**: of the two arcs joining `x` to `y` on the
circle, the shorter has length at most `π / 2` times the distance from `x` to `y`.

This is the direction of the comparison that converts a hypothesis about the ambient metric into a
bound on an arc, and it is where Jordan's inequality `Real.mul_le_sin` enters: writing `t` for
`Circle.angleDiff x y`, the chord formula gives `dist x y = 2 * sin (t / 2)`, and `sin (t / 2)` is
unchanged when `t` is replaced by `2 * π - t`, so it may be computed from whichever of the two arc
lengths is at most `π`. -/
theorem min_angleDiff_le_dist (x y : Circle) :
    min (Circle.angleDiff x y) (Circle.angleDiff y x) ≤ π / 2 * dist x y := by
  rcases eq_or_ne x y with rfl | hxy
  · simp [Circle.angleDiff]
  have hpos : 0 < Circle.angleDiff x y := Circle.angleDiff_pos hxy
  have hlt : Circle.angleDiff x y < 2 * π := Circle.angleDiff_lt_two_pi x y
  have hsum : Circle.angleDiff x y + Circle.angleDiff y x = 2 * π :=
    Circle.angleDiff_add_angleDiff hxy
  -- The chord formula, read off from `y = exp (angleDiff x y + arg x)`.
  have hy : Circle.exp (Circle.angleDiff x y + Complex.arg (x : ℂ)) = y := by
    rw [Circle.exp_add, Circle.exp_arg, Circle.exp_angleDiff_mul]
  have hπ : 0 < π := Real.pi_pos
  have hdist : dist x y = 2 * Real.sin (Circle.angleDiff x y / 2) := by
    have hrw : dist x y = dist (Circle.exp (Complex.arg (x : ℂ)))
        (Circle.exp (Circle.angleDiff x y + Complex.arg (x : ℂ))) := by
      rw [Circle.exp_arg, hy]
    have hangle : (Complex.arg (x : ℂ) - (Circle.angleDiff x y + Complex.arg (x : ℂ))) / 2
        = -(Circle.angleDiff x y / 2) := by ring
    rw [hrw, dist_circleExp_eq_two_mul_abs_sin, hangle, Real.sin_neg, abs_neg,
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]
  -- Jordan's inequality applied to the half of the shorter arc.
  have key : ∀ s : ℝ, 0 < s → s ≤ π → Real.sin (s / 2) = Real.sin (Circle.angleDiff x y / 2) →
      s ≤ π / 2 * dist x y := by
    intro s hs₀ hs₁ hs
    have hjordan : 2 / π * (s / 2) ≤ Real.sin (s / 2) :=
      Real.mul_le_sin (by linarith) (by linarith)
    have hmul : s ≤ π * Real.sin (s / 2) := by
      calc s = π * (2 / π * (s / 2)) := by field_simp
        _ ≤ π * Real.sin (s / 2) := by nlinarith
    have hhalf : π / 2 * (2 * Real.sin (s / 2)) = π * Real.sin (s / 2) := by ring
    rw [hdist, ← hs, hhalf]
    exact hmul
  rcases le_total (Circle.angleDiff x y) π with hle | hle
  · exact (min_le_left _ _).trans (key _ hpos hle rfl)
  · refine (min_le_right _ _).trans (key _ (by linarith) (by linarith) ?_)
    have hrefl : Circle.angleDiff y x / 2 = π - Circle.angleDiff x y / 2 := by linarith
    rw [hrefl, Real.sin_pi_sub]

end TauCeti
