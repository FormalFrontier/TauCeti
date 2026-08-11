/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arccos

/-!
# The chord and the arc on a circle

Mathlib's `Circle` carries both a metric, from the inclusion into `ℂ`, and an arc-length API:
`Circle.exp` parametrizes it by angles and `Circle.angleDiff x y` is the length of the arc running
counterclockwise from `x` to `y`. This file relates the two, comparing the *chord* `dist x y` with
the *arc* separating `x` from `y` in both directions, and transports the chord formula along the
translation and real scaling that carry `Circle.exp` to Mathlib's `circleMap ζ ρ`. It also records
the chord with one endpoint allowed *off* the circle — the distance from a point of `circleMap ζ ρ`
to an arbitrary point of the plane, which is the law of cosines — and reads off from that law when
such a point lies in a disc `ball c r`, whose centre `c` is unrelated to the centre `ζ` of the
circle.

## Main results

* `TauCeti.exp_mul_I_sub_exp_mul_I` — the polar form of the chord: the half-angle sine rotated a
  quarter turn past the midpoint direction.
* `TauCeti.dist_circleExp_eq_two_mul_abs_sin` — the chord subtended by an arc of angle `θ` of the
  unit circle has length `2 * |sin (θ / 2)|`.
* `TauCeti.dist_circleMap_eq_two_mul_abs_sin` — its form for the circle `circleMap ζ ρ` of arbitrary
  centre and radius, where the chord between the angles `θ` and `θ'` has length
  `2 * |ρ| * |sin ((θ - θ') / 2)|`, and
  `TauCeti.dist_circleMap_eq_two_mul_sin_abs`, the same formula with the sign of the angular
  difference cleared, valid for angles at most a full turn apart.
* `TauCeti.dist_circleMap_le_dist_circleMap_of_abs_sub_le` — within half a turn that chord grows
  with the angular gap, so the distance to a fixed point of the circle is unimodal along it, and
  `TauCeti.ordConnected_inter_setOf_dist_circleMap_lt` — consequently a ball meets an arc of
  angular width at most `π` in a set of angles that is order connected.
* `TauCeti.exists_mem_Ioo_circleMap_eq_and_abs_sub_lt_of_mem_ball_circleMap_image_Ioo` — the
  inverse comparison on an arc that does not wrap: a point of the arc close enough to a fixed
  point of it is the image of a
  nearby angle, so closeness in the plane is closeness in angle.
* `TauCeti.dist_circleMap_sq` — the law of cosines: the point of `circleMap ζ ρ` at angle `θ` is at
  distance `ρ ^ 2 + dist ζ c ^ 2 - 2 * ρ * dist ζ c * cos (θ - arg (c - ζ))`, squared, from an
  arbitrary point `c` of the plane.
* `TauCeti.circleMap_mem_ball_iff_sq` and `TauCeti.circleMap_mem_closedBall_iff_sq` — that law
  compared with `r ^ 2`: when the point at angle `θ` lies in the disc `ball c r`, respectively in
  `closedBall c r`.
* `TauCeti.circleMap_mem_ball_of_mem_Icc` — since the criterion sees the angle only through
  `cos (θ - arg (c - ζ))`, the angles it admits form an arc: it holds throughout an interval of
  angles inside a period centred at `arg (c - ζ)` as soon as it holds at both ends.
* `TauCeti.lipschitzWith_one_circleExp` and `TauCeti.diam_circleExp_image_Icc_le` — the chord is at
  most the arc, so an arc of angles of length `b - a` has image of diameter at most `b - a`, and
  `TauCeti.diam_range_circlePath_le` — the same bound for Mathlib's arc `Circle.path x y`, whose
  angle is `Circle.angleDiff x y`.
* `TauCeti.min_angleDiff_le_pi_div_two_mul_dist` — the shorter of the two arcs joining two points of
  the circle has length at most `π / 2` times their distance.

## The argument

The first two are Mathlib's estimates for the normalized chord `‖exp (I * θ) - 1‖`, read off the
factorization `exp a - exp b = (exp (a - b) - 1) * exp b`: the chord formula is
`Complex.norm_exp_I_mul_ofReal_sub_one` and the Lipschitz bound is
`Real.norm_exp_I_mul_ofReal_sub_one_le`, so neither is derived from the other. The converse
comparison `TauCeti.min_angleDiff_le_pi_div_two_mul_dist` is Jordan's inequality `Real.mul_le_sin`
applied to the chord formula; it is the direction that turns a hypothesis about the ambient metric
into a bound on an arc, and so the one a transport argument such as
`TauCeti/Topology/JordanCurve/SmallArc.lean` consumes.
-/

public section

namespace TauCeti

open Metric Set

open scoped Real

/-- The chord of the circle between the angles `a` and `b`, normalized to the chord from angle
`a - b` to angle `0`, which is the quantity Mathlib's `Complex.norm_exp_I_mul_ofReal_sub_one` and
`Real.norm_exp_I_mul_ofReal_sub_one_le` describe. -/
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

/-- **The polar chord identity on the unit circle**: the difference of two unit-circle
points is the half-angle sine, rotated a quarter turn past the midpoint direction. -/
theorem exp_mul_I_sub_exp_mul_I (α β : ℝ) :
    Complex.exp (α * Complex.I) - Complex.exp (β * Complex.I) =
      2 * (Real.sin ((α - β) / 2) : ℂ) * Complex.I *
        Complex.exp ((((α + β) / 2 : ℝ) : ℂ) * Complex.I) := by
  have hsin : Complex.exp ((((α - β) / 2 : ℝ) : ℂ) * Complex.I) -
      Complex.exp (-(((α - β) / 2 : ℝ) : ℂ) * Complex.I) =
      2 * Complex.sin (((α - β) / 2 : ℝ) : ℂ) * Complex.I := by
    have h2 := Complex.two_sin ((((α - β) / 2 : ℝ) : ℂ))
    linear_combination (-Complex.I) * h2 +
      (Complex.exp ((((α - β) / 2 : ℝ) : ℂ) * Complex.I) -
        Complex.exp (-(((α - β) / 2 : ℝ) : ℂ) * Complex.I)) * Complex.I_sq
  have h1 : (α : ℂ) * Complex.I =
      ((α + β) / 2 : ℝ) * Complex.I + (((α - β) / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have h2 : (β : ℂ) * Complex.I =
      ((α + β) / 2 : ℝ) * Complex.I + -(((α - β) / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h1, h2, Complex.exp_add, Complex.exp_add, ← mul_sub, hsin, ← Complex.ofReal_sin]
  ring

/-- **The chord formula for the unit circle**: two points of the circle at angles `a` and `b` are at
distance `2 * |sin ((a - b) / 2)|`. -/
theorem dist_circleExp_eq_two_mul_abs_sin (a b : ℝ) :
    dist (Circle.exp a) (Circle.exp b) = 2 * |Real.sin ((a - b) / 2)| := by
  rw [dist_circleExp_eq_norm_exp_sub_one, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_mul]
  norm_num

/-- **The chord of a circle of arbitrary centre and radius.** The two points of `circleMap ζ ρ` at
angles `θ` and `θ'` are at distance `2 * |ρ| * |sin ((θ - θ') / 2)|`; nothing is assumed of the
radius, a negative `ρ` tracing the same circle in the other sense.

This is the unit-circle formula `TauCeti.dist_circleExp_eq_two_mul_abs_sin` transported along the
translation and real scaling that carry `Circle.exp` to `circleMap ζ ρ`. -/
theorem dist_circleMap_eq_two_mul_abs_sin (ζ : ℂ) (ρ θ θ' : ℝ) :
    dist (circleMap ζ ρ θ) (circleMap ζ ρ θ') = 2 * |ρ| * |Real.sin ((θ - θ') / 2)| := by
  have hsub : circleMap ζ ρ θ - circleMap ζ ρ θ' =
      (ρ : ℂ) * ((Circle.exp θ : ℂ) - (Circle.exp θ' : ℂ)) := by
    simp only [circleMap, Circle.coe_exp]
    ring
  have hchord : ‖(Circle.exp θ : ℂ) - (Circle.exp θ' : ℂ)‖ = 2 * |Real.sin ((θ - θ') / 2)| := by
    rw [← dist_circleExp_eq_two_mul_abs_sin, ← Complex.dist_eq]
    exact (Subtype.dist_eq _ _).symm
  rw [dist_eq_norm, hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, hchord]
  ring

/-- **The chord with the sign of the angular difference cleared.** For angles at most a full turn
apart the chord `TauCeti.dist_circleMap_eq_two_mul_abs_sin` is `2 * |ρ| * sin (|θ - θ'| / 2)`: the
absolute value moves from outside the sine to inside it.

The width restriction is what makes the two forms differ: it puts the half-angle in `[0, π]`, where
the sine is nonnegative, and past a full turn the half-angle leaves that interval and `|sin|` and
`sin ∘ |·|` part company. Up to `π` the right-hand side is moreover an increasing function of the
angular gap, the half-angle then staying in `[0, π / 2]`; beyond `π` the formula still holds but the
chord shrinks again as the gap widens. -/
theorem dist_circleMap_eq_two_mul_sin_abs (ζ : ℂ) (ρ : ℝ) {θ θ' : ℝ} (h : |θ - θ'| ≤ 2 * π) :
    dist (circleMap ζ ρ θ) (circleMap ζ ρ θ') = 2 * |ρ| * Real.sin (|θ - θ'| / 2) := by
  have habs : |(θ - θ') / 2| = |θ - θ'| / 2 := by rw [abs_div, abs_two]
  rw [dist_circleMap_eq_two_mul_abs_sin,
    Real.abs_sin_eq_sin_abs_of_abs_le_pi (by rw [habs]; linarith), habs]

/-- **Within half a turn, the chord grows with the angular gap.** If the angle `u` is no further
from `θ₀` than `v` is, and `v` is within half a turn of `θ₀`, then the point of `circleMap ζ ρ` at
angle `u` is no further from the one at `θ₀` than the point at `v` is.

Both chords are `TauCeti.dist_circleMap_eq_two_mul_sin_abs`, and the half-angles they feed to the
sine stay in `[0, π / 2]`, where the sine is monotone. The restriction to half a turn is sharp:
antipodal points are the furthest apart, and beyond them the chord shrinks again. -/
theorem dist_circleMap_le_dist_circleMap_of_abs_sub_le (ζ : ℂ) (ρ : ℝ) {θ₀ u v : ℝ}
    (huv : |u - θ₀| ≤ |v - θ₀|) (hv : |v - θ₀| ≤ π) :
    dist (circleMap ζ ρ u) (circleMap ζ ρ θ₀) ≤ dist (circleMap ζ ρ v) (circleMap ζ ρ θ₀) := by
  have hu : |u - θ₀| ≤ π := huv.trans hv
  have hdu : dist (circleMap ζ ρ u) (circleMap ζ ρ θ₀) = 2 * |ρ| * Real.sin (|u - θ₀| / 2) :=
    dist_circleMap_eq_two_mul_sin_abs ζ ρ (by linarith [Real.pi_pos])
  have hdv : dist (circleMap ζ ρ v) (circleMap ζ ρ θ₀) = 2 * |ρ| * Real.sin (|v - θ₀| / 2) :=
    dist_circleMap_eq_two_mul_sin_abs ζ ρ (by linarith [Real.pi_pos])
  rw [hdu, hdv]
  have hsin : Real.sin (|u - θ₀| / 2) ≤ Real.sin (|v - θ₀| / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [abs_nonneg (u - θ₀), Real.pi_pos]) (by linarith) (by linarith)
  exact mul_le_mul_of_nonneg_left hsin (by positivity)

/-- **The sine of a half-angle is smallest at an end of the range of angles.** For
`0 < m ≤ t ≤ w < 2 * π`, `sin (t / 2)` is at least `min (sin (m / 2)) (sin (w / 2))`, a positive
number: the half-angle stays in `[0, π]`, where the sine rises to `π / 2` and falls back, so it is
bounded below by its value at whichever end of `[m / 2, w / 2]` the half-angle has not passed.

If `w ≤ π` the first of the two is the binding one and the second is slack; both are needed exactly
because an arc of angular width beyond `π` is allowed. -/
private lemma min_sin_div_two_le_sin_div_two {m t w : ℝ} (hm : 0 < m) (hmt : m ≤ t) (htw : t ≤ w)
    (hw : w < 2 * π) : min (Real.sin (m / 2)) (Real.sin (w / 2)) ≤ Real.sin (t / 2) := by
  rcases le_total (t / 2) (π / 2) with h | h
  · exact (min_le_left _ _).trans
      (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) h (by linarith))
  · refine (min_le_right _ _).trans ?_
    rw [← Real.sin_pi_sub (w / 2), ← Real.sin_pi_sub (t / 2)]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
      (by linarith)

/-- **On a non-wrapping arc, closeness in the plane is closeness in angle.** A point of the arc
`circleMap ζ ρ '' Ioo a b` lying within `2 * |ρ| * min (sin (m / 2)) (sin ((b - a) / 2))` of
`circleMap ζ ρ θ₀` is the image of an angle within `m` of `θ₀`. -/
theorem exists_mem_Ioo_circleMap_eq_and_abs_sub_lt_of_mem_ball_circleMap_image_Ioo (ζ : ℂ)
    (ρ : ℝ) {a b θ₀ m : ℝ}
    (hab2π : b - a < 2 * π) (hθ₀ : θ₀ ∈ Icc a b) (hm0 : 0 < m) {x : ℂ}
    (hx : x ∈ circleMap ζ ρ '' Ioo a b ∩
      ball (circleMap ζ ρ θ₀) (2 * |ρ| * min (Real.sin (m / 2)) (Real.sin ((b - a) / 2)))) :
    ∃ θ ∈ Ioo a b, circleMap ζ ρ θ = x ∧ |θ - θ₀| < m := by
  obtain ⟨⟨θ, hθ, rfl⟩, hx⟩ := hx
  refine ⟨θ, hθ, rfl, ?_⟩
  have hwidth : |θ - θ₀| ≤ b - a := by
    rw [abs_le]
    constructor <;> [linarith [hθ.1, hθ₀.2]; linarith [hθ.2, hθ₀.1]]
  have hπ : |θ - θ₀| ≤ 2 * π := by linarith
  rw [mem_ball, dist_circleMap_eq_two_mul_sin_abs ζ ρ hπ] at hx
  rcases lt_or_ge |θ - θ₀| m with hlt | hcon
  · exact hlt
  · exfalso
    -- the chord grows with the angular gap up to the width of the arc
    have hmono : min (Real.sin (m / 2)) (Real.sin ((b - a) / 2)) ≤ Real.sin (|θ - θ₀| / 2) :=
      min_sin_div_two_le_sin_div_two hm0 hcon hwidth hab2π
    nlinarith [abs_nonneg ρ]

/-- **An order-connected set of angles within half a turn of `θ₀` keeps that form when cut down by
the distance to the point at `θ₀`.** For a set `s` of angles contained in the half-turn
`[θ₀ - π, θ₀ + π]`, the angles of `s` whose points lie within `δ` of the point at angle `θ₀` form an
order-connected subset of `s`.

The chord distance to `θ₀` falls and then rises as the angle sweeps across `s`
(`TauCeti.dist_circleMap_le_dist_circleMap_of_abs_sub_le`), so an angle between two admitted ones is
itself no further from `θ₀` than the admitted one on its side of `θ₀`. The angle `θ₀` need not lie
in `s`, and the radius `δ` is arbitrary: for large `δ` the trace is all of `s`. -/
theorem ordConnected_inter_setOf_dist_circleMap_lt (ζ : ℂ) (ρ : ℝ) {s : Set ℝ} {θ₀ δ : ℝ}
    (hs : s.OrdConnected) (hsub : s ⊆ Icc (θ₀ - π) (θ₀ + π)) :
    (s ∩ {θ | dist (circleMap ζ ρ θ) (circleMap ζ ρ θ₀) < δ}).OrdConnected := by
  refine ⟨fun x hx y hy z hz => ⟨hs.out hx.1 hy.1 hz, ?_⟩⟩
  rcases le_total z θ₀ with hzθ | hzθ
  · refine lt_of_le_of_lt (dist_circleMap_le_dist_circleMap_of_abs_sub_le ζ ρ ?_ ?_) hx.2
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith [hz.1])]
      linarith [hz.1]
    · rw [abs_le]
      exact ⟨by linarith [(hsub hx.1).1], by linarith [(hsub hx.1).2]⟩
  · refine lt_of_le_of_lt (dist_circleMap_le_dist_circleMap_of_abs_sub_le ζ ρ ?_ ?_) hy.2
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith [hz.2])]
      linarith [hz.2]
    · rw [abs_le]
      exact ⟨by linarith [(hsub hy.1).1], by linarith [(hsub hy.1).2]⟩

/-- **The law of cosines for a point of a circle.** The point of `circleMap ζ ρ` at angle `θ` is at
distance `ρ ^ 2 + dist ζ c ^ 2 - 2 * ρ * dist ζ c * cos (θ - arg (c - ζ))`, squared, from an
arbitrary point `c`. For `ρ ≥ 0` this is the law of cosines as usually read: in the triangle with
vertices `ζ`, `circleMap ζ ρ θ` and `c`, the angle at `ζ` between the two sides of lengths `ρ` and
`dist ζ c` is `θ - arg (c - ζ)`. It is the chord formula
`TauCeti.dist_circleMap_eq_two_mul_abs_sin` with one endpoint allowed off the circle.

Nothing is assumed, and the identity is the signed-radius extension of that reading. For `ρ < 0`
the point `circleMap ζ ρ θ` is the one at angle `θ + π` on the circle of radius `-ρ`, so the side
at `ζ` has length `-ρ` and points in the direction `θ + π`; the identity still holds as stated
because only `ρ ^ 2` and `ρ * cos` occur, and the two sign changes cancel. For `c = ζ` both terms
carrying `dist ζ c` vanish, so the junk value `arg 0 = 0` does no harm and the identity reads
`dist (circleMap ζ ρ θ) ζ ^ 2 = ρ ^ 2`. -/
theorem dist_circleMap_sq (ζ c : ℂ) (ρ θ : ℝ) :
    dist (circleMap ζ ρ θ) c ^ 2
      = ρ ^ 2 + dist ζ c ^ 2 - 2 * ρ * dist ζ c * Real.cos (θ - (c - ζ).arg) := by
  have hdist : dist ζ c = ‖c - ζ‖ := by rw [dist_eq_norm, norm_sub_rev]
  have hsub : circleMap ζ ρ θ - c
      = (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) - (c - ζ) := by
    simp only [circleMap]; ring
  -- the conjugate of `c - ζ` in polar form, valid at `c = ζ` as well
  have hconj : (starRingEnd ℂ) (c - ζ)
      = ((‖c - ζ‖ : ℝ) : ℂ) * Complex.exp (((-(c - ζ).arg : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (c - ζ)]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    push_cast
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  -- the cross term is the cosine of the angle at `ζ`
  have hre : ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * (starRingEnd ℂ) (c - ζ)).re
      = ρ * ‖c - ζ‖ * Real.cos (θ - (c - ζ).arg) := by
    have hmul : (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) * (starRingEnd ℂ) (c - ζ)
        = ((ρ * ‖c - ζ‖ : ℝ) : ℂ)
            * Complex.exp (((θ - (c - ζ).arg : ℝ) : ℂ) * Complex.I) := by
      rw [hconj, mul_mul_mul_comm, ← Complex.exp_add]
      push_cast
      ring_nf
    rw [hmul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hunit : Complex.normSq ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = ρ ^ 2 := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    ring
  rw [dist_eq_norm, Complex.sq_norm, hsub, Complex.normSq_sub, hunit, hre,
    Complex.normSq_eq_norm_sq, hdist]
  ring

/-- **When a point of a circle lies in a disc**, read off the law of cosines. For `r ≥ 0` and a
disc `ball c r` whose centre is unrelated to the centre `ζ` of the circle, the point
`circleMap ζ ρ θ` lies in `ball c r` exactly when
`ρ ^ 2 + dist ζ c ^ 2 - r ^ 2 < 2 * ρ * dist ζ c * cos (θ - arg (c - ζ))`.

This is `TauCeti.dist_circleMap_sq` compared with `r ^ 2`, both sides of `dist … < r` being
nonnegative. Nothing is assumed of `ρ`: for `ρ > 0` the point described is the point of
`sphere ζ ρ` at angle `θ`, and for `ρ < 0` it is the point of `sphere ζ (-ρ)` at angle `θ + π`,
the criterion following it as the law of cosines does. Since the right-hand side depends on `θ`
only through `cos (θ - arg (c - ζ))`, the angles it admits form an arc
(`TauCeti.circleMap_mem_ball_of_mem_Icc`).

At a point `ζ` of the boundary circle `sphere c r` the two squared radii cancel and, for `ρ > 0`,
the surviving condition `ρ ^ 2 < 2 * ρ * r * cos (θ - arg (c - ζ))` may be divided by `ρ`; that
case is `TauCeti.circleMap_mem_ball_iff` of
`TauCeti/Analysis/Complex/Conformal/Crosscut/Basic.lean`. -/
theorem circleMap_mem_ball_iff_sq {c ζ : ℂ} {r : ℝ} (hr : 0 ≤ r) (ρ θ : ℝ) :
    circleMap ζ ρ θ ∈ ball c r ↔
      ρ ^ 2 + dist ζ c ^ 2 - r ^ 2 < 2 * ρ * dist ζ c * Real.cos (θ - (c - ζ).arg) := by
  rw [mem_ball, ← sq_lt_sq₀ dist_nonneg hr, dist_circleMap_sq]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **When a point of a circle lies in a closed disc.** The weak companion of
`TauCeti.circleMap_mem_ball_iff_sq`: for `r ≥ 0` and an arbitrary centre `ζ`, the point
`circleMap ζ ρ θ` lies in `closedBall c r` exactly when
`ρ ^ 2 + dist ζ c ^ 2 - r ^ 2 ≤ 2 * ρ * dist ζ c * cos (θ - arg (c - ζ))`. Nothing is assumed of
`ρ`, whose sign is read as it is there.

At a point `ζ` of the boundary circle `sphere c r` the two squared radii cancel and, for `ρ > 0`,
the surviving condition may be divided by `ρ`; that case is
`TauCeti.circleMap_mem_closedBall_iff` of
`TauCeti/Analysis/Complex/Conformal/Crosscut/Endpoints.lean`. -/
theorem circleMap_mem_closedBall_iff_sq {c ζ : ℂ} {r : ℝ} (hr : 0 ≤ r) (ρ θ : ℝ) :
    circleMap ζ ρ θ ∈ closedBall c r ↔
      ρ ^ 2 + dist ζ c ^ 2 - r ^ 2 ≤ 2 * ρ * dist ζ c * Real.cos (θ - (c - ζ).arg) := by
  rw [mem_closedBall, ← sq_le_sq₀ dist_nonneg hr, dist_circleMap_sq]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **A circle meets a disc in a connected set of angles.** If the angles `a` and `b` both lie
within `π` of the direction `arg (c - ζ)` from the centre `ζ` of the circle to the centre `c` of
the disc, and both put the point of `sphere ζ ρ` they name inside `ball c r`, then so does every
angle in `[a, b]`.

This is `TauCeti.circleMap_mem_ball_iff_sq` read through the unimodality of `cos` on a period
centred at `arg (c - ζ)`, which is `Real.lt_cos_of_mem_Icc`. Neither `0 < r` nor any relation
between `ζ` and the disc is assumed: the first is forced by the hypotheses, and the second is not
needed, so the conclusion covers a cutting circle centred anywhere and not only the circular
crosscut at a boundary point `ζ` of the disc. Two
degenerate cases are covered as well, in both of which the criterion is independent of the angle: a
circle centred at `c` itself, whose points are all at the same distance from `c`, and the circle of
radius `ρ = 0`, which is the single point `ζ`. -/
theorem circleMap_mem_ball_of_mem_Icc {c ζ : ℂ} {r ρ : ℝ} (hρ : 0 ≤ ρ) {a b θ : ℝ}
    (ha : -π ≤ a - (c - ζ).arg) (hb : b - (c - ζ).arg ≤ π) (hθ : θ ∈ Icc a b)
    (hain : circleMap ζ ρ a ∈ ball c r) (hbin : circleMap ζ ρ b ∈ ball c r) :
    circleMap ζ ρ θ ∈ ball c r := by
  have hr : 0 < r := dist_nonneg.trans_lt (mem_ball.mp hain)
  rw [circleMap_mem_ball_iff_sq hr.le] at hain hbin ⊢
  have hnn : (0 : ℝ) ≤ 2 * ρ * dist ζ c := mul_nonneg (by linarith) dist_nonneg
  rcases hnn.eq_or_lt with hd | hpos
  · -- a circle centred at `c`, or one of radius zero: the criterion does not see the angle at all
    rw [← hd] at hain ⊢
    linarith
  · -- otherwise divide by `2 * ρ * dist ζ c` and use that `cos` has no interior minimum
    have hkey : ∀ x : ℝ, (ρ ^ 2 + dist ζ c ^ 2 - r ^ 2
          < 2 * ρ * dist ζ c * Real.cos (x - (c - ζ).arg))
        ↔ (ρ ^ 2 + dist ζ c ^ 2 - r ^ 2) / (2 * ρ * dist ζ c)
          < Real.cos (x - (c - ζ).arg) := fun x => by
      rw [div_lt_iff₀ hpos, mul_comm]
    rw [hkey] at hain hbin ⊢
    exact Real.lt_cos_of_mem_Icc ha hb ⟨by linarith [hθ.1], by linarith [hθ.2]⟩ hain hbin

/-- **The chord is at most the arc**: `Circle.exp` is `1`-Lipschitz. -/
theorem lipschitzWith_one_circleExp : LipschitzWith 1 Circle.exp :=
  LipschitzWith.mk_one fun a b => by
    rw [Real.dist_eq, dist_circleExp_eq_norm_exp_sub_one, ← Real.norm_eq_abs]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- An arc of the circle spanning the angles `Set.Icc a b` has diameter at most `b - a`. -/
theorem diam_circleExp_image_Icc_le {a b : ℝ} (hab : a ≤ b) :
    Metric.diam (Circle.exp '' Icc a b) ≤ b - a := by
  simpa only [NNReal.coe_one, one_mul, Real.diam_Icc hab] using
    lipschitzWith_one_circleExp.diam_image_le (Icc a b) (isBounded_Icc a b)

/-- **A closed arc is no wider than its angle.** Mathlib's arc `Circle.path x y`, which runs
counterclockwise from `x` to `y`, has range of diameter at most the length `Circle.angleDiff x y`
of that arc.

This is `TauCeti.diam_circleExp_image_Icc_le` read through `Circle.range_path`, which presents the
closed arc as the `Circle.exp` image of an interval of angles of length `Circle.angleDiff x y`. It
is stated for the range rather than for the path so that it applies unchanged to the reversed arc,
whose range is the same by `Path.symm_range`. -/
theorem diam_range_circlePath_le (x y : Circle) :
    Metric.diam (range (Circle.path x y)) ≤ Circle.angleDiff x y := by
  rw [Circle.range_path]
  simpa using diam_circleExp_image_Icc_le (a := Complex.arg (x : ℂ))
    (b := Circle.angleDiff x y + Complex.arg (x : ℂ)) (by simp [Circle.angleDiff_nonneg])

/-- **The shorter arc is controlled by the chord**: of the two arcs joining `x` to `y` on the
circle, the shorter has length at most `π / 2` times the distance from `x` to `y`.

This is the direction of the comparison that converts a hypothesis about the ambient metric into a
bound on an arc, and so the one a transport argument consumes. -/
theorem min_angleDiff_le_pi_div_two_mul_dist (x y : Circle) :
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
  -- `sin (t / 2)` is unchanged when `t` is replaced by `2 * π - t`, so the half-angle sine may be
  -- computed from whichever of the two arc lengths is at most `π`.
  rcases le_total (Circle.angleDiff x y) π with hle | hle
  · exact (min_le_left _ _).trans (key _ hpos hle rfl)
  · refine (min_le_right _ _).trans (key _ (by linarith) (by linarith) ?_)
    have hrefl : Circle.angleDiff y x / 2 = π - Circle.angleDiff x y / 2 := by linarith
    rw [hrefl, Real.sin_pi_sub]

end TauCeti
