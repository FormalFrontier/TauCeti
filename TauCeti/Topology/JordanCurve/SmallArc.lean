/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.JordanCurve.Separation
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Two nearby points cut a small arc off a Jordan curve

`TauCeti/Topology/JordanCurve/Separation.lean` cuts a Jordan curve at two of its points into two
arcs. That cutting is purely qualitative: it says nothing about the *size* of the two pieces. This
file adds the quantitative statement, for a Jordan curve in a metric space: **as the two cut points
approach each other, one of the two arcs shrinks**. Given `ε > 0` there is a `δ > 0` such that any
two distinct points of the curve at distance less than `δ` cut off an arc of diameter at most `ε`.

The statement is not a formality — it is exactly where compactness of the curve enters. Two points
of a Jordan curve that are close in the ambient space need not be close *along* the curve for any
individual pair; what makes them close along the curve is that the parametrization by the circle is
a homeomorphism of a compact space, hence uniformly continuous in both directions.

## Why this is a layer-L5 prerequisite

Layer **L5** of the conformal-mapping roadmap (`TauCetiRoadmap/ConformalMapping/README.md`) is
Carathéodory's boundary correspondence for a Jordan domain. Its analytic half runs the length–area
method on the circular crosscuts of `Conformal/Crosscut.lean`: a crosscut of the disc at a boundary
point is mapped by the Riemann map to a crosscut of `Ω` whose *endpoints* on `∂Ω` are close, by the
length–area estimate `TauCeti.exists_diam_image_ball_inter_sphere_le`. To convert that into the
collar bound `TauCeti.exists_continuousOn_closedBall_eqOn` asks for, one needs the *region* the
image crosscut cuts off to be small, and that region is bounded by the crosscut together with one of
the two arcs into which its endpoints cut `∂Ω`. So the missing geometric input is precisely that two
nearby points of the Jordan curve `∂Ω` cut off an arc of small diameter — which is what this file
supplies, at the generality of an arbitrary Jordan curve in a metric space.

## The argument

Everything is transported from the model curve, and the transport is quantitative, so the circle
comes first with two elementary metric facts about `Circle.exp`, both of them Mathlib estimates for
the normalized chord `‖exp (I * θ) - 1‖` read off the factorization `exp a - exp b =
(exp (a - b) - 1) * exp b`:

* the **chord formula** `TauCeti.dist_circleExp_eq_two_mul_abs_sin`, `dist (exp a) (exp b) =
  2 * |sin ((a - b) / 2)|`, which is Mathlib's `Complex.norm_exp_I_mul_ofReal_sub_one`;
* the fact that the chord is at most the arc, `TauCeti.lipschitzWith_one_circleExp`, which is
  Mathlib's `Real.norm_exp_I_mul_ofReal_sub_one_le`, whence `TauCeti.diam_circleExp_image_Icc_le`
  by `LipschitzWith.diam_image_le` and `Real.diam_Icc`.

In the converse direction, the *shorter* of the two arc lengths `Circle.angleDiff` separating two
points is at most `π / 2` times their chord (`TauCeti.min_angleDiff_le_dist`). That bound is
Jordan's inequality `Real.mul_le_sin` applied to the chord formula, and it is the direction that
matters here: it is what turns a hypothesis about the ambient distance into a bound on an arc.

Together these give `TauCeti.exists_isPreconnected_union_eq_compl_pair_circle_diam_le`: two
distinct points of the circle cut it into two preconnected pieces, the first of which stays of
diameter at most `π / 2` times their distance after the cut points are put back. The two pieces are
Mathlib's open arcs `Circle.path z w '' Set.Ioo 0 1` and `Circle.path w z '' Set.Ioo 0 1`, whose
covering of the cut circle is `Circle.compl_range_path` together with
`Circle.range_path_inter_range_path`, and each of them with its two endpoints lies in the closed arc
`Circle.range_path`, a `Circle.exp` image of an interval of angles, on which the diameter bound is
immediate. Only preconnectedness of the pieces is recorded, not the openness and path-connectedness
of `TauCeti.exists_isOpen_isPathConnected_union_eq_compl_pair_circle`; that is all the transport
below consumes.

The transport then runs both uniform continuities of the parametrization `TauCeti.jordanParam` of
`TauCeti/Topology/JordanCurve/Separation.lean` at once: one converts "the two points are close in
`X`" into "their parameters are close on the circle", the other converts "the parameter arc is
short" into "its image has small diameter".

## Identifying the arcs

The conclusion is stated so that it constrains *any* decomposition of `C \ {p, q}` into two arcs,
rather than only the one this file happens to build:
`TauCeti.IsJordanCurve.exists_pos_forall_diam_le`
says that for `A` and `B` disjoint with union `C \ {p, q}` and separating preconnected sets — the
exact conclusion of `TauCeti.IsJordanCurve.exists_isPathConnected_union_eq_sdiff_pair` — one of
`A ∪ {p, q}`, `B ∪ {p, q}` has diameter at most `ε`. That works because the separating property
applied to the two transported pieces pins each of them inside `A` or inside `B`, and a piece that
swallows both makes the other one empty. Feeding it the arcs of that theorem gives the packaged form
`TauCeti.IsJordanCurve.exists_pos_forall_exists_diam_le`, in which the *first* arc is the small one.

The two cut points are kept in the set whose diameter is bounded because that is the set a consumer
needs: the small arc is used as a boundary curve, joined to a crosscut ending at `p` and `q`, so the
endpoints must lie in the small set. It is also the stronger statement, `Metric.diam A ≤ ε`
following by `Metric.diam_mono`. No incidence statement such as `p ∈ closure A` can be added at this
generality, since `A = ∅` and `B = C \ {p, q}` satisfy every hypothesis.

## Generality

Unlike `TauCeti/Topology/JordanCurve/Separation.lean`, whose statements are for an arbitrary
topological space, the results here need a metric on the ambient space to speak of `Metric.diam` and
of two points being close, so `X` carries a `PseudoMetricSpace` instance. Nothing else is assumed:
in particular the curve is not required to lie in `ℂ`, so `∂Ω` may be met at whatever generality a
consumer has it.

## Main results

* `TauCeti.dist_circleExp_eq_two_mul_abs_sin` — the chord subtended by an arc of angle `θ` of the
  unit circle has length `2 * |sin (θ / 2)|`.
* `TauCeti.lipschitzWith_one_circleExp` and `TauCeti.diam_circleExp_image_Icc_le` — the chord is at
  most the arc, so an arc of angles of length `b - a` has image of diameter at most `b - a`.
* `TauCeti.min_angleDiff_le_dist` — the shorter of the two arcs joining two points of the circle has
  length at most `π / 2` times their distance.
* `TauCeti.exists_isPreconnected_union_eq_compl_pair_circle_diam_le` — two distinct points cut the
  circle into two preconnected arcs, the first of which is of diameter at most `π / 2` times their
  distance even after the two points are put back.
* `TauCeti.IsJordanCurve.exists_pos_forall_diam_le` — **the main statement**: for every `ε > 0`
  there is a `δ > 0` such that two distinct points `p`, `q` of a Jordan curve at distance less than
  `δ` cut it into two arcs one of which has diameter at most `ε` together with `p` and `q`.
* `TauCeti.IsJordanCurve.exists_pos_forall_exists_diam_le` — the same packaged with the cutting
  itself, producing the two arcs with the small one named first.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
-/

public section

namespace TauCeti

open Metric Set Topology

open scoped Real

/-! ## The chord and the arc -/

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

/-! ## Cutting the circle into a short arc and a long one -/

/-- **Two distinct points cut the circle into a short arc and a long one.** The complement of
`{z, w}` is the union of two preconnected sets, the first of which stays of diameter at most
`π / 2 * dist z w` even after the two cut points are put back: it is `P ∪ {z, w}`, the *closed*
short arc, that is bounded.

The two sets are Mathlib's two open arcs `Circle.path z w '' Set.Ioo 0 1` and
`Circle.path w z '' Set.Ioo 0 1`, which cover the complement of `{z, w}` by
`Circle.compl_range_path` and `Circle.range_path_inter_range_path`. Adding the endpoints back to
either of them lands inside the corresponding closed arc `Circle.range_path` — the endpoints are the
values of the path at `0` and `1` — and that closed arc is an image of an interval of angles of
length `Circle.angleDiff`, so `TauCeti.diam_circleExp_image_Icc_le` bounds its diameter by that arc
length; which of the two is named first depends on which of `Circle.angleDiff z w` and
`Circle.angleDiff w z` is the smaller, and `TauCeti.min_angleDiff_le_dist` bounds that one by the
chord. -/
theorem exists_isPreconnected_union_eq_compl_pair_circle_diam_le {z w : Circle} (hzw : z ≠ w) :
    ∃ P Q : Set Circle, IsPreconnected P ∧ IsPreconnected Q ∧
      P ∪ Q = ({z, w} : Set Circle)ᶜ ∧ Metric.diam (P ∪ {z, w}) ≤ π / 2 * dist z w := by
  have hunion : Circle.path z w '' Ioo 0 1 ∪ Circle.path w z '' Ioo 0 1 =
      ({z, w} : Set Circle)ᶜ := by
    rw [← Circle.compl_range_path hzw.symm, ← Circle.compl_range_path hzw, ← compl_inter,
      Circle.range_path_inter_range_path hzw.symm, pair_comm]
  have hpre : ∀ x y : Circle, IsPreconnected (Circle.path x y '' Ioo 0 1) := fun x y =>
    isPreconnected_Ioo.image _ (Circle.path x y).continuous.continuousOn
  have hdiam : ∀ x y : Circle,
      Metric.diam (Circle.path x y '' Ioo 0 1 ∪ {x, y}) ≤ Circle.angleDiff x y := fun x y => by
    have hsub : Circle.path x y '' Ioo 0 1 ∪ {x, y} ⊆ range (Circle.path x y) :=
      union_subset (image_subset_range _ _)
        (insert_subset ⟨0, (Circle.path x y).source⟩
          (singleton_subset_iff.2 ⟨1, (Circle.path x y).target⟩))
    refine (Metric.diam_mono hsub
      (isCompact_range (Circle.path x y).continuous).isBounded).trans ?_
    rw [Circle.range_path]
    simpa using diam_circleExp_image_Icc_le (a := Complex.arg (x : ℂ))
      (b := Circle.angleDiff x y + Complex.arg (x : ℂ)) (by simp [Circle.angleDiff_nonneg])
  have hmin := min_angleDiff_le_dist z w
  rcases le_total (Circle.angleDiff z w) (Circle.angleDiff w z) with hle | hle
  · exact ⟨_, _, hpre z w, hpre w z, hunion,
      (hdiam z w).trans ((le_min_iff.mpr ⟨le_rfl, hle⟩).trans hmin)⟩
  · refine ⟨_, _, hpre w z, hpre z w, by rw [union_comm]; exact hunion, ?_⟩
    rw [pair_comm z w]
    exact (hdiam w z).trans ((le_min_iff.mpr ⟨hle, le_rfl⟩).trans hmin)

/-! ## Cutting a Jordan curve -/

variable {X : Type*} [PseudoMetricSpace X] {C : Set X} {ε : ℝ}

/-- The set-theoretic content of locating the two transported arcs, applied symmetrically to the
two sides of the cut in `TauCeti.IsJordanCurve.exists_pos_forall_diam_le`: if the disjoint sets `A`
and `B` are covered by `U` and `V` with `U ⊆ A`, then either `V ⊆ B`, and then `A` is no larger
than `U`, or `V ⊆ A` as well, and then `B` is empty. -/
private lemma subset_or_eq_empty_of_union_eq_union {α : Type*} {A B U V : Set α}
    (hcover : U ∪ V = A ∪ B) (hdisj : Disjoint A B) (hU : U ⊆ A) (hV : V ⊆ A ∨ V ⊆ B) :
    A ⊆ U ∨ B = ∅ := by
  rcases hV with hVA | hVB
  · refine Or.inr (eq_empty_of_subset_empty fun x hx => ?_)
    have hmem : x ∈ U ∪ V := by rw [hcover]; exact mem_union_right A hx
    exact hdisj.le_bot ⟨hmem.elim (fun h => hU h) fun h => hVA h, hx⟩
  · refine Or.inl fun x hx => ?_
    have hmem : x ∈ U ∪ V := by rw [hcover]; exact mem_union_left B hx
    exact hmem.elim id fun h => absurd (hdisj.le_bot ⟨hx, hVB h⟩) id

/-- **Two nearby points cut a small arc off a Jordan curve.** For every `ε > 0` there is a `δ > 0`
with the following property: if `p` and `q` are two distinct points of a Jordan curve `C` at
distance less than `δ`, then in any splitting of `C \ {p, q}` into two disjoint pieces `A` and `B`
that separate it — that is, such that every preconnected subset of `C \ {p, q}` lies in one of
them — one of the two pieces has diameter at most `ε` *together with the two cut points*: the bound
is on `A ∪ {p, q}` or on `B ∪ {p, q}`, the corresponding **closed** arc.

Bounding the closed arc rather than the open one is what a consumer needs: the small arc is used as
a boundary curve joined to a crosscut ending at `p` and `q`, so the endpoints have to be inside the
set that is small. It is also strictly stronger, `Metric.diam A ≤ ε` following by
`Metric.diam_mono`. Note that no incidence statement such as `p ∈ closure A` can be added at this
generality: `A = ∅`, `B = C \ {p, q}` satisfies every hypothesis.

The splitting is the one `TauCeti.IsJordanCurve.exists_isPathConnected_union_eq_sdiff_pair`
produces, and the hypotheses here are exactly its conclusion, so that the statement constrains that
cutting without having to reproduce it; `TauCeti.IsJordanCurve.exists_pos_forall_exists_diam_le`
records the combination.

The proof transports `TauCeti.exists_isPreconnected_union_eq_compl_pair_circle_diam_le` along the
parametrization `TauCeti.jordanParam` of `C` by the circle, using its uniform continuity in one
direction to make the parameters of `p` and `q` close and in the other to make the image of the
short *closed* arc of parameters have small diameter. The transported open pieces are preconnected
subsets of `C \ {p, q}`, so each lies in `A` or in `B`; if both land in the same one, the other is
empty and only `{p, q}` is left, which is small because `δ ≤ ε`; otherwise the one containing the
short piece is *contained* in it, because the pieces cover `C \ {p, q}` while `A` and `B` are
disjoint. -/
theorem IsJordanCurve.exists_pos_forall_diam_le (h : IsJordanCurve C) (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃p : X⦄, p ∈ C → ∀ ⦃q : X⦄, q ∈ C → p ≠ q → dist p q < δ →
      ∀ A B : Set X, A ∪ B = C \ {p, q} → Disjoint A B →
        (∀ ⦃S : Set X⦄, S ⊆ C \ {p, q} → IsPreconnected S → S ⊆ A ∨ S ⊆ B) →
        Metric.diam (A ∪ {p, q}) ≤ ε ∨ Metric.diam (B ∪ {p, q}) ≤ ε := by
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp h.isCompact
  set g := jordanParam e with hg
  have hgc : Continuous g := continuous_jordanParam e
  have hginj : Function.Injective g := injective_jordanParam e
  have hgrange : range g = C := range_jordanParam e
  -- Uniform continuity of the parametrization turns short arcs into sets of small diameter.
  obtain ⟨η, hη₀, hη⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hgc) ε hε
  -- Uniform continuity of its inverse turns nearby points into nearby parameters.
  obtain ⟨δ, hδ₀, hδ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous e.continuous) (2 / π * η) (by positivity)
  -- `δ ≤ ε` so that the two cut points alone are already of diameter at most `ε`.
  refine ⟨min δ ε, lt_min hδ₀ hε, fun p hp q hq hpq hpqδ A B hAB hdisj hsep => ?_⟩
  have hpqε : dist p q ≤ ε := (hpqδ.trans_le (min_le_right _ _)).le
  set z := e ⟨p, hp⟩ with hzdef
  set w := e ⟨q, hq⟩ with hwdef
  have hgz : g z = p := jordanParam_apply e hp
  have hgw : g w = q := jordanParam_apply e hq
  have hzw : z ≠ w := fun hh => hpq (congrArg Subtype.val (e.injective hh))
  have hchord : π / 2 * dist z w < η := by
    have hd : dist z w < 2 / π * η :=
      hδ (by simpa [Subtype.dist_eq] using hpqδ.trans_le (min_le_left _ _))
    have hπ : 0 < π := Real.pi_pos
    calc π / 2 * dist z w < π / 2 * (2 / π * η) := by
          exact mul_lt_mul_of_pos_left hd (by positivity)
      _ = η := by field_simp
  obtain ⟨P₀, Q₀, hP₀c, hQ₀c, hunion₀, hP₀d⟩ :=
    exists_isPreconnected_union_eq_compl_pair_circle_diam_le hzw
  -- Transport the two arcs of parameters to the curve.
  have himg : g '' P₀ ∪ g '' Q₀ = C \ {p, q} := by
    rw [← image_union, hunion₀, compl_eq_univ_sdiff, image_sdiff hginj, image_univ, hgrange]
    congr 1
    rw [image_insert_eq, image_singleton, hgz, hgw]
  have hPsub : g '' P₀ ⊆ C \ {p, q} := himg ▸ subset_union_left
  have hQsub : g '' Q₀ ⊆ C \ {p, q} := himg ▸ subset_union_right
  -- The closed short arc downstairs is the image of the closed short arc of parameters.
  have hclosed : g '' (P₀ ∪ {z, w}) = g '' P₀ ∪ {p, q} := by
    rw [image_union, image_insert_eq, image_singleton, hgz, hgw]
  have hPdiam : Metric.diam (g '' P₀ ∪ {p, q}) ≤ ε := by
    rw [← hclosed]
    refine Metric.diam_le_of_forall_dist_le hε.le ?_
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have hbdd : Bornology.IsBounded (P₀ ∪ {z, w}) :=
      (isCompact_univ (X := Circle)).isBounded.subset (subset_univ _)
    exact (hη (lt_of_le_of_lt (Metric.dist_le_diam_of_mem hbdd hu hv)
      (lt_of_le_of_lt hP₀d hchord))).le
  have hPbdd : Bornology.IsBounded (g '' P₀ ∪ {p, q}) :=
    h.isCompact.isBounded.subset (union_subset (hPsub.trans sdiff_subset)
      (insert_subset hp (singleton_subset_iff.2 hq)))
  -- The side containing the short arc either is contained in it, and so is small, or leaves the
  -- other side empty, and then only the two cut points are left.
  have hside : ∀ A' B' : Set X, A' ∪ B' = C \ {p, q} → Disjoint A' B' → g '' P₀ ⊆ A' →
      (g '' Q₀ ⊆ A' ∨ g '' Q₀ ⊆ B') →
      Metric.diam (A' ∪ {p, q}) ≤ ε ∨ Metric.diam (B' ∪ {p, q}) ≤ ε := by
    intro A' B' hcover hd hP hQ
    rcases subset_or_eq_empty_of_union_eq_union (himg.trans hcover.symm) hd hP hQ with hsub | hemp
    · exact Or.inl ((Metric.diam_mono (union_subset_union_left _ hsub) hPbdd).trans hPdiam)
    · rw [hemp, empty_union, Metric.diam_pair]
      exact Or.inr hpqε
  -- Locate each transported arc inside `A` or inside `B`, and apply that symmetrically.
  have hQ := hsep hQsub (hQ₀c.image _ hgc.continuousOn)
  rcases hsep hPsub (hP₀c.image _ hgc.continuousOn) with hPA | hPB
  · exact hside A B hAB hdisj hPA hQ
  · exact (hside B A (by rw [union_comm]; exact hAB) hdisj.symm hPB hQ.symm).symm

/-- **Two nearby points cut a small arc off a Jordan curve**, in packaged form: for every `ε > 0`
there is a `δ > 0` such that two distinct points of a Jordan curve at distance less than `δ` cut it
into two arcs, the first of which has diameter at most `ε` *once its two endpoints are put back*,
that is, `A ∪ {p, q}` is small.

This is `TauCeti.IsJordanCurve.exists_isPathConnected_union_eq_sdiff_pair` together with
`TauCeti.IsJordanCurve.exists_pos_forall_diam_le`, the two arcs being swapped when it is the second
that comes out small. It is the form the Carathéodory boundary argument consumes: the small *closed*
arc `A ∪ {p, q}`, together with the crosscut whose endpoints are `p` and `q`, bounds the region that
has to be shown to have small diameter, so the endpoints must be inside the set that is bounded. -/
theorem IsJordanCurve.exists_pos_forall_exists_diam_le (h : IsJordanCurve C) (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃p : X⦄, p ∈ C → ∀ ⦃q : X⦄, q ∈ C → p ≠ q → dist p q < δ →
      ∃ A B : Set X, IsPathConnected A ∧ IsPathConnected B ∧ Disjoint A B ∧
        A ∪ B = C \ {p, q} ∧
        (∀ ⦃S : Set X⦄, S ⊆ C \ {p, q} → IsPreconnected S → S ⊆ A ∨ S ⊆ B) ∧
        Metric.diam (A ∪ {p, q}) ≤ ε := by
  obtain ⟨δ, hδ₀, hδ⟩ := h.exists_pos_forall_diam_le hε
  refine ⟨δ, hδ₀, fun p hp q hq hpq hpqδ => ?_⟩
  obtain ⟨A, B, hAc, hBc, hdisj, hunion, hsep⟩ :=
    h.exists_isPathConnected_union_eq_sdiff_pair hp hq hpq
  rcases hδ hp hq hpq hpqδ A B hunion hdisj hsep with hA | hB
  · exact ⟨A, B, hAc, hBc, hdisj, hunion, hsep, hA⟩
  · exact ⟨B, A, hBc, hAc, hdisj.symm, by rw [union_comm]; exact hunion,
      fun S hS hSc => (hsep hS hSc).symm, hB⟩

end TauCeti
