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
comes first with two elementary metric facts about `Circle.exp`:

* the **chord formula** `TauCeti.dist_circleExp_eq_two_mul_abs_sin`, `dist (exp a) (exp b) =
  2 * |sin ((a - b) / 2)|`, obtained by factoring out the unimodular `exp b` and halving the angle;
* its two consequences, that the chord is at most the arc
  (`TauCeti.dist_circleExp_le`, whence `TauCeti.diam_circleExp_image_Ioo_le`) and, in the converse
  direction, that the *shorter* of the two arc lengths `Circle.angleDiff` separating two points is
  at most `π / 2` times their chord (`TauCeti.min_angleDiff_le_dist`). The converse bound is
  Jordan's inequality `Real.mul_le_sin`, and it is the direction that matters here: it is what turns
  a hypothesis about the ambient distance into a bound on an arc.

Together these give `TauCeti.exists_isPreconnected_union_eq_compl_pair_circle_diam_le`: two
distinct points of the circle cut it into two preconnected pieces, the first of diameter at most
`π / 2` times their distance. Only preconnectedness of the pieces is recorded, not the openness and
path-connectedness of `TauCeti.exists_isOpen_isPathConnected_union_eq_compl_pair_circle`; that is
all the transport below consumes, and it lets the two arcs be written as `Circle.exp` images of
open intervals of angles, on which the diameter bound is immediate.

The transport then runs both uniform continuities of the parametrization `Circle ≃ₜ C` at once:
one converts "the two points are close in `X`" into "their parameters are close on the circle",
the other converts "the parameter arc is short" into "its image has small diameter".

## Identifying the arcs

The conclusion is stated so that it constrains *any* decomposition of `C \ {p, q}` into two arcs,
rather than only the one this file happens to build:
`TauCeti.IsJordanCurve.exists_pos_forall_diam_le`
says that for `A` and `B` disjoint with union `C \ {p, q}` and separating preconnected sets — the
exact conclusion of `TauCeti.IsJordanCurve.exists_isPathConnected_union_eq_sdiff_pair` — one of `A`,
`B` has diameter at most `ε`. That works because the separating property applied to the two
transported pieces pins each of them inside `A` or inside `B`, and a piece that swallows both makes
the other one empty. Feeding it the arcs of that theorem gives the packaged form
`TauCeti.IsJordanCurve.exists_pos_forall_exists_diam_le`, in which the *first* arc is the small one.

## Generality

Unlike `TauCeti/Topology/JordanCurve/Separation.lean`, whose statements are for an arbitrary
topological space, the results here need a metric on the ambient space to speak of `Metric.diam` and
of two points being close, so `X` carries a `PseudoMetricSpace` instance. Nothing else is assumed:
in particular the curve is not required to lie in `ℂ`, so `∂Ω` may be met at whatever generality a
consumer has it.

## Main results

* `TauCeti.dist_circleExp_eq_two_mul_abs_sin` — the chord subtended by an arc of angle `θ` of the
  unit circle has length `2 * |sin (θ / 2)|`.
* `TauCeti.dist_circleExp_le` and `TauCeti.diam_circleExp_image_Ioo_le` — the chord is at most the
  arc, so an arc of angles of length `b - a` has image of diameter at most `b - a`.
* `TauCeti.min_angleDiff_le_dist` — the shorter of the two arcs joining two points of the circle has
  length at most `π / 2` times their distance.
* `TauCeti.exists_isPreconnected_union_eq_compl_pair_circle_diam_le` — two distinct points cut the
  circle into two preconnected arcs, the first of diameter at most `π / 2` times their distance.
* `TauCeti.IsJordanCurve.exists_pos_forall_diam_le` — **the main statement**: for every `ε > 0`
  there is a `δ > 0` such that two distinct points of a Jordan curve at distance less than `δ` cut
  it into two arcs one of which has diameter at most `ε`.
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

/-- The chord subtended by an arc of angle `θ` starting at `1` has length `2 * |sin (θ / 2)|`.

Squaring both sides turns the claim into `2 - 2 * cos θ = 4 * sin (θ / 2) ^ 2`, which is the
half-angle formula `Real.cos_two_mul_eq_one_sub`. -/
private lemma norm_circleExp_sub_one (θ : ℝ) :
    ‖(Circle.exp θ : ℂ) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have hsplit : ((Circle.exp θ : ℂ) - 1) =
      ((Real.cos θ - 1 : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
    rw [Circle.coe_exp, Complex.exp_mul_I]
    push_cast
    ring
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul_eq_one_sub (θ / 2)
    rwa [show 2 * (θ / 2) = θ by ring] at h
  have hsq : (Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [Real.sin_sq θ, mul_pow, sq_abs, hcos]
    ring
  rw [hsplit, Complex.norm_add_mul_I, hsq, Real.sqrt_sq (by positivity)]

/-- **The chord formula for the unit circle**: two points of the circle at angles `a` and `b` are at
distance `2 * |sin ((a - b) / 2)|`.

The proof factors the unimodular `Circle.exp b` out of the difference, reducing to
`TauCeti.norm_circleExp_sub_one` at the angle `a - b`. -/
theorem dist_circleExp_eq_two_mul_abs_sin (a b : ℝ) :
    dist (Circle.exp a) (Circle.exp b) = 2 * |Real.sin ((a - b) / 2)| := by
  have hfactor : ((Circle.exp a : ℂ) - (Circle.exp b : ℂ)) =
      ((Circle.exp (a - b) : ℂ) - 1) * (Circle.exp b : ℂ) := by
    rw [show Circle.exp a = Circle.exp (a - b) * Circle.exp b by rw [← Circle.exp_add]; ring_nf,
      Circle.coe_mul]
    ring
  have hdist : dist (Circle.exp a) (Circle.exp b)
      = ‖(Circle.exp a : ℂ) - (Circle.exp b : ℂ)‖ := by
    rw [← Complex.dist_eq]
    rfl
  rw [hdist, hfactor, norm_mul, Circle.norm_coe, mul_one, norm_circleExp_sub_one]

/-- **The chord is at most the arc**: `Circle.exp` is `1`-Lipschitz, by `|sin| ≤ |·|` applied to the
chord formula `TauCeti.dist_circleExp_eq_two_mul_abs_sin`. -/
theorem dist_circleExp_le (a b : ℝ) : dist (Circle.exp a) (Circle.exp b) ≤ |a - b| := by
  have h : |Real.sin ((a - b) / 2)| ≤ |a - b| / 2 := by
    simpa [abs_div] using Real.abs_sin_le_abs (x := (a - b) / 2)
  rw [dist_circleExp_eq_two_mul_abs_sin]
  linarith

/-- An arc of the circle spanning the angles `Set.Ioo a b` has diameter at most `b - a`, by the
`1`-Lipschitz bound `TauCeti.dist_circleExp_le`. -/
theorem diam_circleExp_image_Ioo_le {a b : ℝ} (hab : a ≤ b) :
    Metric.diam (Circle.exp '' Ioo a b) ≤ b - a := by
  refine Metric.diam_le_of_forall_dist_le (by linarith) ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (dist_circleExp_le x y).trans
    (abs_le.2 ⟨by linarith [hx.1, hx.2, hy.1, hy.2], by linarith [hx.1, hx.2, hy.1, hy.2]⟩)

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
    rw [hrw, dist_circleExp_eq_two_mul_abs_sin,
      show (Complex.arg (x : ℂ) - (Circle.angleDiff x y + Complex.arg (x : ℂ))) / 2
        = -(Circle.angleDiff x y / 2) by ring,
      Real.sin_neg, abs_neg,
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
    rw [hdist, ← hs, show π / 2 * (2 * Real.sin (s / 2)) = π * Real.sin (s / 2) by ring]
    exact hmul
  rcases le_total (Circle.angleDiff x y) π with hle | hle
  · exact (min_le_left _ _).trans (key _ hpos hle rfl)
  · refine (min_le_right _ _).trans (key _ (by linarith) (by linarith) ?_)
    rw [show Circle.angleDiff y x / 2 = π - Circle.angleDiff x y / 2 by linarith, Real.sin_pi_sub]

/-! ## Cutting the circle into a short arc and a long one -/

/-- The two open arcs of angles cut out by `a` and `t + a`, for `0 < t < 2 * π`, cover the circle
minus the two points `Circle.exp a` and `Circle.exp (t + a)`.

Both inclusions come from injectivity of `Circle.exp` on a half-open period
(`Circle.exp_injOn_Ioc`), together with the fact that such a period exhausts the circle
(`Function.Periodic.image_Ioc`). -/
private lemma circleExp_image_Ioo_union_eq_compl_pair {a t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 2 * π) :
    Circle.exp '' Ioo a (t + a) ∪ Circle.exp '' Ioo (t + a) (a + 2 * π) =
      ({Circle.exp a, Circle.exp (t + a)} : Set Circle)ᶜ := by
  have hinj : InjOn Circle.exp (Ioc a (a + 2 * π)) := Circle.exp_injOn_Ioc (by linarith)
  have hper : Circle.exp '' Ioc a (a + 2 * π) = univ := by
    rw [Circle.periodic_exp.image_Ioc Real.two_pi_pos, Circle.exp_surjective.range_eq]
  have hmem : ∀ s : ℝ, s ∈ Ioo a (a + 2 * π) → s ≠ t + a →
      Circle.exp s ∉ ({Circle.exp a, Circle.exp (t + a)} : Set Circle) := by
    rintro s ⟨hs₀, hs₁⟩ hst (h | h)
    · rw [show Circle.exp a = Circle.exp (a + 2 * π) by simp] at h
      exact absurd (hinj ⟨hs₀, hs₁.le⟩ ⟨by linarith, le_rfl⟩ h) (by linarith)
    · exact hst (hinj ⟨hs₀, hs₁.le⟩ ⟨by linarith, by linarith⟩ h)
  refine subset_antisymm ?_ fun u hu => ?_
  · rintro _ (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact hmem s ⟨hs.1, by linarith [hs.2]⟩ (by linarith [hs.2])
    · exact hmem s ⟨by linarith [hs.1], hs.2⟩ (by linarith [hs.1])
  · obtain ⟨s, hs, rfl⟩ : u ∈ Circle.exp '' Ioc a (a + 2 * π) := hper ▸ mem_univ u
    have hne : s ≠ a + 2 * π := by
      rintro rfl
      exact hu (Or.inl (by simp))
    have hne' : s ≠ t + a := by
      rintro rfl
      exact hu (Or.inr rfl)
    rcases lt_trichotomy s (t + a) with h | h | h
    · exact Or.inl ⟨s, ⟨hs.1, h⟩, rfl⟩
    · exact absurd h hne'
    · exact Or.inr ⟨s, ⟨h, lt_of_le_of_ne hs.2 hne⟩, rfl⟩

/-- **Two distinct points cut the circle into a short arc and a long one.** The complement of
`{z, w}` is the union of two preconnected sets, the first of diameter at most `π / 2 * dist z w`.

The two sets are the two arcs between `z` and `w`, presented as `Circle.exp` images of intervals of
angles so that `TauCeti.diam_circleExp_image_Ioo_le` bounds their diameters by the corresponding arc
lengths; which of the two is named first depends on which of `Circle.angleDiff z w` and
`Circle.angleDiff w z` is the smaller, and `TauCeti.min_angleDiff_le_dist` bounds that one by the
chord. -/
theorem exists_isPreconnected_union_eq_compl_pair_circle_diam_le {z w : Circle} (hzw : z ≠ w) :
    ∃ P Q : Set Circle, IsPreconnected P ∧ IsPreconnected Q ∧
      P ∪ Q = ({z, w} : Set Circle)ᶜ ∧ Metric.diam P ≤ π / 2 * dist z w := by
  set a := Complex.arg (z : ℂ) with ha
  set t := Circle.angleDiff z w with ht
  have ht₀ : 0 < t := Circle.angleDiff_pos hzw
  have ht₁ : t < 2 * π := Circle.angleDiff_lt_two_pi z w
  have hsum : t + Circle.angleDiff w z = 2 * π := Circle.angleDiff_add_angleDiff hzw
  have hz : Circle.exp a = z := Circle.exp_arg z
  have hw : Circle.exp (t + a) = w := by
    rw [Circle.exp_add, ha, Circle.exp_arg, ht, Circle.exp_angleDiff_mul]
  have hunion := circleExp_image_Ioo_union_eq_compl_pair (a := a) ht₀ ht₁
  rw [hz, hw] at hunion
  have hPc : IsPreconnected (Circle.exp '' Ioo a (t + a)) :=
    isPreconnected_Ioo.image _ Circle.exp.continuous.continuousOn
  have hQc : IsPreconnected (Circle.exp '' Ioo (t + a) (a + 2 * π)) :=
    isPreconnected_Ioo.image _ Circle.exp.continuous.continuousOn
  have hP : Metric.diam (Circle.exp '' Ioo a (t + a)) ≤ t := by
    simpa using diam_circleExp_image_Ioo_le (a := a) (b := t + a) (by linarith)
  have hQ : Metric.diam (Circle.exp '' Ioo (t + a) (a + 2 * π)) ≤ Circle.angleDiff w z := by
    have := diam_circleExp_image_Ioo_le (a := t + a) (b := a + 2 * π) (by linarith)
    linarith
  have hmin := min_angleDiff_le_dist z w
  rcases le_total t (Circle.angleDiff w z) with hle | hle
  · refine ⟨_, _, hPc, hQc, hunion, hP.trans ?_⟩
    rw [← ht] at hmin
    exact (le_min_iff.mpr ⟨le_rfl, hle⟩).trans hmin
  · refine ⟨_, _, hQc, hPc, by rw [union_comm]; exact hunion, hQ.trans ?_⟩
    rw [← ht] at hmin
    exact (le_min_iff.mpr ⟨hle, le_rfl⟩).trans hmin

/-! ## Cutting a Jordan curve -/

variable {X : Type*} [PseudoMetricSpace X] {C : Set X} {ε : ℝ}

/-- **Two nearby points cut a small arc off a Jordan curve.** For every `ε > 0` there is a `δ > 0`
with the following property: if `p` and `q` are two distinct points of a Jordan curve `C` at
distance less than `δ`, then in any splitting of `C \ {p, q}` into two disjoint pieces `A` and `B`
that separate it — that is, such that every preconnected subset of `C \ {p, q}` lies in one of
them — one of the two pieces has diameter at most `ε`.

The splitting is the one `TauCeti.IsJordanCurve.exists_isPathConnected_union_eq_sdiff_pair`
produces, and the hypotheses here are exactly its conclusion, so that the statement constrains that
cutting without having to reproduce it; `TauCeti.IsJordanCurve.exists_pos_forall_exists_diam_le`
records the combination.

The proof transports `TauCeti.exists_isPreconnected_union_eq_compl_pair_circle_diam_le` along the
parametrization of `C` by the circle, using its uniform continuity in one direction to make the
parameters of `p` and `q` close and in the other to make the image of the short arc of parameters
have small diameter. The transported pieces are preconnected subsets of `C \ {p, q}`, so each lies
in `A` or in `B`; if both land in the same one, the other is empty, and otherwise the one containing
the short piece is *contained* in it, because the pieces cover `C \ {p, q}` while `A` and `B` are
disjoint. -/
theorem IsJordanCurve.exists_pos_forall_diam_le (h : IsJordanCurve C) (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃p : X⦄, p ∈ C → ∀ ⦃q : X⦄, q ∈ C → p ≠ q → dist p q < δ →
      ∀ A B : Set X, A ∪ B = C \ {p, q} → Disjoint A B →
        (∀ ⦃S : Set X⦄, S ⊆ C \ {p, q} → IsPreconnected S → S ⊆ A ∨ S ⊆ B) →
        Metric.diam A ≤ ε ∨ Metric.diam B ≤ ε := by
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp h.isCompact
  set g : Circle → X := fun u => ((e.symm u : C) : X) with hg
  have hgc : Continuous g := continuous_subtype_val.comp e.symm.continuous
  have hginj : Function.Injective g := Subtype.val_injective.comp e.symm.injective
  have hgrange : range g = C := by
    refine subset_antisymm ?_ fun x hx => ⟨e ⟨x, hx⟩, by simp [hg]⟩
    rintro _ ⟨u, rfl⟩
    exact (e.symm u).2
  -- Uniform continuity of the parametrization turns short arcs into sets of small diameter.
  obtain ⟨η, hη₀, hη⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hgc) ε hε
  -- Uniform continuity of its inverse turns nearby points into nearby parameters.
  obtain ⟨δ, hδ₀, hδ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous e.continuous) (2 / π * η) (by positivity)
  refine ⟨δ, hδ₀, fun p hp q hq hpq hpqδ A B hAB hdisj hsep => ?_⟩
  set z := e ⟨p, hp⟩ with hzdef
  set w := e ⟨q, hq⟩ with hwdef
  have hzw : z ≠ w := fun hh => hpq (congrArg Subtype.val (e.injective hh))
  have hchord : π / 2 * dist z w < η := by
    have hd : dist z w < 2 / π * η := hδ (by simpa [Subtype.dist_eq] using hpqδ)
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
    rw [image_insert_eq, image_singleton, hg]
    simp [hzdef, hwdef]
  have hPsub : g '' P₀ ⊆ C \ {p, q} := himg ▸ subset_union_left
  have hQsub : g '' Q₀ ⊆ C \ {p, q} := himg ▸ subset_union_right
  have hPdiam : Metric.diam (g '' P₀) ≤ ε := by
    refine Metric.diam_le_of_forall_dist_le hε.le ?_
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have hbdd : Bornology.IsBounded P₀ := (isCompact_univ (X := Circle)).isBounded.subset
      (subset_univ _)
    exact (hη (lt_of_le_of_lt (Metric.dist_le_diam_of_mem hbdd hu hv)
      (lt_of_le_of_lt hP₀d hchord))).le
  have hCbdd : Bornology.IsBounded (C \ {p, q}) := h.isCompact.isBounded.subset sdiff_subset
  -- Locate each transported arc inside `A` or inside `B`.
  rcases hsep hPsub (hP₀c.image _ hgc.continuousOn) with hPA | hPB
  · rcases hsep hQsub (hQ₀c.image _ hgc.continuousOn) with hQA | hQB
    · refine Or.inr ?_
      have hBempty : B = ∅ := by
        refine eq_empty_of_subset_empty fun x hx => ?_
        have : x ∈ A := by
          rcases (himg ▸ hAB ▸ mem_union_right A hx : x ∈ g '' P₀ ∪ g '' Q₀) with hxP | hxQ
          · exact hPA hxP
          · exact hQA hxQ
        exact hdisj.le_bot ⟨this, hx⟩
      simp [hBempty, hε.le]
    · refine Or.inl (le_trans (Metric.diam_mono ?_ (hCbdd.subset hPsub)) hPdiam)
      intro x hx
      rcases (himg ▸ hAB ▸ mem_union_left B hx : x ∈ g '' P₀ ∪ g '' Q₀) with hxP | hxQ
      · exact hxP
      · exact absurd (hdisj.le_bot ⟨hx, hQB hxQ⟩) id
  · rcases hsep hQsub (hQ₀c.image _ hgc.continuousOn) with hQA | hQB
    · refine Or.inr (le_trans (Metric.diam_mono ?_ (hCbdd.subset hPsub)) hPdiam)
      intro x hx
      rcases (himg ▸ hAB ▸ mem_union_right A hx : x ∈ g '' P₀ ∪ g '' Q₀) with hxP | hxQ
      · exact hxP
      · exact absurd (hdisj.le_bot ⟨hQA hxQ, hx⟩) id
    · refine Or.inl ?_
      have hAempty : A = ∅ := by
        refine eq_empty_of_subset_empty fun x hx => ?_
        have : x ∈ B := by
          rcases (himg ▸ hAB ▸ mem_union_left B hx : x ∈ g '' P₀ ∪ g '' Q₀) with hxP | hxQ
          · exact hPB hxP
          · exact hQB hxQ
        exact hdisj.le_bot ⟨hx, this⟩
      simp [hAempty, hε.le]

/-- **Two nearby points cut a small arc off a Jordan curve**, in packaged form: for every `ε > 0`
there is a `δ > 0` such that two distinct points of a Jordan curve at distance less than `δ` cut it
into two arcs, the first of which has diameter at most `ε`.

This is `TauCeti.IsJordanCurve.exists_isPathConnected_union_eq_sdiff_pair` together with
`TauCeti.IsJordanCurve.exists_pos_forall_diam_le`, the two arcs being swapped when it is the second
that comes out small. It is the form the Carathéodory boundary argument consumes: the small arc,
together with the crosscut whose endpoints are `p` and `q`, bounds the region that has to be shown
to have small diameter. -/
theorem IsJordanCurve.exists_pos_forall_exists_diam_le (h : IsJordanCurve C) (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃p : X⦄, p ∈ C → ∀ ⦃q : X⦄, q ∈ C → p ≠ q → dist p q < δ →
      ∃ A B : Set X, IsPathConnected A ∧ IsPathConnected B ∧ Disjoint A B ∧
        A ∪ B = C \ {p, q} ∧
        (∀ ⦃S : Set X⦄, S ⊆ C \ {p, q} → IsPreconnected S → S ⊆ A ∨ S ⊆ B) ∧
        Metric.diam A ≤ ε := by
  obtain ⟨δ, hδ₀, hδ⟩ := h.exists_pos_forall_diam_le hε
  refine ⟨δ, hδ₀, fun p hp q hq hpq hpqδ => ?_⟩
  obtain ⟨A, B, hAc, hBc, hdisj, hunion, hsep⟩ :=
    h.exists_isPathConnected_union_eq_sdiff_pair hp hq hpq
  rcases hδ hp hq hpq hpqδ A B hunion hdisj hsep with hA | hB
  · exact ⟨A, B, hAc, hBc, hdisj, hunion, hsep, hA⟩
  · exact ⟨B, A, hBc, hAc, hdisj.symm, by rw [union_comm]; exact hunion,
      fun S hS hSc => (hsep hS hSc).symm, hB⟩

end TauCeti
