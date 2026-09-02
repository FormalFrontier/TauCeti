/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Circle.Arc
public import TauCeti.Topology.Circle.Metric
public import TauCeti.Topology.JordanCurve.Separation
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

Everything is transported from the model curve, and the transport is quantitative, so the comparison
of the chord with the arc on the circle comes first. It is not specific to Jordan curves and lives
in `TauCeti/Topology/Circle/Metric.lean`: the chord is at most the arc
(`TauCeti.diam_circleExp_image_Icc_le`), and conversely the *shorter* of the two arc lengths
`Circle.angleDiff` separating two points is at most `π / 2` times their chord
(`TauCeti.min_angleDiff_le_pi_div_two_mul_dist`). The converse bound is the one that matters here:
it is what turns a hypothesis about the ambient distance into a bound on an arc.

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
`TauCeti/Topology/JordanCurve/Basic.lean` at once: one converts "the two points are close in
`X`" into "their parameters are close on the circle", the other converts "the parameter arc is
short" into "its image has small diameter". That transport is carried out in one step, which
*builds* a small arc. The main statement below then only has to *locate* that arc inside an
arbitrary separating decomposition; that part is set-theoretic except for its closing step, which
compares diameters and so still needs the curve to be bounded.

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

## Joining the two points by an injective path

A consumer that *joins* the small arc to another one — gluing two arcs along their two common
endpoints into a closed curve — needs it as a path rather than as a set, and needs that path
injective, since a path-connected set carries paths with arbitrary repetitions. The last two
statements below supply exactly that, and nothing more: an injective path with the two prescribed
endpoints, running inside the curve, whose range is of small diameter. They relate its range to
neither of the two arcs of the cut above.

Their witness on the circle is Mathlib's arc `Circle.path`, injective by
`Circle.path_injective_of_ne` and reversed by `Path.symm` when the counterclockwise direction is the
long way round; transporting it along the parametrization, which is injective and continuous, gives
an injective path along the curve. Its diameter is bounded by the same two uniform continuities,
which are recorded here once and spent by both transports.

## Main results

* `TauCeti.exists_isPreconnected_union_eq_compl_pair_circle_diam_le` — two distinct points cut the
  circle into two preconnected arcs, the first of which is of diameter at most `π / 2` times their
  distance even after the two points are put back, and
  `TauCeti.exists_path_injective_diam_range_le_circle` — two distinct points of the circle are the
  endpoints of an injective path whose range has diameter at most `π / 2` times their distance.
* `TauCeti.IsJordanCurve.exists_pos_forall_diam_le` — **the main statement**: for every `ε > 0`
  there is a `δ > 0` such that two distinct points `p`, `q` of a Jordan curve at distance less than
  `δ` cut it into two arcs one of which has diameter at most `ε` together with `p` and `q`.
* `TauCeti.IsJordanCurve.exists_pos_forall_exists_diam_le` — the same packaged with the cutting
  itself, producing the two arcs with the small one named first.
* `TauCeti.IsJordanCurve.exists_pos_forall_exists_path_injective_diam_le` — two nearby points of a
  Jordan curve are the endpoints of an injective path along it whose range is of diameter at
  most `ε`.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
-/

public section

namespace TauCeti

open Metric Set Topology

open scoped Real

/-! ## Cutting the circle into a short arc and a long one -/

/-- **Two distinct points cut the circle into a short arc and a long one.** The complement of
`{z, w}` is the union of two preconnected sets, the first of which stays of diameter at most
`π / 2 * dist z w` even after the two cut points are put back: it is `P ∪ {z, w}`, the *closed*
short arc, that is bounded. -/
theorem exists_isPreconnected_union_eq_compl_pair_circle_diam_le {z w : Circle} (hzw : z ≠ w) :
    ∃ P Q : Set Circle, IsPreconnected P ∧ IsPreconnected Q ∧
      P ∪ Q = ({z, w} : Set Circle)ᶜ ∧ Metric.diam (P ∪ {z, w}) ≤ π / 2 * dist z w := by
  -- The two pieces are Mathlib's open arcs, which cover the complement of `{z, w}`.
  have hunion : Circle.path z w '' Ioo 0 1 ∪ Circle.path w z '' Ioo 0 1 =
      ({z, w} : Set Circle)ᶜ := by
    rw [← Circle.compl_range_path hzw.symm, ← Circle.compl_range_path hzw, ← compl_inter,
      Circle.range_path_inter_range_path hzw.symm, pair_comm]
  have hpre : ∀ x y : Circle, IsPreconnected (Circle.path x y '' Ioo 0 1) := fun x y =>
    isPreconnected_Ioo.image _ (Circle.path x y).continuous.continuousOn
  -- Putting the endpoints back — they are the values of the path at `0` and `1` — lands inside the
  -- closed arc `Circle.range_path`, whose diameter is at most its angle.
  have hdiam : ∀ x y : Circle,
      Metric.diam (Circle.path x y '' Ioo 0 1 ∪ {x, y}) ≤ Circle.angleDiff x y := fun x y => by
    have hsub : Circle.path x y '' Ioo 0 1 ∪ {x, y} ⊆ range (Circle.path x y) :=
      union_subset (image_subset_range _ _)
        (insert_subset ⟨0, (Circle.path x y).source⟩
          (singleton_subset_iff.2 ⟨1, (Circle.path x y).target⟩))
    exact (Metric.diam_mono hsub
      (isCompact_range (Circle.path x y).continuous).isBounded).trans (diam_range_circlePath_le x y)
  have hmin := min_angleDiff_le_pi_div_two_mul_dist z w
  -- Name first whichever of the two arcs is the shorter; its length is bounded by the chord.
  rcases le_total (Circle.angleDiff z w) (Circle.angleDiff w z) with hle | hle
  · exact ⟨_, _, hpre z w, hpre w z, hunion,
      (hdiam z w).trans ((le_min_iff.mpr ⟨le_rfl, hle⟩).trans hmin)⟩
  · refine ⟨_, _, hpre w z, hpre z w, by rw [union_comm]; exact hunion, ?_⟩
    rw [pair_comm z w]
    exact (hdiam w z).trans ((le_min_iff.mpr ⟨hle, le_rfl⟩).trans hmin)

/-- **Two points of the circle are joined by a short injective path.** Two distinct points of the
circle are the endpoints of an injective path whose range has diameter at most `π / 2` times their
distance.

The witness is Mathlib's arc `Circle.path z w`, injective by `Circle.path_injective_of_ne`, taken in
the direction in which `Circle.angleDiff` is smaller, and its reverse otherwise; reversing changes
neither the range (`Path.symm_range`) nor injectivity. Only the endpoints, the injectivity and the
diameter bound are recorded: nothing is stated relating the range to either piece of the cut of
`TauCeti.exists_isPreconnected_union_eq_compl_pair_circle_diam_le`.

The diameter bound is `TauCeti.diam_range_circlePath_le` — the arc bounds the chords across it —
fed the comparison `TauCeti.min_angleDiff_le_pi_div_two_mul_dist` of the shorter arc with the chord,
which is the comparison that bounds the short arc there too. -/
theorem exists_path_injective_diam_range_le_circle {z w : Circle} (hzw : z ≠ w) :
    ∃ γ : Path z w, Function.Injective γ ∧ Metric.diam (range γ) ≤ π / 2 * dist z w := by
  have hmin := min_angleDiff_le_pi_div_two_mul_dist z w
  rcases le_total (Circle.angleDiff z w) (Circle.angleDiff w z) with hle | hle
  · exact ⟨Circle.path z w, Circle.path_injective_of_ne hzw,
      (diam_range_circlePath_le z w).trans ((le_min_iff.mpr ⟨le_rfl, hle⟩).trans hmin)⟩
  · refine ⟨(Circle.path w z).symm, ?_, ?_⟩
    · intro a b hab
      simp only [Path.symm_apply, Function.comp_apply] at hab
      exact unitInterval.symm_bijective.injective (Circle.path_injective_of_ne hzw.symm hab)
    · rw [Path.symm_range]
      exact (diam_range_circlePath_le w z).trans ((le_min_iff.mpr ⟨hle, le_rfl⟩).trans hmin)

/-- The scaling shared by the two `δ`-`η` forms below: a distance smaller than `2 / π * η` has
`π / 2` times it smaller than `η`, which is how a bound stated as a multiple of the chord becomes a
bound below a prescribed tolerance. -/
private lemma pi_div_two_mul_lt {η d : ℝ} (hη : 0 < η) (hd : d < 2 / π * η) : π / 2 * d < η := by
  have hπ : 0 < π := Real.pi_pos
  calc π / 2 * d < π / 2 * (2 / π * η) := mul_lt_mul_of_pos_left hd (by positivity)
    _ = η := by field_simp

/-- **Two nearby points cut a short arc off the circle**: the `δ`-`η` form of
`TauCeti.exists_isPreconnected_union_eq_compl_pair_circle_diam_le`, in which the bound on the
diameter of the short arc no longer mentions the distance of the two cut points. This is the form
the transport to a Jordan curve consumes, since what arrives there is a hypothesis of the shape
`dist z w < δ`. -/
private theorem exists_pos_forall_isPreconnected_union_eq_compl_pair_circle_diam_lt {η : ℝ}
    (hη : 0 < η) :
    ∃ δ > 0, ∀ ⦃z w : Circle⦄, z ≠ w → dist z w < δ →
      ∃ P Q : Set Circle, IsPreconnected P ∧ IsPreconnected Q ∧
        P ∪ Q = ({z, w} : Set Circle)ᶜ ∧ Metric.diam (P ∪ {z, w}) < η := by
  have hπ : 0 < π := Real.pi_pos
  refine ⟨2 / π * η, by positivity, fun z w hzw hd => ?_⟩
  obtain ⟨P, Q, hPc, hQc, hunion, hPd⟩ :=
    exists_isPreconnected_union_eq_compl_pair_circle_diam_le hzw
  exact ⟨P, Q, hPc, hQc, hunion, hPd.trans_lt (pi_div_two_mul_lt hη hd)⟩

/-- **Two nearby points of the circle are joined by a short injective path**: the `δ`-`η` form of
`TauCeti.exists_path_injective_diam_range_le_circle`, in the shape the transport to a Jordan curve
consumes. -/
private theorem exists_pos_forall_exists_path_injective_diam_range_lt_circle {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ ⦃z w : Circle⦄, z ≠ w → dist z w < δ →
      ∃ γ : Path z w, Function.Injective γ ∧ Metric.diam (range γ) < η := by
  have hπ : 0 < π := Real.pi_pos
  refine ⟨2 / π * η, by positivity, fun z w hzw hd => ?_⟩
  obtain ⟨γ, hinj, hdiam⟩ := exists_path_injective_diam_range_le_circle hzw
  exact ⟨γ, hinj, hdiam.trans_lt (pi_div_two_mul_lt hη hd)⟩

/-! ## Cutting a Jordan curve -/

variable {X : Type*} [PseudoMetricSpace X] {C : Set X} {ε : ℝ}

/-- **Uniform continuity of the parametrization**, in the form the two transports below spend it:
for every `ε > 0` there is an `η > 0` such that a set of parameters of diameter less than `η` is
carried by `TauCeti.jordanParam e` to a set of diameter at most `ε`.

The circle is compact, so the parametrization is uniformly continuous, and
`Metric.dist_le_diam_of_mem` — the circle being bounded — reads the hypothesis on the diameter as a
bound on the distance between any two of the parameters. -/
private theorem exists_pos_forall_diam_image_jordanParam_le (e : C ≃ₜ Circle) (hε : 0 < ε) :
    ∃ η > 0, ∀ s : Set Circle, Metric.diam s < η → Metric.diam (jordanParam e '' s) ≤ ε := by
  obtain ⟨η, hη₀, hη⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous (continuous_jordanParam e)) ε hε
  refine ⟨η, hη₀, fun s hs => Metric.diam_le_of_forall_dist_le hε.le ?_⟩
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  exact (hη ((Metric.dist_le_diam_of_mem
    ((isCompact_univ (X := Circle)).isBounded.subset (subset_univ _)) hu hv).trans_lt hs)).le

/-- **Uniform continuity of the inverse of the parametrization**, in the form the two transports
below spend it: for every `δ₀ > 0` there is a `δ > 0` such that two points of the curve at distance
less than `δ` are named by parameters at distance less than `δ₀`. The curve is compact, being
homeomorphic to the circle. -/
private theorem exists_pos_forall_dist_apply_lt (e : C ≃ₜ Circle) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ δ > 0, ∀ p (hp : p ∈ C), ∀ q (hq : q ∈ C), dist p q < δ →
      dist (e ⟨p, hp⟩) (e ⟨q, hq⟩) < δ₀ := by
  have : CompactSpace C := e.symm.compactSpace
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous e.continuous) δ₀ hδ₀
  exact ⟨δ, hδpos, fun p hp q hq hpq => hδ (by simpa [Subtype.dist_eq] using hpq)⟩

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

/-- **Two nearby points cut a small arc off a Jordan curve**, in the form that *builds* the small
arc: for every `ε > 0` there is a `δ > 0` such that if `p` and `q` are two distinct points of the
curve at distance less than `δ`, then `C \ {p, q}` is covered by two preconnected sets, the first of
which has diameter at most `ε` once the two cut points are put back.

This is the analytic half of `TauCeti.IsJordanCurve.exists_pos_forall_diam_le`: it transports the
cut of the circle along the parametrization, running both uniform continuities at once. The other
half — passing from this one cover to an arbitrary separating decomposition — is set-theoretic
apart from its closing diameter comparison, which still uses boundedness of the curve. Only the
cover is recorded, not the disjointness of the two pieces, since that is all the identification
below consumes. -/
private theorem IsJordanCurve.exists_pos_forall_exists_isPreconnected_diam_union_pair_le
    (h : IsJordanCurve C) (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃p : X⦄, p ∈ C → ∀ ⦃q : X⦄, q ∈ C → p ≠ q → dist p q < δ →
      ∃ P Q : Set X, IsPreconnected P ∧ IsPreconnected Q ∧ P ∪ Q = C \ {p, q} ∧
        Metric.diam (P ∪ {p, q}) ≤ ε := by
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  set g := jordanParam e
  have hgc : Continuous g := continuous_jordanParam e
  have hginj : Function.Injective g := jordanParam_injective e
  have hgrange : range g = C := range_jordanParam e
  -- Uniform continuity of the parametrization turns short arcs into sets of small diameter.
  obtain ⟨η, hη₀, hη⟩ := exists_pos_forall_diam_image_jordanParam_le e hε
  obtain ⟨δ₀, hδ₀, hcut⟩ :=
    exists_pos_forall_isPreconnected_union_eq_compl_pair_circle_diam_lt hη₀
  -- Uniform continuity of its inverse turns nearby points into nearby parameters.
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_forall_dist_apply_lt e hδ₀
  refine ⟨δ, hδpos, fun p hp q hq hpq hpqδ => ?_⟩
  set z := e ⟨p, hp⟩
  set w := e ⟨q, hq⟩
  have hgz : g z = p := jordanParam_apply_apply e hp
  have hgw : g w = q := jordanParam_apply_apply e hq
  have hzw : z ≠ w := fun hh => hpq (congrArg Subtype.val (e.injective hh))
  obtain ⟨P, Q, hPc, hQc, hunion, hPd⟩ := hcut hzw (hδ p hp q hq hpqδ)
  -- The closed short arc downstairs is the image of the closed short arc of parameters.
  have hclosed : g '' (P ∪ {z, w}) = g '' P ∪ {p, q} := by
    rw [image_union, image_insert_eq, image_singleton, hgz, hgw]
  have himg : g '' P ∪ g '' Q = C \ {p, q} := by
    rw [← image_union, hunion, Set.image_compl_eq_range_sdiff_image hginj, hgrange,
      image_insert_eq, image_singleton, hgz, hgw]
  exact ⟨g '' P, g '' Q, hPc.image _ hgc.continuousOn, hQc.image _ hgc.continuousOn,
    himg, hclosed ▸ hη _ hPd⟩

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

The hypotheses on `A` and `B` are exactly the conclusion of
`TauCeti.IsJordanCurve.exists_isPathConnected_union_eq_sdiff_pair`, so the statement constrains that
cutting without having to reproduce it; `TauCeti.IsJordanCurve.exists_pos_forall_exists_diam_le`
records the combination. -/
theorem IsJordanCurve.exists_pos_forall_diam_le (h : IsJordanCurve C) (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃p : X⦄, p ∈ C → ∀ ⦃q : X⦄, q ∈ C → p ≠ q → dist p q < δ →
      ∀ A B : Set X, A ∪ B = C \ {p, q} → Disjoint A B →
        (∀ ⦃S : Set X⦄, S ⊆ C \ {p, q} → IsPreconnected S → S ⊆ A ∨ S ⊆ B) →
        Metric.diam (A ∪ {p, q}) ≤ ε ∨ Metric.diam (B ∪ {p, q}) ≤ ε := by
  obtain ⟨δ, hδ₀, hδ⟩ := h.exists_pos_forall_exists_isPreconnected_diam_union_pair_le hε
  -- `δ ≤ ε` so that the two cut points alone are already of diameter at most `ε`.
  refine ⟨min δ ε, lt_min hδ₀ hε, fun p hp q hq hpq hpqδ A B hAB hdisj hsep => ?_⟩
  have hpqε : dist p q ≤ ε := (hpqδ.trans_le (min_le_right _ _)).le
  obtain ⟨P, Q, hPc, hQc, hunion, hPd⟩ := hδ hp hq hpq (hpqδ.trans_le (min_le_left _ _))
  have hPsub : P ⊆ C \ {p, q} := hunion ▸ subset_union_left
  have hQsub : Q ⊆ C \ {p, q} := hunion ▸ subset_union_right
  have hPbdd : Bornology.IsBounded (P ∪ {p, q}) :=
    h.isCompact.isBounded.subset (union_subset (hPsub.trans sdiff_subset)
      (insert_subset hp (singleton_subset_iff.2 hq)))
  -- The side containing the short arc either is contained in it, and so is small, or leaves the
  -- other side empty, and then only the two cut points are left.
  have hside : ∀ A' B' : Set X, A' ∪ B' = C \ {p, q} → Disjoint A' B' → P ⊆ A' →
      (Q ⊆ A' ∨ Q ⊆ B') →
      Metric.diam (A' ∪ {p, q}) ≤ ε ∨ Metric.diam (B' ∪ {p, q}) ≤ ε := by
    intro A' B' hcover hd hP hQ
    rcases subset_or_eq_empty_of_union_eq_union (hunion.trans hcover.symm) hd hP hQ with hsub | hemp
    · exact Or.inl ((Metric.diam_mono (union_subset_union_left _ hsub) hPbdd).trans hPd)
    · rw [hemp, empty_union, Metric.diam_pair]
      exact Or.inr hpqε
  -- Locate each arc inside `A` or inside `B`, and apply that symmetrically.
  have hQ := hsep hQsub hQc
  rcases hsep hPsub hPc with hPA | hPB
  · exact hside A B hAB hdisj hPA hQ
  · exact (hside B A (by rw [union_comm]; exact hAB) hdisj.symm hPB hQ.symm).symm

/-- **Two nearby points cut a small arc off a Jordan curve**, in packaged form: for every `ε > 0`
there is a `δ > 0` such that two distinct points of a Jordan curve at distance less than `δ` cut it
into two arcs, the first of which has diameter at most `ε` *once its two endpoints are put back*,
that is, `A ∪ {p, q}` is small.

This is the form the Carathéodory boundary argument consumes: the small *closed* arc `A ∪ {p, q}`,
together with the crosscut whose endpoints are `p` and `q`, bounds the region that has to be shown
to have small diameter, so the endpoints must be inside the set that is bounded. For the form that
instead constrains an arbitrary separating decomposition, see
`TauCeti.IsJordanCurve.exists_pos_forall_diam_le`. -/
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

/-! ## Joining the two points by an injective path -/

/-- **Two nearby points of a Jordan curve are joined by a small injective path along it.** For every
`ε > 0` there is a `δ > 0` such that two distinct points `p`, `q` of a Jordan curve `C` at distance
less than `δ` are the endpoints of an injective path whose range lies on `C` and has diameter at
most `ε`.

Injectivity is what a consumer joining this path to a second one needs — gluing two arcs along their
common endpoints into a closed curve is a statement about paths — and it is not available from the
path-connectedness of the arcs of `TauCeti.IsJordanCurve.exists_pos_forall_exists_diam_le`, which
yields a path but no control of its repetitions.

The transport is that of
`TauCeti.IsJordanCurve.exists_pos_forall_exists_isPreconnected_diam_union_pair_le`, run on the
circle statement `TauCeti.exists_path_injective_diam_range_le_circle` instead of on the cut into two
arcs: the parametrization `TauCeti.jordanParam e` is injective and continuous, so it carries the
injective path of parameters to an injective path along `C`, and both uniform continuities are spent
exactly as before.

Nothing is claimed here about the two arcs of `C \ {p, q}`: neither which of them the path
traverses, nor that its range is one of them together with the endpoints. What the conclusion offers
is a subset of `C` containing `p` and `q`, of diameter at most `ε`, traversed injectively. -/
theorem IsJordanCurve.exists_pos_forall_exists_path_injective_diam_le (h : IsJordanCurve C)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ ⦃p : X⦄, p ∈ C → ∀ ⦃q : X⦄, q ∈ C → p ≠ q → dist p q < δ →
      ∃ γ : Path p q, Function.Injective γ ∧ range γ ⊆ C ∧ Metric.diam (range γ) ≤ ε := by
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  obtain ⟨η, hη₀, hη⟩ := exists_pos_forall_diam_image_jordanParam_le e hε
  obtain ⟨δ₀, hδ₀, hcut⟩ := exists_pos_forall_exists_path_injective_diam_range_lt_circle hη₀
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_forall_dist_apply_lt e hδ₀
  refine ⟨δ, hδpos, fun p hp q hq hpq hpqδ => ?_⟩
  have hzw : e ⟨p, hp⟩ ≠ e ⟨q, hq⟩ := fun hh => hpq (congrArg Subtype.val (e.injective hh))
  obtain ⟨γ, hinj, hdiam⟩ := hcut hzw (hδ p hp q hq hpqδ)
  -- The path downstairs is the parametrization composed with the path of parameters.
  refine ⟨(γ.map (continuous_jordanParam e)).cast (jordanParam_apply_apply e hp).symm
    (jordanParam_apply_apply e hq).symm, ?_, ?_, ?_⟩ <;>
    rw [Path.cast_coe, Path.map_coe]
  · exact (jordanParam_injective e).comp hinj
  · rw [range_comp]
    exact (image_subset_range _ _).trans (range_jordanParam e).subset
  · rw [range_comp]
    exact hη _ hdiam

/-- **A Jordan curve has, near any of its points, a compact preconnected arc
missing that point whose complement lies in a given ball around it.**  The
compact arc `S` is the image of a closed circle arc under the Jordan
parametrization, chosen small enough that its complement `C \ S` — the open
window through `a` — stays inside `ball a r`.

`S` is built directly: parametrize `C` by `jordanParam e`, pick an angle
`θ₀` over `a`, and let `S` be the image of the closed arc of angles
`Icc (θ₀ + η) (θ₀ - η + 2π)`, compact and preconnected as a continuous image
of an interval; continuity at `θ₀` keeps its complement inside `ball a r`. -/
theorem IsJordanCurve.exists_isCompact_isPreconnected_notMem_sdiff_subset_ball
    (hJ : IsJordanCurve C) {a : X} (ha : a ∈ C) {r : ℝ} (hr : 0 < r) :
    ∃ S ⊆ C, IsCompact S ∧ IsPreconnected S ∧ a ∉ S ∧ C \ S ⊆ ball a r := by
  obtain ⟨e⟩ := isJordanCurve_iff.mp hJ
  set g : Circle → X := jordanParam e
  have hginj : Function.Injective g := jordanParam_injective e
  have hgrange : range g = C := range_jordanParam e
  have hgc : Continuous g := continuous_jordanParam e
  obtain ⟨u₀, hu₀⟩ : a ∈ range g := by rw [hgrange]; exact ha
  obtain ⟨θ₀, hθ₀⟩ := Circle.exp_surjective u₀
  have hga : g (Circle.exp θ₀) = a := by rw [hθ₀, hu₀]
  have hcont : ContinuousAt (fun θ : ℝ => g (Circle.exp θ)) θ₀ :=
    (hgc.comp Circle.exp.continuous).continuousAt
  obtain ⟨η₀, hη₀, hη⟩ := Metric.continuousAt_iff.mp hcont r hr
  set η : ℝ := min η₀ (π / 2)
  have hηpos : 0 < η := lt_min hη₀ (by positivity)
  have hηle : η ≤ π / 2 := min_le_right _ _
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  set K : Set Circle := Circle.exp '' Icc (θ₀ + η) (θ₀ - η + 2 * π)
  set S : Set X := g '' K
  have hSC : S ⊆ C := by rw [← hgrange]; exact image_subset_range _ _
  have hScompact : IsCompact S :=
    (isCompact_Icc.image Circle.exp.continuous).image hgc
  have hSpre : IsPreconnected S :=
    (isPreconnected_Icc.image _ Circle.exp.continuous.continuousOn).image _ hgc.continuousOn
  have hab : θ₀ + η ≤ θ₀ - η + 2 * π := by linarith [Real.pi_pos]
  have hlt : (θ₀ - η + 2 * π) - (θ₀ + η) < 2 * π := by linarith
  refine ⟨S, hSC, hScompact, hSpre, ?_, ?_⟩
  · rintro ⟨u, huK, hu⟩
    have : u = Circle.exp θ₀ := hginj (hu.trans hga.symm)
    subst this
    obtain ⟨θ, hθ, hθeq⟩ := huK
    have hnot : Circle.exp θ₀ ∈ (Circle.exp '' Icc (θ₀ + η) (θ₀ - η + 2 * π))ᶜ := by
      rw [compl_circleExp_image_Icc hab hlt]
      refine ⟨θ₀ + 2 * π, ⟨by linarith, by linarith⟩, ?_⟩
      rw [Circle.exp_add, Circle.exp_two_pi, mul_one]
    exact hnot ⟨θ, hθ, hθeq⟩
  · rintro z ⟨hzC, hzS⟩
    rw [← hgrange] at hzC
    obtain ⟨u, rfl⟩ := hzC
    have huK : u ∉ K := fun h => hzS ⟨u, h, rfl⟩
    have hu : u ∈ Circle.exp '' Ioo (θ₀ - η + 2 * π) (θ₀ + η + 2 * π) := by
      have huK' : u ∈ (Circle.exp '' Icc (θ₀ + η) (θ₀ - η + 2 * π))ᶜ := huK
      rwa [compl_circleExp_image_Icc hab hlt] at huK'
    obtain ⟨θ, hθ, rfl⟩ := hu
    have hshift : Circle.exp θ = Circle.exp (θ - 2 * π) := by
      have hθ2 : θ = (θ - 2 * π) + 2 * π := by ring
      conv_lhs => rw [hθ2]
      rw [Circle.exp_add, Circle.exp_two_pi, mul_one]
    rw [hshift, mem_ball, ← hga]
    apply hη
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hθ.1, hθ.2]

end TauCeti
