/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import TauCeti.Topology.FilledHull
import Mathlib.Analysis.LocallyConvex.Separation
-- `NormedSpace.toLocallyConvexSpace`, needed to apply `geometric_hahn_banach_point_closed`.
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# The width of a filled hull

The filled hull `TauCeti.filledHull K` — `K` together with the bounded connected components of its
complement — is defined in `TauCeti/Topology/FilledHull.lean`, where it needs only a topology and a
bornology. In a real normed space the one substantial fact is that filling does not make a set
wider:

> `TauCeti.filledHull_subset_closedConvexHull` — `filledHull K ⊆ closedConvexHull ℝ K`,

whence `TauCeti.diam_filledHull`: a set and its filled hull have the same diameter. The
mechanism is separation: a point `x` outside the closed convex hull of `K` is cut off
from it by a continuous linear functional (`geometric_hahn_banach_point_closed`), and the open
half-space `{y | φ y < u}` so produced is a convex — hence preconnected — subset of `Kᶜ` containing
`x`, and it is unbounded, running off to infinity along any direction on which `φ` is negative. So
the component of `x` in `Kᶜ` is unbounded and `x` is not in the filled hull. Nonemptiness of `K` is
needed only to know that `φ ≠ 0`; for `K = ∅` and a zero-dimensional space the convex-hull statement
is false, the hull then being everything and the convex hull empty. The diameter statements survive
that case unhypothesised, because `TauCeti.subsingleton_filledHull_empty` says `filledHull ∅` is
empty in a nontrivial space and a point in the zero space, of diameter `0` either way.

Because the width of a filled hull is controlled, so is that of anything inside it, and the shape
in which this is spent is `TauCeti.IsPreconnected.subset_filledHull`: a preconnected set disjoint
from `K` is trapped inside the filled hull as soon as it meets it. Together the two say that
*a connected set that a small `K` cuts off from infinity is itself small*, with no regularity asked
of `K`.

## Roadmap role

The filled hull is the vocabulary in which the open frontier item of layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md` is stated; see the roadmap section of
`TauCeti/Topology/FilledHull.lean`. The step waiting on that item is the one bounding the piece a
crosscut cuts off from a Jordan domain: the file
`TauCeti/Analysis/Complex/Conformal/Crosscut/SmallJordanCurve.lean` encloses a short image crosscut
in an arbitrarily small Jordan curve `J`, and the cut-off piece is a connected set disjoint from
`J`; once separation says it is the inside of `J` that the piece falls on,
`TauCeti.IsPreconnected.subset_filledHull` and
`TauCeti.diam_filledHull` make it no wider than `J`.

This is a different route to a diameter bound from `TauCeti.diam_le_diam_of_frontier_subset` of
`TauCeti/Analysis/Normed/Module/DiamFrontier.lean`, which bounds a set by *any* bounded set
containing its frontier: there the enclosing set must be known to contain the whole frontier, here
only that the set is cut off from infinity. Neither implies the other.

## Generality

The width statements are stated for an arbitrary real normed space — nothing about the plane is
used, and the separation argument is the general Hahn–Banach one.

## Main results

* `TauCeti.filledHull_subset_closedConvexHull` — a filled hull lies in the closed convex hull.
* `TauCeti.diam_filledHull` and `TauCeti.isBounded_filledHull` — filling preserves the diameter, and
  a filled hull is bounded exactly when the set filled is.
-/

public section

namespace TauCeti

open Bornology Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}

/-- **The filled hull lies in the closed convex hull.** A point outside the closed convex hull of a
nonempty `K` is separated from it by a continuous linear functional; the open half-space this
produces is convex, avoids `K`, and is unbounded, so the component of the point in `Kᶜ` is
unbounded.

Nonemptiness of `K` is what forces the separating functional to be nonzero, and so the half-space to
be unbounded; without it the statement fails in the zero space, where `filledHull ∅ = univ`. -/
theorem filledHull_subset_closedConvexHull (hK : K.Nonempty) :
    filledHull K ⊆ closedConvexHull ℝ K := by
  intro x hx
  rw [mem_filledHull_iff] at hx
  by_contra hxC
  obtain ⟨φ, u, hφx, hφC⟩ := geometric_hahn_banach_point_closed convex_closedConvexHull
    isClosed_closedConvexHull hxC
  -- The open half-space cut off by `φ` is a preconnected subset of `Kᶜ` containing `x`.
  have hHK : {y | φ y < u} ⊆ Kᶜ :=
    fun y hy hyK => absurd (hφC y (subset_closedConvexHull hyK)) (not_lt.mpr hy.le)
  have hsub : {y | φ y < u} ⊆ connectedComponentIn Kᶜ x :=
    (convex_halfSpace_lt φ.toLinearMap.isLinear u).isPreconnected.subset_connectedComponentIn
      hφx hHK
  -- It is unbounded: `φ` is nonzero, so some direction decreases it without bound.
  obtain ⟨b, hb⟩ := hK
  have hφne : φ ≠ 0 := by
    rintro rfl
    have hb' := hφC b (subset_closedConvexHull hb)
    simp only [zero_apply] at hφx hb'
    linarith
  obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by
    by_contra h
    exact hφne (by ext w; simpa using not_not.mp (not_exists.mp h w))
  set v : E := (-(φ w)⁻¹) • w with hv
  have hφv : φ v = -1 := by
    rw [hv, map_smul, smul_eq_mul, neg_mul, inv_mul_cancel₀ hw]
  have hvnorm : 0 < ‖v‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    rw [h, map_zero] at hφv
    norm_num at hφv
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp (hx.subset hsub)
  have hxR : ‖x‖ ≤ R := hR x hφx
  set t : ℝ := (R + ‖x‖ + 1) / ‖v‖ with ht
  have ht0 : 0 ≤ t := by
    refine div_nonneg ?_ (norm_nonneg v)
    linarith [norm_nonneg x]
  have htv : t * ‖v‖ = R + ‖x‖ + 1 := div_mul_cancel₀ _ hvnorm.ne'
  have hmem : x + t • v ∈ {y | φ y < u} := by
    have hval : φ (x + t • v) = φ x - t := by
      rw [map_add, map_smul, hφv, smul_eq_mul, mul_neg_one]
      ring
    simp only [mem_ofPred_eq, hval]
    linarith
  have hbig : t * ‖v‖ ≤ ‖x + t • v‖ + ‖x‖ := by
    have h := norm_sub_le (x + t • v) x
    simpa [norm_smul, abs_of_nonneg ht0] using h
  have := hR _ hmem
  rw [htv] at hbig
  linarith [norm_nonneg x]

/-- **The filled hull of the empty set is a subsingleton.** In a nontrivial space it is empty: the
whole space is convex, hence preconnected, and unbounded, so every component of `∅ᶜ = univ` is
unbounded. In the zero space it is that space, a single point. Either way it is as wide as `∅`,
which is why the diameter statements below need no nonemptiness hypothesis. -/
theorem subsingleton_filledHull_empty : (filledHull (∅ : Set E)).Subsingleton := by
  rcases subsingleton_or_nontrivial E with _ | _
  · exact fun a _ b _ => Subsingleton.elim a b
  · intro y hy
    rw [mem_filledHull_iff, compl_empty] at hy
    exact absurd (hy.subset ((convex_univ (𝕜 := ℝ)).isPreconnected.subset_connectedComponentIn
      (mem_univ y) subset_rfl)) (NormedSpace.unbounded_univ ℝ E)

/-- **A filled hull is bounded exactly when the set filled is.** One direction is
`TauCeti.subset_filledHull`; the other holds because the hull lies in the closed convex hull. -/
@[simp]
theorem isBounded_filledHull : IsBounded (filledHull K) ↔ IsBounded K := by
  refine ⟨fun h => h.subset subset_filledHull, fun hKb => ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | hK
  · exact subsingleton_filledHull_empty.finite.isBounded
  · refine IsBounded.subset ?_ (filledHull_subset_closedConvexHull hK)
    rw [closedConvexHull_eq_closure_convexHull]
    exact (isBounded_convexHull.mpr hKb).closure

/-- **Filling preserves the diameter.** The hull contains `K`, and is contained in the closed convex
hull of `K`, which by `convexHull_diam` and `Metric.diam_closure` is exactly as wide as `K`. An
unbounded `K` has an unbounded hull by `TauCeti.isBounded_filledHull`, and both diameters are then
`0`. -/
@[simp]
theorem diam_filledHull : diam (filledHull K) = diam K := by
  by_cases hKb : IsBounded K
  · rcases K.eq_empty_or_nonempty with rfl | hK
    · rw [diam_subsingleton subsingleton_filledHull_empty, diam_empty]
    have hbdd : IsBounded (closedConvexHull ℝ K) := by
      rw [closedConvexHull_eq_closure_convexHull]
      exact (isBounded_convexHull.mpr hKb).closure
    refine le_antisymm ?_ (diam_mono subset_filledHull (isBounded_filledHull.mpr hKb))
    calc diam (filledHull K) ≤ diam (closedConvexHull ℝ K) :=
          diam_mono (filledHull_subset_closedConvexHull hK) hbdd
      _ = diam K := by
          rw [closedConvexHull_eq_closure_convexHull, diam_closure, convexHull_diam]
  · rw [diam_eq_zero_of_unbounded (mt isBounded_filledHull.mp hKb), diam_eq_zero_of_unbounded hKb]

end TauCeti
