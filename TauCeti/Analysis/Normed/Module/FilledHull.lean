/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.LocallyConvex.Separation
-- `NormedSpace.toLocallyConvexSpace`, needed to apply `geometric_hahn_banach_point_closed`.
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Filling in the bounded complementary components of a set

The **filled hull** `TauCeti.filledHull K` of a subset `K` of a topological space with a bornology
is `K` together with the bounded connected components of its complement: the points whose component
in `Kᶜ` is bounded. Points of `K` qualify vacuously, their component in `Kᶜ` being empty. Filling a
circle gives the closed disc it bounds; filling a segment, or any set whose complement is connected
and unbounded, changes nothing.

In a real normed space the one substantial fact is that filling does not make a set wider:

> `TauCeti.filledHull_subset_closure_convexHull` — `filledHull K ⊆ closure (convexHull ℝ K)`,

whence `TauCeti.diam_filledHull`: a bounded `K` and its filled hull have the same diameter. The
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
from `K` is trapped inside the filled hull as soon as it meets it, since it then lies in a single
bounded component. Together the two say that *a connected set that a small `K` cuts off from
infinity is itself small*, with no regularity asked of `K`.

The negation of membership — that the component of a point in the complement of `K` is *unbounded*
— already occurs, unfolded, in the winding-number layer: it is the hypothesis of
`TauCeti.windingNumber_eq_zero_of_unbounded_component` in
`TauCeti/Analysis/Contour/Winding/UnboundedComponent.lean` and of its cycle form in
`TauCeti/Analysis/Contour/Cycle/Winding.lean`, both of which say that the winding number vanishes
off the filled hull of the trace. Those statements are left as they stand: they are about the
unbounded side, which needs no name, whereas everything below is about the filled side.

## Roadmap role

Plane separation for Jordan curves is the open frontier item of layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`, the Carathéodory boundary correspondence:
`ConformalMapping/STATUS.md` records that nothing in the repository establishes that a Jordan curve
separates the plane, and asks that how much of it the boundary work needs be settled first. What
that work needs is the single statement that every point of a Jordan curve is a limit of points
inside it,

> `J ⊆ closure (filledHull J \ J)`,

which is written in the vocabulary defined here — the inside of `J` is `filledHull J \ J`. So this
file supplies what the missing stage is stated with rather than presuming it: nothing below assumes
separation, or any other regularity of `K`.

Beyond that stage, the step waiting on it is the one bounding the piece a crosscut cuts off from a
Jordan domain. `TauCeti/Analysis/Complex/Conformal/Crosscut/SmallJordanCurve.lean` encloses a short
image crosscut in an arbitrarily small Jordan curve `J`, and the cut-off piece is a connected set
disjoint from `J`; once separation says it is the inside of `J` that the piece falls on,
`TauCeti.IsPreconnected.subset_filledHull` and `TauCeti.diam_filledHull` make it no wider than `J`.

This is a different route to a diameter bound from `TauCeti.diam_le_diam_of_frontier_subset` of
`TauCeti/Analysis/Normed/Module/DiamFrontier.lean`, which bounds a set by *any* bounded set
containing its frontier: there the enclosing set must be known to contain the whole frontier, here
only that the set is cut off from infinity. Neither implies the other.

## Generality

The definition and its structural lemmas, up to `TauCeti.IsPreconnected.subset_filledHull`, ask only
for a topology and a bornology: they are about components and boundedness and use nothing else. The
width statements are those that need a real normed space, and even they are stated for an arbitrary
one — nothing about the plane is used, and the separation argument is the general Hahn–Banach one.
In particular the hull is *not* claimed to be closed, connected, or idempotent — none of which is
needed downstream, and the first two of which fail without hypotheses on `K`.

## Main results

* `TauCeti.filledHull` — the filled hull, and `TauCeti.subset_filledHull`,
  `TauCeti.filledHull_mono` its two structural properties.
* `TauCeti.filledHull_subset_closure_convexHull` — a filled hull lies in the closed convex hull.
* `TauCeti.diam_filledHull` and `TauCeti.isBounded_filledHull` — filling preserves the diameter of a
  bounded set, and in particular its boundedness.
* `TauCeti.IsPreconnected.subset_filledHull` — a preconnected set disjoint from `K` that meets the
  filled hull lies in it, and so, with `TauCeti.diam_filledHull`, is no wider than `K`.
-/

public section

namespace TauCeti

open Bornology Metric Set

variable {E : Type*} {K L S : Set E} {x : E}

section Basic

variable [TopologicalSpace E] [Bornology E]

/-- The **filled hull** of a set `K`: the points whose connected component in the complement of `K`
is bounded. Equivalently, `K` together with the bounded connected components of `Kᶜ`; a point of
`K` belongs because its component in `Kᶜ` is empty. -/
def filledHull (K : Set E) : Set E := {x | IsBounded (connectedComponentIn Kᶜ x)}

@[simp]
theorem mem_filledHull_iff : x ∈ filledHull K ↔ IsBounded (connectedComponentIn Kᶜ x) := Iff.rfl

/-- **A set lies in its filled hull.** For `x ∈ K` the component of `x` in `Kᶜ` is empty, and the
empty set is bounded. -/
theorem subset_filledHull : K ⊆ filledHull K := by
  intro x hx
  have hxc : x ∉ Kᶜ := by simpa using hx
  simp [mem_filledHull_iff, connectedComponentIn_eq_empty hxc]

/-- **Filling is monotone.** Enlarging `K` shrinks the complement, hence shrinks each component of
it, hence can only turn unbounded components into bounded ones. -/
theorem filledHull_mono (h : K ⊆ L) : filledHull K ⊆ filledHull L := by
  intro x hx
  by_cases hxL : x ∈ L
  · exact subset_filledHull hxL
  · refine hx.subset (isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn (by simpa using hxL)) ?_)
    exact (connectedComponentIn_subset _ _).trans (compl_subset_compl.mpr h)

/-- **A preconnected set that a set cuts off from infinity lies in its filled hull.** If `S` is
preconnected and disjoint from `K`, then `S` lies in a single connected component of `Kᶜ`; meeting
the filled hull says that component is bounded, so all of `S` is in the hull. -/
theorem IsPreconnected.subset_filledHull (hS : IsPreconnected S) (hSK : Disjoint S K)
    (hne : (S ∩ filledHull K).Nonempty) : S ⊆ filledHull K := by
  obtain ⟨x, hxS, hxH⟩ := hne
  have hScompl : S ⊆ Kᶜ := fun y hy => Set.disjoint_left.mp hSK hy
  have hScomp : S ⊆ connectedComponentIn Kᶜ x := hS.subset_connectedComponentIn hxS hScompl
  intro y hy
  rw [mem_filledHull_iff, ← connectedComponentIn_eq (hScomp hy)]
  exact hxH

end Basic

/-! ## The width of a filled hull -/

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The filled hull lies in the closed convex hull.** A point outside the closed convex hull of a
nonempty `K` is separated from it by a continuous linear functional; the open half-space this
produces is convex, avoids `K`, and is unbounded, so the component of the point in `Kᶜ` is
unbounded.

Nonemptiness of `K` is what forces the separating functional to be nonzero, and so the half-space to
be unbounded; without it the statement fails in the zero space, where `filledHull ∅ = univ`. -/
theorem filledHull_subset_closure_convexHull (hK : K.Nonempty) :
    filledHull K ⊆ closure (convexHull ℝ K) := by
  intro x hx
  by_contra hxC
  obtain ⟨φ, u, hφx, hφC⟩ := geometric_hahn_banach_point_closed
    ((convex_convexHull ℝ K).closure) isClosed_closure hxC
  have hKC : K ⊆ closure (convexHull ℝ K) := (subset_convexHull ℝ K).trans subset_closure
  -- The open half-space cut off by `φ` is a preconnected subset of `Kᶜ` containing `x`.
  have hHK : {y | φ y < u} ⊆ Kᶜ := fun y hy hyK => absurd (hφC y (hKC hyK)) (not_lt.mpr hy.le)
  have hsub : {y | φ y < u} ⊆ connectedComponentIn Kᶜ x :=
    (convex_halfSpace_lt φ.toLinearMap.isLinear u).isPreconnected.subset_connectedComponentIn
      hφx hHK
  -- It is unbounded: `φ` is nonzero, so some direction decreases it without bound.
  obtain ⟨b, hb⟩ := hK
  have hφne : φ ≠ 0 := by
    rintro rfl
    have hb' := hφC b (hKC hb)
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

/-- **A bounded set has a bounded filled hull.** -/
theorem isBounded_filledHull (hKb : IsBounded K) : IsBounded (filledHull K) := by
  rcases K.eq_empty_or_nonempty with rfl | hK
  · exact subsingleton_filledHull_empty.finite.isBounded
  · exact ((isBounded_convexHull.mpr hKb).closure).subset (filledHull_subset_closure_convexHull hK)

/-- **Filling preserves the diameter.** The hull contains `K`, and is contained in the closed convex
hull of `K`, which by `convexHull_diam` and `Metric.diam_closure` is exactly as wide as `K`. -/
theorem diam_filledHull (hKb : IsBounded K) : diam (filledHull K) = diam K := by
  rcases K.eq_empty_or_nonempty with rfl | hK
  · rw [diam_subsingleton subsingleton_filledHull_empty, diam_empty]
  refine le_antisymm ?_ (diam_mono subset_filledHull (isBounded_filledHull hKb))
  calc diam (filledHull K) ≤ diam (closure (convexHull ℝ K)) :=
        diam_mono (filledHull_subset_closure_convexHull hK) ((isBounded_convexHull.mpr hKb).closure)
    _ = diam K := by rw [diam_closure, convexHull_diam]

end Normed

end TauCeti
