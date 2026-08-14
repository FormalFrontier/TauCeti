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
`x`, and it is unbounded (`TauCeti.not_isBounded_halfSpace_lt`). So the component of `x` in `Kᶜ` is
unbounded and `x` is not in the filled hull. Nonemptiness of `K` is needed only to know that
`φ ≠ 0`; for `K = ∅` and a zero-dimensional space the convex-hull statement is false, the hull then
being everything and the convex hull empty. The diameter statements survive that case
unhypothesised, because `filledHull ∅` is empty in a nontrivial space
(`TauCeti.filledHull_empty`) and the single point of the zero space otherwise, of diameter `0`
either way.

Because the width of a filled hull is controlled, so is that of anything inside it, and the shape
in which this is spent is `TauCeti.IsPreconnected.subset_filledHull`: a preconnected set disjoint
from `K` is trapped inside the filled hull as soon as it meets it. Their composite,
`TauCeti.IsPreconnected.diam_le_diam_of_disjoint`, says that *a connected set that a small `K` cuts
off from infinity is itself small*, with no regularity asked of `K`.

## Roadmap role

The filled hull is the vocabulary in which the open frontier item of layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md` is stated; see the roadmap section of
`TauCeti/Topology/FilledHull.lean`. The step waiting on that item is the one bounding the piece a
crosscut cuts off from a Jordan domain: the file
`TauCeti/Analysis/Complex/Conformal/Crosscut/SmallJordanCurve.lean` encloses a short image crosscut
in an arbitrarily small Jordan curve `J`, and the cut-off piece is a connected set disjoint from
`J`; once separation says it is the inside of `J` that the piece falls on,
`TauCeti.IsPreconnected.diam_le_diam_of_disjoint` makes it no wider than `J`.

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
* `TauCeti.IsPreconnected.diam_le_diam_of_disjoint` — a preconnected set that a bounded `K` cuts off
  from infinity is no wider than `K`.
* `TauCeti.not_isBounded_halfSpace_lt` — an open half-space cut out by a nonzero continuous
  functional is unbounded, and `TauCeti.isBounded_closedConvexHull`,
  `TauCeti.diam_closedConvexHull` — the closed forms of the two convex-hull facts the width
  argument runs on.
-/

public section

namespace TauCeti

open Bornology Metric Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K S : Set E}

/-- **A closed convex hull is bounded exactly when the set is.** The closed form of
`isBounded_convexHull`, the closure adding nothing. -/
@[simp]
theorem isBounded_closedConvexHull : IsBounded (closedConvexHull ℝ K) ↔ IsBounded K := by
  rw [closedConvexHull_eq_closure_convexHull, isBounded_closure_iff, isBounded_convexHull]

/-- **Taking the closed convex hull preserves the diameter.** The closed form of `convexHull_diam`,
the closure adding nothing by `Metric.diam_closure`. -/
@[simp]
theorem diam_closedConvexHull : diam (closedConvexHull ℝ K) = diam K := by
  rw [closedConvexHull_eq_closure_convexHull, diam_closure, convexHull_diam]

/-- **An open half-space cut out by a nonzero continuous functional is unbounded.** Along a
direction `v` with `φ v = 1` the value of `φ` decreases without bound as one walks towards `-v`,
while the norm grows without bound, so the half-space contains points of arbitrarily large norm. -/
theorem not_isBounded_halfSpace_lt {φ : E →L[ℝ] ℝ} (hφ : φ ≠ 0) (u : ℝ) :
    ¬ IsBounded {y | φ y < u} := by
  obtain ⟨w, hw⟩ : ∃ w, φ w ≠ 0 := by simpa using DFunLike.ne_iff.mp hφ
  obtain ⟨v, hφv⟩ : ∃ v : E, φ v = 1 :=
    ⟨(φ w)⁻¹ • w, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hw]⟩
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr fun h => by simp [h] at hφv
  intro hbdd
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbdd
  -- Walk to `-t • v` for a `t` large enough to break both the bound `u` on `φ` and the bound `R`.
  obtain ⟨t, ht1, ht2⟩ : ∃ t : ℝ, (R + 1) / ‖v‖ ≤ t ∧ |u| + 1 ≤ t :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have ht0 : 0 ≤ t := le_trans (by positivity) ht2
  have hmem : (-t) • v ∈ {y | φ y < u} := by
    have hval : φ ((-t) • v) = -t := by rw [map_smul, hφv, smul_eq_mul, mul_one]
    simp only [mem_ofPred_eq, hval]
    linarith [neg_abs_le u]
  have hnorm := hR _ hmem
  rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg ht0] at hnorm
  linarith [(div_le_iff₀ hvnorm).mp ht1]

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
  -- It is unbounded, because a nonempty `K` forces `φ` to be nonzero.
  obtain ⟨b, hb⟩ := hK
  have hφne : φ ≠ 0 := by
    rintro rfl
    have hb' := hφC b (subset_closedConvexHull hb)
    simp only [zero_apply] at hφx hb'
    linarith
  exact not_isBounded_halfSpace_lt hφne u (hx.subset hsub)

/-- **The filled hull of the empty set is empty** in a nontrivial space: the whole space is
connected and unbounded, so every component of `∅ᶜ = univ` is unbounded. -/
@[simp]
theorem filledHull_empty [Nontrivial E] : filledHull (∅ : Set E) = ∅ := by
  apply filledHull_eq_self
  · rw [compl_empty]
    exact isPreconnected_univ
  · rw [compl_empty]
    exact NormedSpace.unbounded_univ ℝ E

/-- The filled hull of the empty set is a subsingleton: empty in a nontrivial space by
`TauCeti.filledHull_empty`, and the whole zero space, a single point, otherwise. Either way it is as
wide as `∅`, which is why the diameter statements below need no nonemptiness hypothesis. -/
private theorem subsingleton_filledHull_empty : (filledHull (∅ : Set E)).Subsingleton := by
  rcases subsingleton_or_nontrivial E with _ | _
  · exact fun a _ b _ => Subsingleton.elim a b
  · rw [filledHull_empty]
    exact subsingleton_empty

/-- **A filled hull is bounded exactly when the set filled is.** One direction is
`TauCeti.subset_filledHull`; the other holds because the hull lies in the closed convex hull. -/
@[simp]
theorem isBounded_filledHull : IsBounded (filledHull K) ↔ IsBounded K := by
  refine ⟨fun h => h.subset subset_filledHull, fun hKb => ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | hK
  · exact subsingleton_filledHull_empty.finite.isBounded
  · exact (isBounded_closedConvexHull.mpr hKb).subset (filledHull_subset_closedConvexHull hK)

/-- **Filling preserves the diameter.** The hull contains `K`, and for nonempty `K` it is contained
in the closed convex hull of `K`, which by `TauCeti.diam_closedConvexHull` is exactly as wide as
`K`; `filledHull ∅` is a subsingleton, of diameter `0` like `∅` itself. An unbounded `K` has an
unbounded hull by `TauCeti.isBounded_filledHull`, and both diameters are then `0`. -/
@[simp]
theorem diam_filledHull : diam (filledHull K) = diam K := by
  by_cases hKb : IsBounded K
  · rcases K.eq_empty_or_nonempty with rfl | hK
    · rw [diam_subsingleton subsingleton_filledHull_empty, diam_empty]
    refine le_antisymm ?_ (diam_mono subset_filledHull (isBounded_filledHull.mpr hKb))
    calc diam (filledHull K) ≤ diam (closedConvexHull ℝ K) :=
          diam_mono (filledHull_subset_closedConvexHull hK) (isBounded_closedConvexHull.mpr hKb)
      _ = diam K := diam_closedConvexHull
  · rw [diam_eq_zero_of_unbounded (mt isBounded_filledHull.mp hKb), diam_eq_zero_of_unbounded hKb]

/-- **A preconnected set that a bounded `K` cuts off from infinity is no wider than `K`.** If `S` is
preconnected, disjoint from `K`, and meets the filled hull of `K`, then it lies inside that hull by
`TauCeti.IsPreconnected.subset_filledHull`, which is no wider than `K` by
`TauCeti.diam_filledHull`. No regularity is asked of `K`. -/
theorem IsPreconnected.diam_le_diam_of_disjoint (hS : IsPreconnected S) (hSK : Disjoint S K)
    (hne : (S ∩ filledHull K).Nonempty) (hK : IsBounded K) : diam S ≤ diam K :=
  calc diam S ≤ diam (filledHull K) :=
        diam_mono (IsPreconnected.subset_filledHull hS hSK hne) (isBounded_filledHull.mpr hK)
    _ = diam K := diam_filledHull

end TauCeti
