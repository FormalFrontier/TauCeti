/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Finiteness of the Riemannian distance, and the induced metric space

`Manifold.riemannianEDist I x y` is the infimum of the lengths of `C¹` paths from `x` to `y`, an
*extended* distance: it is `∞` as soon as no such path exists. This file identifies exactly when it
is finite, and uses that to promote the extended metric space structure
`EMetricSpace.ofRiemannianMetric` of a preconnected Riemannian manifold to an ordinary metric space
structure, which is what statements about `dist`, `ProperSpace` and `CompleteSpace` need.

The key point is that `{y | riemannianEDist I x y < ∞}` is clopen: it is open because nearby points
are at small Riemannian distance (`eventually_riemannianEDist_lt`), and its complement is open for
the same reason. Hence it contains the connected component of `x`. Conversely a `C¹` path is in
particular continuous, so a point at finite Riemannian distance from `x` lies in the connected
component of `x`. Together these give
`riemannianEDist_lt_top_iff_mem_connectedComponent`, of which finiteness on a preconnected manifold
is the special case that matters downstream.

## Main results

* `TauCeti.Manifold.riemannianEDist_lt_top_iff_mem_connectedComponent`: the Riemannian distance from
  `x` to `y` is finite if and only if `y` lies in the connected component of `x`.
* `TauCeti.Manifold.riemannianEDist_ne_top`: on a preconnected manifold the Riemannian distance is
  never `∞`.
* `TauCeti.PseudoMetricSpace.ofRiemannianMetric` and `TauCeti.MetricSpace.ofRiemannianMetric`: the
  (pseudo)metric space structures of a preconnected Riemannian manifold, refining
  `PseudoEMetricSpace.ofRiemannianMetric` and `EMetricSpace.ofRiemannianMetric`; both satisfy
  `IsRiemannianManifold I M`.
* `TauCeti.IsRiemannianManifold.edist_le_pathELength` and
  `TauCeti.IsRiemannianManifold.dist_le_toReal_pathELength`: the ambient distance of a Riemannian
  manifold, read through `IsRiemannianManifold.out`, is bounded by the length of any `C¹` path.

## References

* [Geodesics, the exponential map, and the Hopf–Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 0, "Distance compatibility and finiteness".
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 7 §2, Def. 2.4.
-/

public section

open Bundle Manifold Set
open scoped ENNReal Manifold Topology

noncomputable section

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

namespace Manifold

section Finiteness

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- A point at finite Riemannian distance from `x` lies in the connected component of `x`: it is
joined to `x` by a `C¹`, hence continuous, path. -/
theorem mem_connectedComponent_of_riemannianEDist_lt_top {x y : M}
    (h : riemannianEDist I x y < ⊤) : y ∈ connectedComponent x := by
  obtain ⟨γ, hγ0, hγ1, hγ, -⟩ := exists_lt_of_riemannianEDist_lt h
  have hpre : IsPreconnected (γ '' Icc 0 1) := isPreconnected_Icc.image γ hγ.continuousOn
  exact hpre.subset_connectedComponent ⟨0, left_mem_Icc.2 zero_le_one, hγ0⟩
    ⟨1, right_mem_Icc.2 zero_le_one, hγ1⟩

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I) in
/-- The set of points at finite Riemannian distance from `x` is open: any point close enough to a
point `y` of this set is at Riemannian distance `< 1` from `y`, hence at finite distance from `x` by
the triangle inequality. -/
theorem isOpen_setOfPred_riemannianEDist_lt_top (x : M) :
    IsOpen {y | riemannianEDist I x y < ⊤} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  filter_upwards [eventually_riemannianEDist_lt I y zero_lt_one] with z hz
  exact (riemannianEDist_triangle (y := y)).trans_lt
    (ENNReal.add_lt_top.2 ⟨hy, hz.trans_le le_top⟩)

variable (I) in
/-- The set of points at finite Riemannian distance from `x` is closed: if `y` is at infinite
Riemannian distance from `x`, then so is any point close enough to `y`, again by the triangle
inequality. -/
theorem isClosed_setOfPred_riemannianEDist_lt_top (x : M) :
    IsClosed {y | riemannianEDist I x y < ⊤} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  filter_upwards [eventually_riemannianEDist_lt I y zero_lt_one] with z hz hz'
  refine hy ((riemannianEDist_triangle (y := z)).trans_lt (ENNReal.add_lt_top.2 ⟨hz', ?_⟩))
  rw [riemannianEDist_comm]
  exact hz.trans_le le_top

variable (I) in
/-- The set of points at finite Riemannian distance from `x` is clopen. -/
theorem isClopen_setOfPred_riemannianEDist_lt_top (x : M) :
    IsClopen {y | riemannianEDist I x y < ⊤} :=
  ⟨isClosed_setOfPred_riemannianEDist_lt_top I x, isOpen_setOfPred_riemannianEDist_lt_top I x⟩

variable (I) in
/-- Two points of a preconnected set are at finite Riemannian distance. -/
theorem riemannianEDist_lt_top_of_isPreconnected {s : Set M} (hs : IsPreconnected s) {x y : M}
    (hx : x ∈ s) (hy : y ∈ s) : riemannianEDist I x y < ⊤ :=
  hs.subset_isClopen (isClopen_setOfPred_riemannianEDist_lt_top I x)
    ⟨x, hx, by simp [riemannianEDist_self]⟩ hy

variable (I) in
/-- The Riemannian distance from `x` to `y` is finite exactly when `y` lies in the connected
component of `x`. -/
theorem riemannianEDist_lt_top_iff_mem_connectedComponent {x y : M} :
    riemannianEDist I x y < ⊤ ↔ y ∈ connectedComponent x :=
  ⟨mem_connectedComponent_of_riemannianEDist_lt_top,
    riemannianEDist_lt_top_of_isPreconnected I isPreconnected_connectedComponent
      mem_connectedComponent⟩

variable (I) in
/-- The Riemannian distance from `x` to `y` is finite exactly when `y` lies in the connected
component of `x`. -/
theorem riemannianEDist_ne_top_iff_mem_connectedComponent {x y : M} :
    riemannianEDist I x y ≠ ⊤ ↔ y ∈ connectedComponent x := by
  rw [← lt_top_iff_ne_top, riemannianEDist_lt_top_iff_mem_connectedComponent I]

variable (I) in
/-- On a preconnected manifold, the Riemannian distance between any two points is finite. -/
theorem riemannianEDist_lt_top [PreconnectedSpace M] (x y : M) : riemannianEDist I x y < ⊤ :=
  riemannianEDist_lt_top_of_isPreconnected I isPreconnected_univ (mem_univ x) (mem_univ y)

variable (I) in
/-- On a preconnected manifold, the Riemannian distance between any two points is finite. This is
the hypothesis needed to turn `EMetricSpace.ofRiemannianMetric` into a genuine metric space. -/
theorem riemannianEDist_ne_top [PreconnectedSpace M] (x y : M) : riemannianEDist I x y ≠ ⊤ :=
  (riemannianEDist_lt_top I x y).ne

end Finiteness

end Manifold

namespace IsRiemannianManifold

section PseudoEMetric

variable {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

variable (I) in
/-- In a Riemannian manifold, the ambient extended distance is bounded above by the length of any
`C¹` path between the two points. -/
theorem edist_le_pathELength {γ : ℝ → M} {a b : ℝ} {x y : M} (hγ : CMDiff[Icc a b] 1 γ)
    (ha : γ a = x) (hb : γ b = y) (hab : a ≤ b) : edist x y ≤ pathELength I γ a b := by
  rw [IsRiemannianManifold.out (I := I) x y]
  exact riemannianEDist_le_pathELength hγ ha hb hab

variable (I) in
/-- In a Riemannian manifold, any bound `r` on the ambient extended distance from `x` to `y` is
witnessed by a `C¹` path on `[0, 1]` of length `< r`. -/
theorem exists_pathELength_lt_of_edist_lt {x y : M} {r : ℝ≥0∞} (hr : edist x y < r) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ CMDiff[Icc 0 1] 1 γ ∧ pathELength I γ 0 1 < r := by
  rw [IsRiemannianManifold.out (I := I) x y] at hr
  exact exists_lt_of_riemannianEDist_lt hr

variable [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I) in
include I in
/-- In a Riemannian manifold, the ambient extended distance from `x` to `y` is finite exactly when
`y` lies in the connected component of `x`. -/
theorem edist_lt_top_iff_mem_connectedComponent {x y : M} :
    edist x y < ⊤ ↔ y ∈ connectedComponent x := by
  rw [IsRiemannianManifold.out (I := I) x y,
    Manifold.riemannianEDist_lt_top_iff_mem_connectedComponent I]

variable (I) in
include I in
/-- In a preconnected Riemannian manifold, the ambient extended distance is never `∞`. -/
theorem edist_ne_top [PreconnectedSpace M] (x y : M) : edist x y ≠ ⊤ := by
  rw [IsRiemannianManifold.out (I := I) x y]
  exact Manifold.riemannianEDist_ne_top I x y

end PseudoEMetric

section PseudoMetric

variable {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

variable (I) in
/-- In a Riemannian manifold whose ambient distance is an ordinary one, that distance is the real
part of the Riemannian extended distance. -/
theorem dist_eq_toReal_riemannianEDist (x y : M) : dist x y = (riemannianEDist I x y).toReal := by
  rw [dist_edist, IsRiemannianManifold.out (I := I) x y]

variable (I) in
/-- In a Riemannian manifold whose ambient distance is an ordinary one, the distance is bounded
above by the length of any `C¹` path of finite length between the two points. -/
theorem dist_le_toReal_pathELength {γ : ℝ → M} {a b : ℝ} {x y : M} (hγ : CMDiff[Icc a b] 1 γ)
    (ha : γ a = x) (hb : γ b = y) (hab : a ≤ b) (h : pathELength I γ a b ≠ ⊤) :
    dist x y ≤ (pathELength I γ a b).toReal := by
  rw [dist_edist]
  exact ENNReal.toReal_mono h (edist_le_pathELength I hγ ha hb hab)

variable (I) in
/-- In a Riemannian manifold whose ambient distance is an ordinary one, any bound `r` on the
distance from `x` to `y` is witnessed by a `C¹` path on `[0, 1]` of length `< ENNReal.ofReal r`. -/
theorem exists_pathELength_lt_of_dist_lt {x y : M} {r : ℝ} (hr : dist x y < r) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ CMDiff[Icc 0 1] 1 γ ∧
      pathELength I γ 0 1 < ENNReal.ofReal r := by
  refine exists_pathELength_lt_of_edist_lt I ?_
  rw [edist_dist]
  exact (ENNReal.ofReal_lt_ofReal_iff (dist_nonneg.trans_lt hr)).2 hr

end PseudoMetric

end IsRiemannianManifold

section OfRiemannianMetric

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- The pseudometric space structure associated to a Riemannian metric on a preconnected manifold,
obtained from `PseudoEMetricSpace.ofRiemannianMetric` now that the extended distance is known to be
finite. As for the extended version, the topology is defeq to the original one. -/
@[reducible] def PseudoMetricSpace.ofRiemannianMetric [RegularSpace M] [PreconnectedSpace M] :
    PseudoMetricSpace M :=
  letI : PseudoEMetricSpace M := .ofRiemannianMetric I M
  PseudoEMetricSpace.toPseudoMetricSpace (fun x y ↦ Manifold.riemannianEDist_ne_top I x y)

/-- The distance of `PseudoMetricSpace.ofRiemannianMetric` is the infimum of the lengths of `C¹`
paths, i.e. the resulting pseudometric space satisfies the `IsRiemannianManifold I M` predicate. -/
instance [RegularSpace M] [PreconnectedSpace M] :
    letI : PseudoMetricSpace M := PseudoMetricSpace.ofRiemannianMetric I M
    IsRiemannianManifold I M := by
  let : PseudoMetricSpace M := PseudoMetricSpace.ofRiemannianMetric I M
  -- `PseudoEMetricSpace.toPseudoMetricSpace` is set up so that the extended distance is preserved
  -- definitionally (its `edist` field is literally `edist`), and the extended distance of
  -- `PseudoEMetricSpace.ofRiemannianMetric` is `riemannianEDist I` by construction. So the
  -- predicate holds by `rfl`, exactly as for the extended structure it refines.
  exact ⟨fun _ _ ↦ rfl⟩

variable (I M) in
/-- The metric space structure associated to a Riemannian metric on a preconnected manifold,
obtained from `EMetricSpace.ofRiemannianMetric` now that the extended distance is known to be
finite. As for the extended version, the topology is defeq to the original one.

This should only be used when constructing data in specific situations. To develop the theory, one
should rather assume that there is an already existing metric space structure, satisfying
additionally the predicate `IsRiemannianManifold I M`. -/
@[reducible] def MetricSpace.ofRiemannianMetric [T3Space M] [PreconnectedSpace M] :
    MetricSpace M :=
  letI : EMetricSpace M := .ofRiemannianMetric I M
  EMetricSpace.toMetricSpace (fun x y ↦ Manifold.riemannianEDist_ne_top I x y)

/-- The distance of `MetricSpace.ofRiemannianMetric` is the infimum of the lengths of `C¹` paths,
i.e. the resulting metric space satisfies the `IsRiemannianManifold I M` predicate. -/
instance [T3Space M] [PreconnectedSpace M] :
    letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
    IsRiemannianManifold I M := by
  let : MetricSpace M := MetricSpace.ofRiemannianMetric I M
  -- As above: `EMetricSpace.toMetricSpace` preserves the extended distance definitionally, and the
  -- extended distance of `EMetricSpace.ofRiemannianMetric` is `riemannianEDist I` by construction.
  exact ⟨fun _ _ ↦ rfl⟩

end OfRiemannianMetric

end TauCeti
