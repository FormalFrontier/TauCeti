/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import TauCeti.Topology.ClusterSet

/-!
# The cluster set of a map on a convex domain

`TauCeti.isPreconnected_clusterSetOn` makes the cluster set of a map connected as soon as the
approach regions `U ∩ t` are connected along a neighbourhood basis of the approach point. On a
**convex** domain that hypothesis is automatic, at every point of the ambient space: the
intersection of `U` with a ball is convex, and balls form a neighbourhood basis. This file records
that specialization, which is how the hypothesis is discharged in practice — the disc, a half-plane
and a polygon are all convex.

Convexity of `U` is used only through the convexity of `U ∩ ball w δ`; the point `w` is arbitrary
and in particular need not lie in `U`, the interesting case being a boundary point. Nothing is
assumed of the map beyond continuity on `U` and values in a compact set: connectedness of the
cluster set is a property of the *domain*, not of the map.

The consumer is the Carathéodory boundary correspondence, layer **L5** of the conformal-mapping
roadmap, where `U` is the unit disc: the cluster set of a Riemann map at a boundary point is a
continuum, and the conformal layer places that continuum *on the frontier of the image*.
Carathéodory's theorem is the assertion that for a Jordan domain it degenerates to a point.

## Main results

* `TauCeti.isPreconnected_clusterSetOn_of_convex` and `TauCeti.isConnected_clusterSetOn_of_convex`
  — on a convex domain the cluster set is preconnected, and is a continuum at a point of the
  closure.
* `TauCeti.isConnected_clusterSetOn_of_convex_of_isBounded` — the form used in practice: a
  continuous map with bounded image into a proper metric space.

## References

* E. F. Collingwood and A. J. Lohwater, *The Theory of Cluster Sets*, Ch. 1.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
-/

public section

namespace TauCeti

open Metric Set Topology

section Compact

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace Y] [T2Space Y]
  {U : Set E} {K : Set Y} {f : E → Y} {w : E}

/-- **On a convex domain the cluster set is preconnected.** The neighbourhood-basis hypothesis of
`TauCeti.isPreconnected_clusterSetOn` is discharged by the balls around `w`, whose intersections
with a convex `U` are convex, hence preconnected. -/
theorem isPreconnected_clusterSetOn_of_convex (hUc : Convex ℝ U) (hK : IsCompact K)
    (hfK : MapsTo f U K) (hfc : ContinuousOn f U) : IsPreconnected (clusterSetOn f U w) :=
  isPreconnected_clusterSetOn hK hfK hfc fun s hs => by
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
    exact ⟨ball w δ, ball_mem_nhds w hδ, hball, (hUc.inter (convex_ball w δ)).isPreconnected⟩

/-- **On a convex domain the cluster set at a point of the closure is a continuum.** -/
theorem isConnected_clusterSetOn_of_convex (hUc : Convex ℝ U) (hK : IsCompact K)
    (hfK : MapsTo f U K) (hfc : ContinuousOn f U) (hw : w ∈ closure U) :
    IsConnected (clusterSetOn f U w) :=
  ⟨clusterSetOn_nonempty hK hfK hw, isPreconnected_clusterSetOn_of_convex hUc hK hfK hfc⟩

end Compact

section Proper

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace Y] [ProperSpace Y]
  {U : Set E} {f : E → Y} {w : E}

/-- **The continuum property in the form it is applied in**: a continuous map on a convex domain,
with bounded image in a proper metric space, has a continuum for its cluster set at every point of
the closure of the domain — in particular at every boundary point. -/
theorem isConnected_clusterSetOn_of_convex_of_isBounded (hUc : Convex ℝ U) (hfc : ContinuousOn f U)
    (hfb : Bornology.IsBounded (f '' U)) (hw : w ∈ closure U) :
    IsConnected (clusterSetOn f U w) :=
  isConnected_clusterSetOn_of_convex hUc hfb.isCompact_closure
    (fun z hz => subset_closure ⟨z, hz, rfl⟩) hfc hw

end Proper

end TauCeti
