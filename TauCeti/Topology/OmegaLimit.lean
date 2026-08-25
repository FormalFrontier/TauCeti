/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import TauCeti.Topology.Continuum

/-!
# The ω-limit set of a curve

The **ω-limit set** of a curve `u : ℝ → X` is the set of points that `u t` approaches as
`t → ∞`: the set of cluster points of `u` along `atTop`, written `{x | MapClusterPt x atTop u}`.
This file proves that it is the nested intersection `⋂ T, closure (u '' Ici T)` of the closures of
its tails and that it is preconnected. Its nonemptiness for a curve confined to a compact set is
the existing `IsCompact.exists_mapClusterPt`.

Mathlib's `omegaLimit` is the ω-limit set of a *flow* `ϕ : τ → α → α` applied to a set of initial
conditions; specialising it to a single curve would force a dummy one-point space of initial
conditions into every statement. The ω-limit set of one curve is exactly a set of cluster points,
so `Filter.MapClusterPt` is used instead, as it is in `TauCeti/Topology/ClusterSet.lean` for the
boundary cluster set — and, unlike the flow, a curve here need only be defined and continuous on a
half-line `Set.Ici a`.

Both hypotheses on the curve are needed for the two substantive statements. `u t = t` on `ℝ` has
empty ω-limit set, so confinement to a compact set is what makes it nonempty. Preconnectedness is
where continuity enters: `u t = ⌊t⌋ % 2` is confined to `{0, 1}` and has ω-limit set `{0, 1}`.

The substantive statements are proved by writing the ω-limit set as the intersection of the closed
tails `closure (u '' Ici T)`, `T ≥ a`, which is a downward directed family of compact preconnected
sets, and applying `TauCeti.isPreconnected_iInter_of_directed`.

This file is written for the Morse-theoretic
`TauCeti/Analysis/Calculus/Morse/Convergence.lean`, where the ω-limit set of a negative gradient
trajectory is shown to consist of critical points and, being preconnected inside a finite critical
locus, to be a single point.

## Main results

* `TauCeti.setOf_mapClusterPt_atTop_eq_iInter` — the ω-limit set of a curve is the intersection of
  the closures of its tails.
* `TauCeti.isPreconnected_setOf_mapClusterPt_atTop` — the ω-limit set of such a curve, continuous
  on the half-line carrying that tail, is preconnected.

## References

* M. Audin, M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014, Chapter 2.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HeegaardFloer/README.md),
  Lane M, "Morse homology".
-/

public section

namespace TauCeti

open Filter Set Topology

variable {X : Type*} [TopologicalSpace X] {u : ℝ → X} {K : Set X} {a : ℝ}

/-- **The ω-limit set of a curve is the intersection of the closures of its tails.** The
intersection may be taken over the tails starting at any time `T ≥ a`, since those still form a
basis of `atTop`; the half-line `Set.Ici a` is the domain on which the curve is later assumed
continuous. -/
theorem setOf_mapClusterPt_atTop_eq_iInter (u : ℝ → X) (a : ℝ) :
    {x | MapClusterPt x atTop u} = ⋂ T : ↥(Ici a), closure (u '' Ici (T : ℝ)) := by
  ext x
  simp only [mem_ofPred_eq, MapClusterPt, clusterPt_iff_forall_mem_closure, mem_iInter]
  refine ⟨fun h T => h _ (image_mem_map (Ici_mem_atTop _)), fun h s hs => ?_⟩
  obtain ⟨T, hT⟩ := mem_atTop_sets.mp (mem_map.mp hs)
  refine closure_mono ?_ (h ⟨max T a, mem_Ici.mpr (le_max_right T a)⟩)
  rintro _ ⟨t, ht, rfl⟩
  exact hT t ((le_max_left _ _).trans ht)

/-- **The ω-limit set of a curve with a tail in a compact set is preconnected**, provided the curve
is continuous on the half-line carrying that tail. Together with
`IsCompact.exists_mapClusterPt` this makes the ω-limit set connected in the sense of `IsConnected`.
-/
theorem isPreconnected_setOf_mapClusterPt_atTop [T2Space X] (hK : IsCompact K)
    (hu : ContinuousOn u (Ici a)) (hmaps : MapsTo u (Ici a) K) :
    IsPreconnected {x | MapClusterPt x atTop u} := by
  have : Nonempty ↥(Ici a) := ⟨⟨a, mem_Ici.mpr le_rfl⟩⟩
  rw [setOf_mapClusterPt_atTop_eq_iInter u a]
  refine isPreconnected_iInter_of_directed (fun T₁ T₂ => ?_) (fun T => ?_) (fun T => ?_)
  · refine ⟨⟨max (T₁ : ℝ) (T₂ : ℝ),
      mem_Ici.mpr ((mem_Ici.mp T₁.2).trans (le_max_left _ _))⟩, ?_, ?_⟩ <;>
      exact closure_mono (image_mono (Ici_subset_Ici.mpr (by simp)))
  · exact hK.of_isClosed_subset isClosed_closure (closure_minimal
      ((image_mono (Ici_subset_Ici.mpr (mem_Ici.mp T.2))).trans hmaps.image_subset)
      hK.isClosed)
  · exact ((isPreconnected_Ici (a := (T : ℝ))).image u
      (hu.mono (Ici_subset_Ici.mpr (mem_Ici.mp T.2)))).closure

end TauCeti
