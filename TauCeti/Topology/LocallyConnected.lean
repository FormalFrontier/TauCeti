/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Local connectedness passes to quotients

Local connectedness is not preserved by continuous images in general — every metric space is a
continuous image of a discrete one — but it *is* preserved by quotient maps, and hence by the
continuous images that are automatically quotient maps: those of a compact space in a Hausdorff
one. This file proves both, in the type-level form and in the set-level form
`TauCeti.locallyConnectedSpace_image_of_isCompact` that a subset of a topological space needs.

Mathlib has `LocallyConnectedSpace` with its `connectedComponentIn` characterization, and knows
that the property passes to open subspaces (`Topology.IsOpenEmbedding.locallyConnectedSpace`,
`IsOpen.locallyConnectedSpace`), but records no behaviour under quotients.

The proof is the standard one and uses `locallyConnectedSpace_iff_connectedComponentIn_open` on
both sides: for `V` open in the target and `y ∈ V`, the preimage of the connected component of `y`
in `V` is a union of connected components of the open set `q ⁻¹' V`, because a connected component
`C` of `q ⁻¹' V` has connected image inside `V`, so that image lies in a single component of `V`.
Those components are open downstairs by local connectedness, so the preimage is open, and the
component itself is then open because `q` is a quotient map.

The intended consumer is layer **L5** of the conformal-mapping roadmap, Carathéodory's boundary
correspondence: a conformal map that extends continuously to the closure of its domain carries a
locally connected boundary to a locally connected boundary, which is the necessary half of
Carathéodory's continuity theorem. That application is in
`TauCeti/Analysis/Complex/Conformal/LocallyConnectedBoundary.lean`; nothing here is specific to it.

## Main results

* `TauCeti.locallyConnectedSpace_of_isQuotientMap` — a quotient of a locally connected space is
  locally connected.
* `TauCeti.locallyConnectedSpace_of_continuous_surjective` — the continuous image of a compact
  locally connected space in a Hausdorff space is locally connected.
* `TauCeti.locallyConnectedSpace_image_of_isCompact` — the set-level form: `f '' s` is locally
  connected for a compact, locally connected `s` on which `f` is continuous.

## References

* R. Engelking, *General Topology*, Theorem 6.1.29 (Hahn's theorem on quotients).
* J. G. Hocking and G. S. Young, *Topology*, Ch. 3.
-/

public section

namespace TauCeti

open Filter Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **A quotient of a locally connected space is locally connected.** No separation or compactness
hypothesis is needed: being a quotient map is exactly what lets openness of the connected
components be transported downstairs.

Some hypothesis beyond continuity and surjectivity is needed: every metric space is the continuous
image of the same set with the discrete topology, which is locally connected. -/
theorem locallyConnectedSpace_of_isQuotientMap [LocallyConnectedSpace X] {q : X → Y}
    (hq : IsQuotientMap q) : LocallyConnectedSpace Y := by
  rw [locallyConnectedSpace_iff_connectedComponentIn_open]
  intro V hV y _
  rw [← hq.isCoinducing.isOpen_preimage]
  -- It suffices to show that every point of `q ⁻¹' connectedComponentIn V y` has the connected
  -- component containing it in the open set `q ⁻¹' V` as a neighbourhood inside that preimage.
  refine isOpen_iff_mem_nhds.mpr fun x hx => ?_
  have hxV : x ∈ q ⁻¹' V := connectedComponentIn_subset V y hx
  have hopen : IsOpen (connectedComponentIn (q ⁻¹' V) x) :=
    (hV.preimage hq.continuous).connectedComponentIn
  refine mem_of_superset (hopen.mem_nhds (mem_connectedComponentIn hxV)) fun z hz => ?_
  -- The image of that component is connected, lies in `V` and meets `connectedComponentIn V y`,
  -- so it is contained in it.
  have himg : q '' connectedComponentIn (q ⁻¹' V) x ⊆ connectedComponentIn V y := by
    have hpre : IsPreconnected (q '' connectedComponentIn (q ⁻¹' V) x) :=
      isPreconnected_connectedComponentIn.image _ hq.continuous.continuousOn
    rw [connectedComponentIn_eq hx]
    exact hpre.subset_connectedComponentIn ⟨x, mem_connectedComponentIn hxV, rfl⟩
      (image_subset_iff.mpr (connectedComponentIn_subset _ _))
  exact himg ⟨z, hz, rfl⟩

/-- **The continuous image of a compact locally connected space in a Hausdorff space is locally
connected.** A continuous surjection out of a compact space onto a Hausdorff one is closed, hence
a quotient map, so `TauCeti.locallyConnectedSpace_of_isQuotientMap` applies. -/
theorem locallyConnectedSpace_of_continuous_surjective [LocallyConnectedSpace X] [CompactSpace X]
    [T2Space Y] {f : X → Y} (hf : Continuous f) (hsurj : Function.Surjective f) :
    LocallyConnectedSpace Y :=
  locallyConnectedSpace_of_isQuotientMap (hf.isClosedMap.isQuotientMap hf hsurj)

/-- **The set-level form: a compact, locally connected set has locally connected continuous
images.** Stated with the subtype topologies on `s` and on `f '' s`, which is how a boundary or a
closure of a subset of a normed space is met in practice. -/
theorem locallyConnectedSpace_image_of_isCompact [T2Space Y] {s : Set X} {f : X → Y}
    [LocallyConnectedSpace s] (hs : IsCompact s) (hf : ContinuousOn f s) :
    LocallyConnectedSpace (f '' s) := by
  haveI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  have hsurj : Function.Surjective ((mapsTo_image f s).restrict f s (f '' s)) := by
    rintro ⟨-, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  exact locallyConnectedSpace_of_continuous_surjective
    (hf.mapsToRestrict (mapsTo_image f s)) hsurj

end TauCeti
