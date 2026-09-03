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
# Local connectedness of continuous images of compact spaces

Local connectedness is not preserved by continuous images in general — every metric space is a
continuous image of a discrete one — but it *is* preserved by quotient maps, and hence by the
continuous images that are automatically quotient maps: those of a compact space in a Hausdorff
one. This file proves that, in the type-level form and in the set-level form
`TauCeti.locallyConnectedSpace_image_of_isCompact` that a subset of a topological space needs.

The quotient step itself is Mathlib's. `Topology.IsCoinducing.locallyConnectedSpace` states that
a topology coinduced by a locally connected one is locally connected, which reaches quotient maps
through `IsQuotientMap.isCoinducing` and is strictly more general, since coinducing does not ask
for surjectivity. What is added here is the passage from that to a continuous surjection out of a
compact space, which is closed and therefore a quotient map.

The intended consumer is layer **L5** of the conformal-mapping roadmap, Carathéodory's boundary
correspondence: a conformal map that extends continuously to the closure of its domain carries a
locally connected boundary to a locally connected boundary, which is the necessary half of
Carathéodory's continuity theorem. That application is in
`TauCeti/Analysis/Complex/Conformal/LocallyConnectedBoundary.lean`; nothing here is specific to it.

## Main results

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

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The continuous image of a compact locally connected space in a Hausdorff space is locally
connected.** A continuous surjection out of a compact space onto a Hausdorff one is closed, hence
a quotient map, hence coinducing, so `Topology.IsCoinducing.locallyConnectedSpace` applies. -/
theorem locallyConnectedSpace_of_continuous_surjective [LocallyConnectedSpace X] [CompactSpace X]
    [T2Space Y] {f : X → Y} (hf : Continuous f) (hsurj : Function.Surjective f) :
    LocallyConnectedSpace Y :=
  (hf.isClosedMap.isQuotientMap hf hsurj).isCoinducing.locallyConnectedSpace

/-- **The set-level form: a compact, locally connected set has locally connected continuous
images.** Stated with the subtype topologies on `s` and on `f '' s`, which is how a boundary or a
closure of a subset of a normed space is met in practice. -/
theorem locallyConnectedSpace_image_of_isCompact [T2Space Y] {s : Set X} {f : X → Y}
    [LocallyConnectedSpace s] (hs : IsCompact s) (hf : ContinuousOn f s) :
    LocallyConnectedSpace (f '' s) := by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  exact locallyConnectedSpace_of_continuous_surjective (hf.mapsToRestrict (mapsTo_image f s))
    (surjective_mapsTo_image_restrict f s)

end TauCeti
