/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.LocallyPathConnected
public import TauCeti.Topology.Homotopy.Path

/-!
# Point-set topology of path components

Paths and path homotopies based in `pathComponent x₀` remain in that component, without any
local path-connectedness assumption. This gives path connectedness of the component as a
subspace; under local path connectedness of the ambient space, openness of path components also
gives local path connectedness of the subspace.

## Main declarations

* `TauCeti.homotopic_pathComponent_of_map_subtypeVal_homotopic`: path homotopies reflect along
  the inclusion of a path component.
* Instances making `↥(pathComponent x₀)` path connected and locally path connected.
* `TauCeti.pathComponentSelf`: a point viewed in its own path component.

## References

This supplies point-set prerequisites for the "or one builds the cover of `pathComponent x₀`"
clause in `TauCetiRoadmap/UniversalCovers/README.md`.
-/

public section

open scoped unitInterval
open Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

/-- Two paths in a path component which are homotopic in the ambient space are already
homotopic in the path component. -/
theorem homotopic_pathComponent_of_map_subtypeVal_homotopic
    {a b : pathComponent x₀} {γ δ : Path a b}
    (h : (γ.map continuous_subtype_val).Homotopic
      (δ.map continuous_subtype_val)) :
    γ.Homotopic δ := by
  obtain ⟨H⟩ := h
  have hγmem : ∀ t, (γ.map continuous_subtype_val) t ∈ pathComponent x₀ := fun t =>
    (γ t).2
  have hmem : ∀ p : I × I, H p ∈ pathComponent x₀ := fun p =>
    Joined.mem_pathComponent
      ((H.evalAt p.2).mem_pathComponent p.1)
      (H.map_zero_left p.2 ▸ hγmem p.2)
  exact Path.homotopic_of_continuous_square (fun p => ⟨H p, hmem p⟩)
    (H.continuous.subtype_mk hmem) (fun t => Subtype.ext (H.map_zero_left t))
    (fun t => Subtype.ext (H.map_one_left t)) (fun t => Subtype.ext (H.source t))
    (fun t => Subtype.ext (H.target t))

/-- The path component of a point, as a subspace, is path connected. -/
instance instPathConnectedSpaceSubtypePathComponent :
    PathConnectedSpace (pathComponent x₀) :=
  isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent

/-- In a locally path connected space the path components are open, hence locally path connected
as subspaces. -/
instance instLocallyPathConnectedSpaceSubtypePathComponent [LocallyPathConnectedSpace X] :
    LocallyPathConnectedSpace (pathComponent x₀) :=
  (IsOpen.pathComponent x₀).locallyPathConnectedSpace

/-- The basepoint of `X`, viewed as a point of its own path component. -/
abbrev pathComponentSelf : (pathComponent x₀ : Set X) :=
  ⟨x₀, mem_pathComponent_self x₀⟩

end TauCeti
