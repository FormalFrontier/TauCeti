/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Connected.Clopen

/-!
# Connected components

This file records general topological properties of the quotient of a space by its connected
components.

## Main declaration

* `TauCeti.instT1SpaceConnectedComponents`: the connected-components quotient of any topological
  space is a T1 space.
-/

public section

open Topology

universe u

variable {X : Type u} [TopologicalSpace X]

namespace TauCeti

/-- The quotient of a topological space by its connected components is a T1 space. -/
instance instT1SpaceConnectedComponents : T1Space (ConnectedComponents X) :=
  ⟨fun c => by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [← ConnectedComponents.isQuotientMap_coe.isClosed_preimage,
      connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent⟩

end TauCeti
