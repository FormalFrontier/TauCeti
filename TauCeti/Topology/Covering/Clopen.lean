/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Covering.Basic

/-!
# Covering maps onto a clopen subspace

A covering map `p : E → ↥s` onto a subspace of `X` is also a covering map `E → X` as soon as `s`
is clopen: over a point of `s` an evenly covered neighbourhood in `↥s` is one in `X` because `s`
is open, and over a point outside `s` the open set `sᶜ` has empty preimage, which
`IsEvenlyCovered.of_preimage_eq_empty` accepts as an evenly covered neighbourhood with empty
fibre.

Openness alone is not enough: for `s` open but not closed, a point of `frontier s` has every
neighbourhood meeting `s`, so no neighbourhood of it is evenly covered by a surjection onto `s`.
Mathlib's `IsCoveringMap` allows empty fibres, which is exactly what makes the clopen statement
work without assuming `p` surjective or `s = X`.

## Main declarations

* `IsCoveringMap.subtypeVal_comp`: the composite of a covering map onto a clopen
  subspace with the subspace inclusion is a covering map.
-/

public section

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {s : Set X}

/-- **A covering map onto a clopen subspace is a covering map into the ambient space.** Points of
`s` inherit their evenly covered neighbourhoods through the open inclusion, and points outside
`s` are evenly covered by `sᶜ` with empty fibre. -/
theorem _root_.IsCoveringMap.subtypeVal_comp {p : E → s} (hp : IsCoveringMap p) (hs : IsClopen s) :
    IsCoveringMap (Subtype.val ∘ p) := by
  intro x
  by_cases hx : x ∈ s
  · exact ((hp ⟨x, hx⟩).subtypeVal_comp _ hs.isOpen).to_isEvenlyCovered_preimage
  · refine IsEvenlyCovered.to_isEvenlyCovered_preimage
      (IsEvenlyCovered.of_preimage_eq_empty Empty (hs.isClosed.isOpen_compl.mem_nhds hx) ?_)
    exact Set.eq_empty_of_forall_notMem fun e he => he (p e).2

end TauCeti
