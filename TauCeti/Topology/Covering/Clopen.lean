/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Covering.Basic

/-!
# Covering maps and clopen sets

A covering map `p : E → ↥s` onto a subspace of `X` is also a covering map `E → X` as soon as `s`
is clopen: over a point of `s` an evenly covered neighbourhood in `↥s` is one in `X` because `s`
is open, and over a point outside `s` the open set `sᶜ` has empty preimage, which
`IsEvenlyCovered.of_preimage_eq_empty` accepts as an evenly covered neighbourhood with empty
fibre.

Openness alone is not enough: for `s` open but not closed, a point of `frontier s` has every
neighbourhood meeting `s`, so no neighbourhood of it is evenly covered by a surjection onto `s`.
Mathlib's `IsCoveringMap` allows empty fibres, which is exactly what makes the clopen statement
work without assuming `p` surjective or `s = X`.

Empty fibres are also what makes the *range* of a covering map clopen. It is open because a
covering map is a local homeomorphism, and closed because a point outside the range has an evenly
covered neighbourhood whose fibre is empty, so that whole neighbourhood misses the range. Over a
preconnected base a covering map with nonempty total space is therefore surjective.

## Main declarations

* `IsCoveringMap.subtypeVal_comp`: the composite of a covering map onto a clopen
  subspace with the subspace inclusion is a covering map.
* `IsCoveringMap.isClopen_range`: the range of a covering map is clopen.
* `IsCoveringMap.surjective`: a covering map onto a preconnected base with nonempty total space
  is surjective.
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

/-- **The range of a covering map is clopen.** It is open because a covering map is a local
homeomorphism, and closed because an evenly covered neighbourhood of a point outside the range
has empty preimage. -/
theorem _root_.IsCoveringMap.isClopen_range {p : E → X} (hp : IsCoveringMap p) :
    IsClopen (Set.range p) := by
  refine ⟨?_, hp.isLocalHomeomorph.isOpenMap.isOpen_range⟩
  rw [← isOpen_compl_iff]
  refine isOpen_iff_forall_mem_open.mpr fun x hx => ?_
  obtain ⟨-, U, hxU, hU, -, H, -⟩ := hp x
  have : IsEmpty (p ⁻¹' {x} : Set E) := ⟨fun e => hx ⟨e, e.2⟩⟩
  have hpU : p ⁻¹' U = ∅ := Set.isEmpty_coe_sort.mp (Function.isEmpty ⇑H)
  refine ⟨U, fun y hy => ?_, hU, hxU⟩
  rintro ⟨e, rfl⟩
  exact Set.eq_empty_iff_forall_notMem.mp hpU e hy

/-- **A covering map onto a preconnected base is surjective** as soon as its total space is
nonempty: its range is a nonempty clopen subset. -/
theorem _root_.IsCoveringMap.surjective [PreconnectedSpace X] [Nonempty E] {p : E → X}
    (hp : IsCoveringMap p) : Function.Surjective p :=
  Set.range_eq_univ.mp (hp.isClopen_range.eq_univ (Set.range_nonempty p))

end TauCeti
