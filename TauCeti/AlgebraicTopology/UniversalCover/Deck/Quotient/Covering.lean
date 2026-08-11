/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient.ActingGroup
public import TauCeti.AlgebraicTopology.UniversalCover.Deck.Quotient.Basic

/-!
# A regular covering is a quotient covering map for its deck group

For a covering map `p : E → B` with preconnected total space whose deck action is regular
(surjective, with `Deck p` acting transitively on every fibre), `p` exhibits `B` as the
quotient of `E` by the deck transformation group: `p` is a `IsQuotientCoveringMap` for
`Deck p`. This is the deck-side formulation of the universal-covers roadmap statement that
`UniversalCover x₀ / π₁(X, x₀) ≃ X`, packaged so that it consumes Mathlib's quotient
covering map theory rather than re-deriving it.

Conversely, a quotient covering map has regular deck action, for any acting group: its
fibres are the orbits, and translation by a group element is a deck transformation. For a
preconnected covering map, this gives an equivalence between being a quotient covering map
for the deck group and regularity of the deck action.

## Main declarations

* `TauCeti.Deck.IsRegular.isQuotientCoveringMap`: a regular, preconnected covering map is a
  quotient covering map for its deck group.
* `TauCeti.Deck.IsQuotientCoveringMap.isRegular`: quotient covering maps have regular deck
  action, whatever the acting group.
* `TauCeti.Deck.isQuotientCoveringMap_iff_isRegular`: for a preconnected covering map, being a
  quotient covering map for the deck group is equivalent to regularity of the deck action.
* `TauCeti.IsCoveringMap.isOpenQuotientMap`: a surjective covering map is an open quotient map.
* `TauCeti.Deck.IsRegular.isOpenQuotientMap`: a regular covering map is an open quotient map.

## References

This supplies a prerequisite for the Tau Ceti universal-covers roadmap, Stages 0.3 and 1,
where the quotient of the cover by the deck group is identified with the base via Mathlib's
`IsQuotientCoveringMap` (`Mathlib/Topology/Covering/Quotient.lean`).
-/

public section

namespace TauCeti

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

/-- A surjective covering map is an open quotient map. -/
theorem IsCoveringMap.isOpenQuotientMap (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) : IsOpenQuotientMap p :=
  .of_isOpenMap_isQuotientMap hp.isOpenMap (hp.isQuotientMap hsurj)

namespace Deck

/-- A regular covering map with preconnected total space is a quotient covering map for its
deck transformation group: it presents the base as the quotient `E / Deck p`. -/
theorem IsRegular.isQuotientCoveringMap [PreconnectedSpace E] (hreg : IsRegular p)
    (hp : IsCoveringMap p) : IsQuotientCoveringMap p (Deck p) := by
  rw [isQuotientCoveringMap_iff_isCoveringMap_and]
  exact ⟨hp, hreg.1, inferInstance, isCancelSMul hp,
    fun {e₁ e₂} => Deck.IsRegular.apply_eq_iff_mem_orbit hreg⟩

/-- A quotient covering map for any acting group has regular deck action: its fibres are the
orbits of the acting group, and each group element translates by a deck transformation. -/
theorem IsQuotientCoveringMap.isRegular {G : Type*} [Group G] [MulAction G E]
    (h : IsQuotientCoveringMap p G) : IsRegular p := by
  refine isRegular_iff_exists_apply_eq.mpr ⟨h.surjective, fun {e e'} hee => ?_⟩
  obtain ⟨g, hg⟩ := h.apply_eq_iff_mem_orbit.mp hee.symm
  exact ⟨IsQuotientCoveringMap.toDeckHom h g, by
    rw [IsQuotientCoveringMap.toDeckHom_apply]; exact hg⟩

/-- For a covering map with preconnected total space, being a quotient covering map for the
deck transformation group is equivalent to regularity of the deck action. -/
theorem isQuotientCoveringMap_iff_isRegular [PreconnectedSpace E] (hp : IsCoveringMap p) :
    IsQuotientCoveringMap p (Deck p) ↔ IsRegular p := by
  exact ⟨fun h => IsQuotientCoveringMap.isRegular h, fun hreg => hreg.isQuotientCoveringMap hp⟩

/-- A regular covering map is an open quotient map. -/
theorem IsRegular.isOpenQuotientMap (hreg : IsRegular p) (hp : IsCoveringMap p) :
    IsOpenQuotientMap p :=
  TauCeti.IsCoveringMap.isOpenQuotientMap hp hreg.1

end Deck

end TauCeti
