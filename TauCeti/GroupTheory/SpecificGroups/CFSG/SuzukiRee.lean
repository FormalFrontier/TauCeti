/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
public import TauCeti.LinearAlgebra.RootSystem.RootLength

/-!
# Root-subgroup exponents for the Suzuki--Ree isogenies

The exceptional isogenies used to construct the Suzuki and Ree groups exchange long and short
simple roots. Their action on a simple root subgroup also raises its parameter to an exponent:
the exponent is `1` on a long simple root and the defining characteristic on a short simple root.
This file records that convention for `TauCeti.SuzukiReeIndex`.

The assignment is a genuine choice. Reversing the two exponents would still make the square of the
exceptional isogeny a prime-field Frobenius, so the square relation alone does not determine which
isogeny the later construction uses. Defining the exponent through
`TauCeti.DynkinType.IsLongSimpleRoot` ties it to the Bourbaki numbering and root-length convention
already fixed by the root-systems development, without introducing a second table for `B₂`, `G₂`,
and `F₄`.

## Main definitions and results

* `TauCeti.SuzukiReeIndex.exponent` is `1` on long simple roots and the characteristic on short
  simple roots.
* `TauCeti.SuzukiReeIndex.exponent_of_isLongSimpleRoot` and
  `TauCeti.SuzukiReeIndex.exponent_of_not_isLongSimpleRoot` are the two computation rules used by
  the exceptional-isogeny equations.
* `TauCeti.SuzukiReeIndex.exponent_eq_one_iff` and
  `TauCeti.SuzukiReeIndex.exponent_eq_characteristic_iff` characterize the two values without
  unfolding the definition.

This is the exponent-convention part of milestone I0 in
`TauCetiRoadmap/CFSGStatement/README.md`. The convention follows Carter, *Simple Groups of Lie
Type*, and the Bourbaki numbering fixed by the CFSG and root-systems roadmaps.
-/

public section

namespace TauCeti

namespace SuzukiReeIndex

/-- The exponent attached to a numbered simple root subgroup by the exceptional isogeny: `1` on a
long simple root and the defining characteristic on a short simple root.

The long-root predicate is the root-systems development's Bourbaki-numbered predicate, rather than
a second family-by-family table. -/
def exponent (e : SuzukiReeIndex) (i : Fin e.1.rank) : ℕ :=
  if e.1.dynkinType.IsLongSimpleRoot i then 1 else e.1.characteristic

/-- The exceptional isogeny uses exponent `1` on long simple root subgroups. -/
@[simp]
theorem exponent_of_isLongSimpleRoot (e : SuzukiReeIndex) (i : Fin e.1.rank)
    (hi : e.1.dynkinType.IsLongSimpleRoot i) : e.exponent i = 1 := by
  simp [exponent, hi]

/-- The exceptional isogeny uses the defining characteristic as its exponent on short simple root
subgroups. -/
@[simp]
theorem exponent_of_not_isLongSimpleRoot (e : SuzukiReeIndex) (i : Fin e.1.rank)
    (hi : ¬e.1.dynkinType.IsLongSimpleRoot i) : e.exponent i = e.1.characteristic := by
  simp [exponent, hi]

/-- A root-subgroup exponent is `1` exactly on a long simple root. -/
@[simp]
theorem exponent_eq_one_iff (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.exponent i = 1 ↔ e.1.dynkinType.IsLongSimpleRoot i := by
  simp [exponent, e.1.characteristic_prime.ne_one]

/-- A root-subgroup exponent is the defining characteristic exactly on a short simple root. -/
@[simp]
theorem exponent_eq_characteristic_iff (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.exponent i = e.1.characteristic ↔ ¬e.1.dynkinType.IsLongSimpleRoot i := by
  by_cases hi : e.1.dynkinType.IsLongSimpleRoot i
  · simp only [exponent_of_isLongSimpleRoot e i hi, hi, not_true_eq_false, iff_false]
    exact e.1.characteristic_prime.ne_one.symm
  · simp only [exponent_of_not_isLongSimpleRoot e i hi, hi, not_false_eq_true]

/-- Every root-subgroup exponent is positive. -/
theorem exponent_pos (e : SuzukiReeIndex) (i : Fin e.1.rank) : 0 < e.exponent i := by
  by_cases hi : e.1.dynkinType.IsLongSimpleRoot i
  · simp only [exponent_of_isLongSimpleRoot e i hi, Nat.zero_lt_one]
  · rw [exponent_of_not_isLongSimpleRoot e i hi]
    exact e.1.characteristic_prime.pos

/-- Every root-subgroup exponent is at most the defining characteristic. -/
theorem exponent_le_characteristic (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.exponent i ≤ e.1.characteristic := by
  by_cases hi : e.1.dynkinType.IsLongSimpleRoot i
  · rw [exponent_of_isLongSimpleRoot e i hi]
    exact e.1.characteristic_prime.one_lt.le
  · simp only [exponent_of_not_isLongSimpleRoot e i hi, le_refl]

/-- The two possible values of a root-subgroup exponent. -/
theorem exponent_eq_one_or_eq_characteristic (e : SuzukiReeIndex) (i : Fin e.1.rank) :
    e.exponent i = 1 ∨ e.exponent i = e.1.characteristic := by
  by_cases hi : e.1.dynkinType.IsLongSimpleRoot i
  · exact Or.inl (exponent_of_isLongSimpleRoot e i hi)
  · exact Or.inr (exponent_of_not_isLongSimpleRoot e i hi)

end SuzukiReeIndex

end TauCeti
