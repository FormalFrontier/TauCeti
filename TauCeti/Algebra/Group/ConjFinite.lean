/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ConjFinite
public import TauCeti.Algebra.Group.Conj

/-!
# Sizes of conjugacy classes

Elementary facts about the size of the carrier of a conjugacy class: the class of the identity is
the singleton `{1}`, every class of a finite group is nonempty, and the class size times the order
of a representative divides the order of the group.

That last divisibility is what makes the quotient `#G / (#C * orderOf g)` exact rather than a
truncated natural-number division, which matters wherever such a quotient is asserted to count
something. `TauCeti.ConjClasses.card_carrier_mk` in `TauCeti/Algebra/Group/Conj.lean` identifies
the class size with the index of a centralizer, and everything here is read off from that.

## Main results

* `TauCeti.ConjClasses.carrier_mk_one`: the class of `1` is `{1}`, with its counting form
  `TauCeti.ConjClasses.card_carrier_mk_one`.
* `TauCeti.ConjClasses.card_carrier_pos`: a conjugacy class of a finite group has positive size.
* `TauCeti.ConjClasses.card_carrier_mul_orderOf_dvd_card`: the class size times the order of a
  representative divides the order of the group.
* `TauCeti.ConjClasses.card_div_card_carrier_mul_orderOf`: that quotient equals the order of the
  centralizer divided by the order of the representative.
-/

public section

namespace TauCeti

namespace ConjClasses

variable {G : Type*} [Group G]

/-- **The conjugacy class of the identity is the singleton `{1}`**: an element conjugate to `1` is
`1`. -/
@[simp]
theorem carrier_mk_one : (_root_.ConjClasses.mk (1 : G)).carrier = {1} := by
  ext g
  rw [_root_.ConjClasses.mem_carrier_iff_mk_eq, _root_.ConjClasses.mk_eq_mk_iff_isConj,
    isConj_one_left, Set.mem_singleton_iff]

/-- **The identity conjugacy class has exactly one element.** This is the weight that normalizes the
identity column of a character table.

This is not a `@[simp]` lemma: `Nat.card` of a coerced set is not in simp normal form, `Set.ncard`
being what `Nat.card_coe_set_eq` rewrites it to. -/
theorem card_carrier_mk_one : Nat.card (_root_.ConjClasses.mk (1 : G)).carrier = 1 := by
  rw [carrier_mk_one]
  simp

/-- **A conjugacy class of a finite group has positive size**: it contains any of its
representatives. -/
theorem card_carrier_pos [Finite G] (C : _root_.ConjClasses G) : 0 < Nat.card C.carrier := by
  obtain ⟨g, rfl⟩ := C.exists_rep
  have : Nonempty (_root_.ConjClasses.mk g).carrier := ⟨⟨g, _root_.ConjClasses.mem_carrier_mk⟩⟩
  exact Nat.card_pos

/-- An element lies in its own centralizer. -/
private theorem mem_centralizer_self (g : G) : g ∈ Subgroup.centralizer {g} :=
  Subgroup.mem_centralizer_iff.mpr fun h hh ↦ by
    rw [Set.mem_singleton_iff] at hh; subst hh; rfl

/-- **The size of a conjugacy class times the order of a representative divides the group order.**

The class size is the index of the centralizer, and the order of `g` divides the order of that
centralizer because `g` lies in it; multiplying index by order recovers the group order. This is
what makes `Nat.card G / (Nat.card C.carrier * orderOf g)` an exact division rather than a
truncated one, and `card_div_card_carrier_mul_orderOf` evaluates that quotient. -/
theorem card_carrier_mul_orderOf_dvd_card (g : G) :
    Nat.card (_root_.ConjClasses.mk g).carrier * orderOf g ∣ Nat.card G := by
  obtain ⟨k, hk⟩ := (Subgroup.centralizer {g}).orderOf_dvd_natCard (mem_centralizer_self g)
  exact ⟨k, by rw [card_carrier_mk, mul_assoc, ← hk, Subgroup.index_mul_card]⟩

/-- **That quotient in closed form.** Dividing the group order by the class size times the order of
a representative leaves the centralizer order divided by that same order; the common factor is the
centralizer's index, which the class size equals. -/
theorem card_div_card_carrier_mul_orderOf [Finite G] (g : G) :
    Nat.card G / (Nat.card (_root_.ConjClasses.mk g).carrier * orderOf g)
      = Nat.card (Subgroup.centralizer {g}) / orderOf g := by
  rw [card_carrier_mk, ← Subgroup.index_mul_card (Subgroup.centralizer {g}),
    Nat.mul_div_mul_left _ _ (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)]

end ConjClasses

end TauCeti
