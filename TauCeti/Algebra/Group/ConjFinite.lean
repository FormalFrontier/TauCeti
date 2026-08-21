/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ConjFinite

/-!
# Sizes of conjugacy classes

Two elementary facts about the carrier of a conjugacy class: the class of the identity is the
singleton `{1}`, and every class of a finite group is nonempty.

## Main results

* `TauCeti.ConjClasses.carrier_mk_one`: the class of `1` is `{1}`, with its counting form
  `TauCeti.ConjClasses.card_carrier_mk_one`.
* `TauCeti.ConjClasses.card_carrier_pos`: a conjugacy class of a finite group has positive size.
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

end ConjClasses

end TauCeti
