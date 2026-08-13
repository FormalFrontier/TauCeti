/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Character

/-!
# A character is a class function

Mathlib records the conjugation invariance of the character of a representation as
`Representation.char_conj`, in the form `χ (h * g * h⁻¹) = χ g` that a computation with a
conjugating element produces.  A classification of conjugacy classes, on the other hand, hands out
the conjugacy of two elements as `IsConj g h`, and this file records the same invariance in that
form: a character takes the same value at any two conjugate elements, whatever the group and the
representation.

## Main results

* `TauCeti.Representation.character_eq_of_isConj`: the character of a representation agrees at two
  conjugate elements.

## References

* [Compact groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md),
  "Engine case: `SU(2)` and the maximal torus", where a character on the maximal torus is carried
  to the whole group along the conjugacy of every element into that torus.
-/

public section

namespace TauCeti

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- **The character of a representation is a class function**: it takes the same value at any two
conjugate elements.  This is `Representation.char_conj` with the conjugacy presented as
`IsConj`. -/
theorem character_eq_of_isConj (ρ : Representation k G V) {g h : G} (hgh : IsConj g h) :
    ρ.character g = ρ.character h := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hgh
  rw [← hc, _root_.Representation.char_conj]

end Representation

end TauCeti
