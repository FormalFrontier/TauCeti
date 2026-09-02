/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.RepresentationRing.Basic
import TauCeti.RepresentationTheory.CharacterTable.Determined

/-!
# Injectivity of the character map on the representation ring

Let `G` be a finite group and `k` an algebraically closed field of characteristic zero. This file
proves that the character homomorphism from the representation ring of `G` is injective. Thus a
virtual representation is determined by its character.

For the representation ring itself, every element of split `K₀` is a difference `[V] - [W]`.
A difference in the kernel has `V.character = W.character`, so the object-level theorem makes
`V` and `W` isomorphic and their difference vanishes. The object-level input is
`FDRep.nonempty_iso_of_character_eq`, proved in
`TauCeti/RepresentationTheory/CharacterTable/Determined.lean` from Maschke decompositions and
the character pairing.

## Main results

* `TauCeti.repRingCharacter_injective`: the character homomorphism on the representation ring is
  injective.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part II, §9.1.

This is the injectivity target in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`.
-/

public section

namespace TauCeti

universe u v

section CharacterMap

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- **For a finite group over an algebraically closed field of characteristic zero, the character
homomorphism is injective.** Thus every virtual representation is determined by its character. -/
theorem repRingCharacter_injective [Finite G] [IsAlgClosed k] [CharZero k] :
    Function.Injective (repRingCharacter k G) := by
  intro x y hxy
  apply sub_eq_zero.mp
  obtain ⟨V, W, hVW⟩ := SplitK0.exists_eq_sub (x - y)
  have hzero : repRingCharacter k G (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hchar : V.character = W.character := by
    rw [hVW, map_sub, repRingCharacter_of, repRingCharacter_of, sub_eq_zero] at hzero
    exact hzero
  obtain ⟨i⟩ := FDRep.nonempty_iso_of_character_eq V W hchar
  rw [hVW, SplitK0.of_congr i, sub_self]

end CharacterMap

end TauCeti
