/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.RepresentationRing.Basic
import TauCeti.RepresentationTheory.CharacterTable.Independence

/-!
# Injectivity of the character map on the representation ring

Let `G` be a finite group and `k` an algebraically closed field of characteristic zero. This file
proves that the character homomorphism from the representation ring of `G` is injective. Thus a
virtual representation is determined by its character.

For the representation ring itself, every element of split `K₀` is a difference `[V] - [W]`.
A difference in the kernel has `V.character = W.character`, so the object-level theorem makes
`V` and `W` isomorphic and their difference vanishes. The object-level input is
`TauCeti.FDRep.nonempty_iso_of_character_eq`, proved in the character-theory area from Maschke
decompositions and the character pairing.

## Main results

* `TauCeti.repRingCharacter_injective`: the character homomorphism on the representation ring is
  injective.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Part I, §§2.3 and 2.5, and Part II,
  §9.1.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §§25 and 30.

This is the injectivity target in Layer 6 of
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`.
-/

public section

namespace TauCeti

universe u v

section CharacterMap

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- **The character homomorphism is injective in characteristic zero.** If a virtual difference
`[V] - [W]` has zero character, then `V` and `W` have equal characters. Semisimplicity and
`TauCeti.FDRep.nonempty_iso_of_character_eq` make them isomorphic, so their classes agree in
the representation ring. -/
theorem repRingCharacter_injective [Finite G] [IsAlgClosed k] [CharZero k] :
    Function.Injective (repRingCharacter k G) := by
  intro x y hxy
  apply sub_eq_zero.mp
  obtain ⟨V, W, hVW⟩ := SplitK0.exists_eq_sub_of (x - y)
  have hzero : repRingCharacter k G (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hchar : V.character = W.character := by
    rw [hVW, map_sub, repRingCharacter_of, repRingCharacter_of, sub_eq_zero] at hzero
    exact hzero
  obtain ⟨i⟩ := FDRep.nonempty_iso_of_character_eq V W hchar
  rw [hVW, SplitK0.of_congr i, sub_self]

end CharacterMap

end TauCeti
