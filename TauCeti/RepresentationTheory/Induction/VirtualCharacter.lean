/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Induction.Character
public import TauCeti.RepresentationTheory.CharacterTable.VirtualCharacter

/-!
# Induction and virtual characters

This file records the compatibility between induction of finite-dimensional representations and
the virtual-character lattice.

## Main statement

* `TauCeti.ClassFunction.ind_ofFDRep_mem_virtualCharacters`: induction takes the character of a
  finite-dimensional subgroup representation to a virtual character of the ambient group.

## References

This supplies a compatibility needed by the virtual-character and Artin-induction targets of
Layer 6 in
`TauCetiRoadmap/RepresentationTheory/InductionRestriction/README.md`.
-/

public section

namespace TauCeti

namespace ClassFunction

universe u

variable {k G : Type u} [Field k] [Group G]

/-- **A character induced from a subgroup is a virtual character.**  Inducing the class function of
a finite-dimensional representation gives the class function of the induced representation
(`TauCeti.ClassFunction.ind_ofFDRep`), and a character is a virtual character.  This is deliberately
not a simp lemma: its left-hand side reduces through `ind_ofFDRep` to the existing
`TauCeti.character_mem_virtualCharacters` simp lemma. -/
theorem ind_ofFDRep_mem_virtualCharacters (S : Subgroup G) [S.FiniteIndex] (A : FDRep k S) :
    ((ind S (ofFDRep A) : ClassFunction k G) : G → k) ∈ virtualCharacters k G := by
  rw [ClassFunction.ind_ofFDRep]
  have hcharacter :
      ((ofFDRep (indFDRep (k := k) (G := G) A) : ClassFunction k G) : G → k) =
        (indFDRep (k := k) (G := G) A).character :=
    funext fun g => ofFDRep_apply _ g
  rw [hcharacter]
  exact character_mem_virtualCharacters _

end ClassFunction

end TauCeti
