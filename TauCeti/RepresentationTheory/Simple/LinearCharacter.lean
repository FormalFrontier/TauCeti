/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.LinearCharacter
public import TauCeti.RepresentationTheory.Simple.Basic

/-!
# The simple object carried by a linear character

`Representation.ofLinearCharacter χ` is the representation of `G` on the line `k` in which `g` acts
by multiplication by the unit `χ g`. This file records what that construction contributes to the
list of simple objects of `FDRep k G`: it is irreducible, being carried by a line, and the linear
character is recovered from the isomorphism class of the object it names.

The last statement strengthens `Representation.ofLinearCharacter_injective`, which recovers `χ`
only from the representation on the nose: here merely being *isomorphic* in `FDRep k G` already
forces the characters to agree, because the character of `ofLinearCharacter χ` is `χ` itself and
characters are isomorphism invariants. So distinct linear characters index pairwise
non-isomorphic simple objects, one for each degree-one row of the character table.

## Main statements

* `Representation.isIrreducible_ofLinearCharacter`, `Representation.simple_ofLinearCharacter`:
  a linear character is irreducible, being carried by a line, hence a simple object of
  `FDRep k G`.
* `Representation.eq_of_nonempty_iso_ofLinearCharacter`: two linear characters whose
  representations are isomorphic are equal.

## References

Linear characters are the degree-one rows of a character table; see
[the character-theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).
-/

public section

open CategoryTheory TauCeti TauCeti.Representation

namespace Representation

variable {k : Type*} [Field k] {G : Type*} [Monoid G]

/-- **A linear character is irreducible**: it is carried by a line. -/
instance isIrreducible_ofLinearCharacter (χ : G →* kˣ) :
    (ofLinearCharacter χ).IsIrreducible :=
  isIrreducible_of_finrank_eq_one _ (Module.finrank_self k)

/-- The finite-dimensional object carrying a linear character is a simple object of
`FDRep k G`. -/
instance simple_ofLinearCharacter (χ : G →* kˣ) : Simple (FDRep.of (ofLinearCharacter χ)) := by
  rw [FDRep.simple_iff_isIrreducible]
  exact isIrreducible_ofLinearCharacter χ

/-- **Isomorphic linear characters are equal.** An isomorphism of the two one-dimensional
representations identifies their characters, and the character of `ofLinearCharacter χ` is `χ`.
The characters of `ofLinearCharacter χ` and of `FDRep.of (ofLinearCharacter χ)` agree
definitionally, `FDRep.of` changing neither the carrier nor the action. -/
theorem eq_of_nonempty_iso_ofLinearCharacter {χ φ : G →* kˣ}
    (h : Nonempty (FDRep.of (ofLinearCharacter χ) ≅ FDRep.of (ofLinearCharacter φ))) : χ = φ := by
  obtain ⟨e⟩ := h
  ext g
  rw [← char_ofLinearCharacter χ g, ← char_ofLinearCharacter φ g]
  exact congrFun (FDRep.char_iso e) g

end Representation
