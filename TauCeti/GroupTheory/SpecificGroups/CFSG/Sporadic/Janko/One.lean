/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# A transcribed presentation of the first Janko group

This file carries the `J₁` row of the sporadic presentation data required by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. It records the ATLAS version 3 presentation on the
standard generators `a` and `b` as a `TauCeti.GroupPresentation`, together with the source,
generator convention, transcription notes, and expected counts.

The presentation displayed by the ATLAS is

```text
⟨a, b | a² = b³ = (ab)⁷
       = (ab(abab⁻¹)³)⁵
       = (ab(abab⁻¹)⁶abab(ab⁻¹)²)² = 1⟩.
```

The structured expressions below preserve those products and powers. The previously proved
`Relator.toWord_toFreeGroup` theorem is the audit boundary between these expressions and the signed
words used by `PresentedGroup`.

As an independent transcription check, GAP 4.15.1 was used in two directions. The five relators
evaluate to the identity on the ATLAS package's independent 266-point standard generators for
`J₁`; conversely, Todd--Coxeter enumeration of the abstract presentation gives order `175560`, and
GAP constructs an isomorphism from its permutation image to the ATLAS group. This computation is
provenance for the transcription, not a Lean theorem. This file asserts no order, finiteness,
simplicity, or identification result.

## Main definition

* `TauCeti.Sporadic.j1Presentation`: the ATLAS finite presentation of `J₁`.

## References

* R. A. Wilson, R. A. Parker, and J. N. Bray, *ATLAS of Finite Group Representations*,
  version 3, `J₁`, section "Presentation",
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J1/>.
-/

public section

namespace TauCeti.Sporadic

private abbrev a : Relator (Fin 2) := .gen 0

private abbrev b : Relator (Fin 2) := .gen 1

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The subword `abab⁻¹` repeated in the two long ATLAS relators for `J₁`. -/
private abbrev repeatedWord : Relator (Fin 2) :=
  a ⬝ b ⬝ a ⬝ .inv b

/-- The word `ab(abab⁻¹)³`, whose fifth power is an ATLAS relator for `J₁`. -/
private abbrev fifthPowerBase : Relator (Fin 2) :=
  a ⬝ b ⬝ .pow repeatedWord 3

/-- The word `ab(abab⁻¹)⁶abab(ab⁻¹)²`, whose square is an ATLAS relator for `J₁`. -/
private abbrev squareBase : Relator (Fin 2) :=
  a ⬝ b ⬝ .pow repeatedWord 6 ⬝ a ⬝ b ⬝ a ⬝ b ⬝ .pow (a ⬝ .inv b) 2

/-- The ATLAS version 3 finite presentation of the first Janko group `J₁` on its standard
generators `a` and `b`.

The ATLAS supplies a full presentation of the abstract group, rather than the semi-presentation
used elsewhere in the database to recognize standard generators in an already constructed group.
No structural property of the presented group is asserted here: this definition records only the
cited generators and relations. -/
def j1Presentation : GroupPresentation where
  generatorNames := ["a", "b"]
  source := "R. A. Wilson, R. A. Parker, and J. N. Bray, ATLAS of Finite Group \
    Representations, version 3"
  sourceLocator := "J_1 page, Presentation section, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J1/"
  generatorConvention := "The ATLAS standard generators a and b, in that order, so index 0 is a \
    and index 1 is b. Products are read left to right and negative exponents denote inverses."
  transcriptionNotes := "The five displayed words are stored as five relators equal to the \
    identity. GAP 4.15.1 checks them on the independent ATLAS 266-point generators; enumeration \
    of this abstract presentation gives order 175560 and an isomorphism to the ATLAS group."
  expectedGeneratorCount := 2
  expectedRelatorCount := 5
  transcribed :=
    [ .pow a 2,
      .pow b 3,
      .pow (a ⬝ b) 7,
      .pow fifthPowerBase 5,
      .pow squareBase 2 ]

/-- The generator and relator counts recorded for `J₁` agree with the transcribed data. -/
theorem j1Presentation_matchesMetadata : j1Presentation.matchesMetadata := by decide

end TauCeti.Sporadic
