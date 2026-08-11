/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# A transcribed presentation of the second Janko group

This file carries the `J₂` row of the sporadic presentation manifest required by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. It records a published two-generator, three-relator
presentation in `TauCeti.GroupPresentation`, including its exact source, generator convention,
transcription notes, and expected counts.

The presentation is the `n = 7`, order `604800` entry in Section 3 of Stoytchev's paper. In the
source's notation it is

```text
⟨a, b | aba = bab,
         ab²a = b⁵,
         (ab⁻¹ab⁻³a³b⁻¹)³a⁷ = 1⟩.
```

The source writes the exponent in the last relation as `±3`, thereby giving two presentations; this
file chooses the displayed positive exponent. Equalities are transcribed as relators by multiplying
the left-hand side by the inverse of the right-hand side. Thus the first two compiled words are
`a b a B A B` and `a b b a B B B B B`, where capitals denote inverses.

## Checks

The generator and relator counts are checked by `j2Presentation_matchesMetadata`. The stored
expressions preserve the source's powers and display each relation in the same left-to-right order;
`Relator.toWord_toFreeGroup` is the already-proved audit boundary from those expressions to the
signed words used by `PresentedGroup`.

As an independent transcription check, the exact three relators below were enumerated with GAP
4.15.1 over the trivial subgroup; the resulting finitely presented group has order `604800`,
agreeing with both the paper and GAP's Atlas group `J2`. This computation is provenance for the
transcription, not a Lean theorem, and this file asserts no order, finiteness, simplicity, or
identification result.

## Main definition

* `TauCeti.Sporadic.j2Presentation`: Stoytchev's finite presentation of `J₂`.

## References

* O. Stoytchev, *A Class of Efficient Presentations of Finite Simple Groups*,
  arXiv:2011.05660v1 (2020), Section 3, `n = 7`, order `604800` entry.
-/

public section

namespace TauCeti.Sporadic

private abbrev a : Relator (Fin 2) := .gen 0

private abbrev b : Relator (Fin 2) := .gen 1

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The word `ab⁻¹ab⁻³a³b⁻¹` occurring in Stoytchev's presentation of `J₂`. -/
private abbrev j2Word : Relator (Fin 2) :=
  a ⬝ .inv b ⬝ a ⬝ .pow (.inv b) 3 ⬝ .pow a 3 ⬝ .inv b

/-- A finite presentation of the second Janko group `J₂`, transcribed from the order `604800`
entry in Section 3 of Stoytchev's *A Class of Efficient Presentations of Finite Simple Groups*.

The source obtains this presentation by enumerating the finitely presented group and checking that
the group of order `604800` is simple. No such structural property is asserted here: this definition
records only the cited generators and relations. -/
def j2Presentation : GroupPresentation where
  generatorNames := ["a", "b"]
  source := "O. Stoytchev, A Class of Efficient Presentations of Finite Simple Groups, \
    arXiv:2011.05660v1 (2020)"
  sourceLocator := "Section 3, n = 7, order 604800 entry (the presentation labelled J_2)"
  generatorConvention := "The generators a and b of the source, in that order, so index 0 is a \
    and index 1 is b. Products are read left to right, negative exponents denote inverses, and \
    each displayed equality is imposed as a relator equal to the identity."
  transcriptionNotes := "The relations aba = bab and ab^2 a = b^5 are transcribed as \
    aba(bab)^-1 and ab^2 a b^-5. For the source's final relation \
    (a b^-1 a b^-3 a^3 b^-1)^(+/-3) a^7 = 1, this row chooses the positive exponent +3. \
    GAP 4.15.1 independently enumerates these exact three relators to order 604800."
  expectedGeneratorCount := 2
  expectedRelatorCount := 3
  transcribed :=
    [ a ⬝ b ⬝ a ⬝ .inv (b ⬝ a ⬝ b),
      a ⬝ .pow b 2 ⬝ a ⬝ .pow (.inv b) 5,
      .pow j2Word 3 ⬝ .pow a 7 ]

/-- The generator and relator counts recorded for `J₂` agree with the transcribed data. -/
theorem j2Presentation_matchesMetadata : j2Presentation.matchesMetadata := by decide

end TauCeti.Sporadic
