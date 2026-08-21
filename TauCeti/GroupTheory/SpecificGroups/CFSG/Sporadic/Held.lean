/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# A transcribed presentation of the Held group

This file carries the `He` row of the sporadic presentation data required by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. It records John Bray's ATLAS version 3 presentation on
the standard generators `a` and `b` as a `TauCeti.GroupPresentation`, together with the source,
generator convention, transcription notes, and expected counts.

The presentation displayed by the ATLAS is

```text
⟨a, b | a² = b⁷ = (ab)¹⁷ = [a,b]⁶ = [a,b³]⁵
       = [a,babab⁻¹abab]
       = (ab)⁴ab²ab⁻³ababab⁻¹ab³ab⁻²ab² = 1⟩.
```

The ATLAS commutator convention is `[r,s] = r⁻¹s⁻¹rs`, opposite to Mathlib's
`commutatorElement`. Accordingly each displayed commutator is stored using
`Relator.comm (.inv r) (.inv s)`, as prescribed by `Relator`'s API. The structured expressions
otherwise preserve the displayed products and powers. The proved `Relator.toWord_toFreeGroup`
theorem is the audit boundary between these expressions and the signed words used by
`PresentedGroup`.

GAP 4.15.1 with AtlasRep 2.1.9 independently checks the seven transcribed relations on the
ATLAS 2058-point standard generators; those generators yield a simple group of order
`4030387200`. This computation is provenance for the transcription, not a Lean theorem. This file
asserts no order, finiteness, simplicity, or identification result.

## Main definition

* `TauCeti.Sporadic.hePresentation`: John Bray's ATLAS finite presentation of `He`.

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, presentation `HeG1-P1`, contributed by John Bray,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/HeG1-P1>.
-/

public section

namespace TauCeti.Sporadic

private abbrev a : Relator (Fin 2) := .gen 0

private abbrev b : Relator (Fin 2) := .gen 1

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The word `babab⁻¹abab` in the long commutator of Bray's presentation. -/
private abbrev commutatorWord : Relator (Fin 2) :=
  b ⬝ a ⬝ b ⬝ a ⬝ .inv b ⬝ a ⬝ b ⬝ a ⬝ b

/-- The final relator in Bray's presentation, before setting it equal to the identity. -/
private abbrev finalWord : Relator (Fin 2) :=
  .pow (a ⬝ b) 4 ⬝ a ⬝ .pow b 2 ⬝ a ⬝ .pow (.inv b) 3 ⬝
    a ⬝ b ⬝ a ⬝ b ⬝ a ⬝ .inv b ⬝ a ⬝ .pow b 3 ⬝ a ⬝
    .pow (.inv b) 2 ⬝ a ⬝ .pow b 2

/-- John Bray's ATLAS version 3 finite presentation of the Held group `He` on its standard
generators `a` and `b`.

The ATLAS lists this as a full presentation of the abstract group, separately from the
semi-presentation used to recognize standard generators in a group already constructed. No
structural property of the presented group is asserted here: this definition records only the
cited generators and relations. -/
def hePresentation : GroupPresentation where
  generatorNames := ["a", "b"]
  source := "R. A. Wilson, R. A. Parker, J. N. Bray et al., ATLAS of Finite Group \
    Representations, version 3; presentation contributed by John Bray"
  sourceLocator := "HeG1-P1, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/HeG1-P1"
  generatorConvention := "The ATLAS standard generators a and b, in that order, so index 0 is a \
    and index 1 is b. Products are read left to right, negative exponents denote inverses, and \
    [r,s] denotes r^-1 s^-1 r s."
  transcriptionNotes := "The seven displayed words are stored as seven relators equal to the \
    identity. ATLAS distinguishes HeG1-P1 from its semi-presentation. GAP 4.15.1 with AtlasRep \
    2.1.9 checks these relators on the independent ATLAS 2058-point generators, which generate a \
    simple group of order 4030387200."
  expectedGeneratorCount := 2
  expectedRelatorCount := 7
  transcribed :=
    [ .pow a 2,
      .pow b 7,
      .pow (a ⬝ b) 17,
      .pow (.comm (.inv a) (.inv b)) 6,
      .pow (.comm (.inv a) (.inv (.pow b 3))) 5,
      .comm (.inv a) (.inv commutatorWord),
      finalWord ]

/-- The generator and relator counts recorded for `He` agree with the transcribed data. -/
theorem hePresentation_matchesMetadata : hePresentation.matchesMetadata := by decide

end TauCeti.Sporadic
