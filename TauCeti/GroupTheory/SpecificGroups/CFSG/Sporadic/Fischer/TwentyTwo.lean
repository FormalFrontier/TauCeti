/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# A transcribed presentation of the first Fischer group

This file carries the `Fi₂₂` row of the sporadic presentation data required by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. It records the ATLAS presentation on the standard
generators `a` and `b` as a `TauCeti.GroupPresentation`, together with its exact source, generator
convention, transcription notes, expected counts, and the decidable count check.

The thirteen relators are

```text
a², b¹³, (ab)¹¹, (ab²)²¹,
[a,b]³, [a,b²]³, [a,b³]³, [a,b⁴]², [a,b⁵]³,
[a,bab²]³, [a,b⁻¹ab⁻²]², [a,bab⁵]², [a,b²ab⁵]².
```

The source's commutator convention is `[r,s] = r⁻¹s⁻¹rs`, opposite to Mathlib's
`commutatorElement`, so each commutator is stored as `Relator.comm (.inv r) (.inv s)` as
`TauCeti.Relator` prescribes. The proved `TauCeti.Relator.toWord_toFreeGroup` is the audit boundary
between these expressions and the signed words consumed by `PresentedGroup`.

The presentation source is backed by a computation for the double cover `2·Fi₂₂`. Its twelve
base relators present the double cover, with central involution represented by both `(ab²)²¹` and
`(ab ab ab⁻³)⁵`; adjoining either as a relator kills that involution and gives `Fi₂₂`. The ATLAS
source records that the coset enumeration over the displayed involution centralizer works with
either choice, while the version 3 presentation page chooses `(ab²)²¹` as transcribed here.

As an independent check, GAP 4.15.1 with AtlasRep 2.1.9 evaluates all thirteen displayed relators
to the identity on the ATLAS standard generators in the 3510-point permutation representation of
`Fi₂₂`. This is transcription provenance rather than a Lean theorem: the file asserts no order,
finiteness, simplicity, or identification result. A separate read-through against the
`FiniteSimpleGroups` development named by the roadmap remains part of the S1 review artifact.

## Main definition

* `TauCeti.Sporadic.fi22Presentation`: the ATLAS finite presentation of `Fi₂₂`.

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, presentation `F22G1-P1`,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/F22G1-P1>.
* The relator list and its reduction to the proved `2·Fi₂₂` presentation are recorded in
  <https://brauer.maths.qmul.ac.uk/Atlas/spor/F22/mag/F22G1-P1.M> and
  <https://brauer.maths.qmul.ac.uk/Atlas/spor/F22/mag/2F22G1-P1.M>.
-/

public section

namespace TauCeti.Sporadic

private abbrev a : Relator (Fin 2) := .gen 0

private abbrev b : Relator (Fin 2) := .gen 1

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The source's commutator `[r, s] = r⁻¹ s⁻¹ r s`, represented in Mathlib's convention. -/
private abbrev sourceComm (r s : Relator (Fin 2)) : Relator (Fin 2) :=
  .comm (.inv r) (.inv s)

/-- The ATLAS finite presentation of the Fischer group `Fi₂₂` on its standard generators `a`
and `b`.

The ATLAS lists this as a presentation of the abstract group, separately from the relations used
only to recognize standard generators inside an existing group. No structural property of the
presented group is asserted here: this definition records only the cited generators and relators.
-/
def fi22Presentation : GroupPresentation where
  generatorNames := ["a", "b"]
  source := "R. A. Wilson, R. A. Parker, J. N. Bray et al., ATLAS of Finite Group \
    Representations, version 3"
  sourceLocator := "F22G1-P1, https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/F22G1-P1; the \
    relator data and the proof through the double-cover presentation are in \
    https://brauer.maths.qmul.ac.uk/Atlas/spor/F22/mag/F22G1-P1.M and \
    https://brauer.maths.qmul.ac.uk/Atlas/spor/F22/mag/2F22G1-P1.M"
  generatorConvention := "The ATLAS standard generators a and b of Fi22, with a in class 2A, \
    b of order 13, and ab of order 11, in that order, so index 0 is a and index 1 is b. \
    Products are read left to right, negative exponents denote inverses, and [r,s] denotes \
    r^-1 s^-1 r s."
  transcriptionNotes := "Transcribe the thirteen words displayed on the version 3 presentation \
    page, using (a*b^2)^21 as the fourth relator. The Magma data also gives \
    (a*b*a*b*a*b^-3)^5 as an interchangeable relator: the proof file identifies both words \
    with the central involution of 2.Fi22 and records successful index-3510 coset enumeration \
    with either one. GAP 4.15.1 with AtlasRep 2.1.9 checks the thirteen displayed relators on \
    the standard generators of the 3510-point Fi22 permutation representation. A comparison \
    with the independent FiniteSimpleGroups construction remains an S1 review artifact."
  expectedGeneratorCount := 2
  expectedRelatorCount := 13
  transcribed :=
    [ .pow a 2,
      .pow b 13,
      .pow (a ⬝ b) 11,
      .pow (a ⬝ .pow b 2) 21,
      .pow (sourceComm a b) 3,
      .pow (sourceComm a (.pow b 2)) 3,
      .pow (sourceComm a (.pow b 3)) 3,
      .pow (sourceComm a (.pow b 4)) 2,
      .pow (sourceComm a (.pow b 5)) 3,
      .pow (sourceComm a (b ⬝ a ⬝ .pow b 2)) 3,
      .pow (sourceComm a (.inv b ⬝ a ⬝ .pow (.inv b) 2)) 2,
      .pow (sourceComm a (b ⬝ a ⬝ .pow b 5)) 2,
      .pow (sourceComm a (.pow b 2 ⬝ a ⬝ .pow b 5)) 2 ]

/-- The generator and relator counts recorded for `Fi₂₂` agree with the transcribed data. -/
theorem matchesMetadata_fi22Presentation : fi22Presentation.matchesMetadata := by
  decide

end TauCeti.Sporadic
