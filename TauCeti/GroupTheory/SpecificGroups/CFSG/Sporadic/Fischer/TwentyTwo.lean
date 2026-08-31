/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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

The row is a sealed definition, so it publishes an equation for each of its fields: the transcribed
relator expressions with their generator indices written out, and the provenance a manifest row
exists to record. Together with `TauCeti.GroupPresentation.relators_def` and
`TauCeti.GroupPresentation.mem_relatorSet_iff` the first of those determines the compiled words and
the relations defining the presented group, so a consumer reasons about the row without unfolding
it.

Three decidable checks accompany those equations. The relator lengths and their total record the
compiled data one word at a time and in aggregate. Cyclic reducedness shows that cyclic reduction
does not shorten any of these relators, so `328` is also their post-reduction total. The ATLAS page
records no length for this presentation, so the total here states the transcription for a reviewer
to compare with the source, rather than checking it against a recorded number.

## Main definitions and results

* `TauCeti.Sporadic.fi22Presentation`: the ATLAS finite presentation of `Fi₂₂`.
* `TauCeti.Sporadic.fi22Presentation_transcribed` and the equations for the remaining fields: the
  characterization of the sealed row.
* `TauCeti.Sporadic.fi22Presentation_map_length_relators`,
  `TauCeti.Sporadic.fi22Presentation_totalLength` and
  `TauCeti.Sporadic.fi22Presentation_relatorsCyclicallyReduced`: the three checks on the compiled
  words.

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, presentation `F22G1-P1`,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/F22G1-P1>.
* The relator list and its reduction to the proved `2·Fi₂₂` presentation are recorded in
  <https://brauer.maths.qmul.ac.uk/Atlas/spor/F22/mag/F22G1-P1.M> and
  <https://brauer.maths.qmul.ac.uk/Atlas/spor/F22/mag/2F22G1-P1.M>.
* The presentation-row characterization and audit theorem scaffold is adapted from the Janko-row
  formalization in <https://github.com/TauCetiProject/TauCeti/pull/5283>.
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

/-- The generator names recorded for `Fi₂₂`. The row's body is sealed, so this is what lets a
consumer see that it is a two-generator presentation. -/
@[simp]
theorem fi22Presentation_generatorNames : fi22Presentation.generatorNames = ["a", "b"] := by
  simp [fi22Presentation]

/-- The source recorded for `Fi₂₂`. The row's body is sealed, so this equation is what publishes
the citation itself, rather than only the row's name, to a downstream audit. -/
@[simp]
theorem fi22Presentation_source :
    fi22Presentation.source = "R. A. Wilson, R. A. Parker, J. N. Bray et al., ATLAS of Finite \
      Group Representations, version 3" := by
  simp [fi22Presentation]

/-- The locator recorded for `Fi₂₂`, pointing at the presentation inside its source. -/
@[simp]
theorem fi22Presentation_sourceLocator :
    fi22Presentation.sourceLocator = "F22G1-P1, \
      https://brauer.maths.qmul.ac.uk/Atlas/v3/pres/F22G1-P1; the relator data and the proof \
      through the double-cover presentation are in \
      https://brauer.maths.qmul.ac.uk/Atlas/spor/F22/mag/F22G1-P1.M and \
      https://brauer.maths.qmul.ac.uk/Atlas/spor/F22/mag/2F22G1-P1.M" := by
  simp [fi22Presentation]

/-- The generator convention recorded for `Fi₂₂`, fixing which generator each relator index names
and which of the two commutator conventions the source uses. -/
@[simp]
theorem fi22Presentation_generatorConvention :
    fi22Presentation.generatorConvention = "The ATLAS standard generators a and b of Fi22, with a \
      in class 2A, b of order 13, and ab of order 11, in that order, so index 0 is a and index 1 \
      is b. Products are read left to right, negative exponents denote inverses, and [r,s] \
      denotes r^-1 s^-1 r s." := by
  simp [fi22Presentation]

/-- The transcription notes recorded for `Fi₂₂`. -/
@[simp]
theorem fi22Presentation_transcriptionNotes :
    fi22Presentation.transcriptionNotes = "Transcribe the thirteen words displayed on the version \
      3 presentation page, using (a*b^2)^21 as the fourth relator. The Magma data also gives \
      (a*b*a*b*a*b^-3)^5 as an interchangeable relator: the proof file identifies both words with \
      the central involution of 2.Fi22 and records successful index-3510 coset enumeration with \
      either one. GAP 4.15.1 with AtlasRep 2.1.9 checks the thirteen displayed relators on the \
      standard generators of the 3510-point Fi22 permutation representation. A comparison with \
      the independent FiniteSimpleGroups construction remains an S1 review artifact." := by
  simp [fi22Presentation]

/-- The generator count `Fi₂₂`'s source states. With
`TauCeti.Sporadic.fi22Presentation_generatorNames` this is what makes
`TauCeti.Sporadic.fi22Presentation_matchesMetadata` an equation between two visible numbers. -/
@[simp]
theorem fi22Presentation_expectedGeneratorCount : fi22Presentation.expectedGeneratorCount = 2 := by
  simp [fi22Presentation]

/-- The relator count `Fi₂₂`'s source states. With
`TauCeti.Sporadic.fi22Presentation_transcribed` this is what makes
`TauCeti.Sporadic.fi22Presentation_matchesMetadata` an equation between two visible numbers. -/
@[simp]
theorem fi22Presentation_expectedRelatorCount : fi22Presentation.expectedRelatorCount = 13 := by
  simp [fi22Presentation]

/-- The relator expressions transcribed for `Fi₂₂`, with their generator indices written out and
the private abbreviations of this file expanded.

The row's body is sealed, so this is the equation that characterizes it: with
`TauCeti.GroupPresentation.relators_def` it determines the compiled words, and with
`TauCeti.GroupPresentation.mem_relatorSet_iff` it determines the relations defining
`TauCeti.GroupPresentation.Group`, so a consumer never has to unfold the row. Index `0` is the
generator `a` and index `1` is `b`, and the bounds come from
`TauCeti.Sporadic.fi22Presentation_generatorNames`. `Relator.comm` follows Mathlib's convention
`⁅r, s⁆ = r s r⁻¹ s⁻¹`, so each source commutator `[r,s] = r⁻¹ s⁻¹ r s` appears here as
`Relator.comm` applied to the two inverses. -/
@[simp]
theorem fi22Presentation_transcribed :
    fi22Presentation.transcribed =
      [ -- a²
        .pow (.gen ⟨0, by simp⟩) 2,
        -- b¹³
        .pow (.gen ⟨1, by simp⟩) 13,
        -- (ab)¹¹
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩) 11,
        -- (ab²)²¹
        .pow (.gen ⟨0, by simp⟩ ⬝ .pow (.gen ⟨1, by simp⟩) 2) 21,
        -- [a,b]³
        .pow (.comm (.inv (.gen ⟨0, by simp⟩)) (.inv (.gen ⟨1, by simp⟩))) 3,
        -- [a,b²]³
        .pow (.comm (.inv (.gen ⟨0, by simp⟩)) (.inv (.pow (.gen ⟨1, by simp⟩) 2))) 3,
        -- [a,b³]³
        .pow (.comm (.inv (.gen ⟨0, by simp⟩)) (.inv (.pow (.gen ⟨1, by simp⟩) 3))) 3,
        -- [a,b⁴]²
        .pow (.comm (.inv (.gen ⟨0, by simp⟩)) (.inv (.pow (.gen ⟨1, by simp⟩) 4))) 2,
        -- [a,b⁵]³
        .pow (.comm (.inv (.gen ⟨0, by simp⟩)) (.inv (.pow (.gen ⟨1, by simp⟩) 5))) 3,
        -- [a,bab²]³
        .pow (.comm (.inv (.gen ⟨0, by simp⟩))
          (.inv (.gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .pow (.gen ⟨1, by simp⟩) 2))) 3,
        -- [a,b⁻¹ab⁻²]²
        .pow (.comm (.inv (.gen ⟨0, by simp⟩))
          (.inv (.inv (.gen ⟨1, by simp⟩) ⬝ .gen ⟨0, by simp⟩ ⬝
            .pow (.inv (.gen ⟨1, by simp⟩)) 2))) 2,
        -- [a,bab⁵]²
        .pow (.comm (.inv (.gen ⟨0, by simp⟩))
          (.inv (.gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .pow (.gen ⟨1, by simp⟩) 5))) 2,
        -- [a,b²ab⁵]²
        .pow (.comm (.inv (.gen ⟨0, by simp⟩))
          (.inv (.pow (.gen ⟨1, by simp⟩) 2 ⬝ .gen ⟨0, by simp⟩ ⬝
            .pow (.gen ⟨1, by simp⟩) 5))) 2 ] := by
  simp [fi22Presentation]

/-- The generator and relator counts recorded for `Fi₂₂` agree with the transcribed data. -/
theorem fi22Presentation_matchesMetadata : fi22Presentation.matchesMetadata := by
  decide

/-- The lengths of the thirteen compiled relator words for `Fi₂₂`, in the order of the source.

Reading the counts off one relator at a time is what lets a reviewer locate a discrepancy, rather
than only observe one in the total of `TauCeti.Sporadic.fi22Presentation_totalLength`. -/
theorem fi22Presentation_map_length_relators :
    fi22Presentation.relators.map List.length =
      [2, 13, 22, 63, 12, 18, 24, 20, 36, 30, 20, 32, 36] := by
  simp [GroupPresentation.relators_def, fi22Presentation]

/-- The compiled relator words for `Fi₂₂` have `328` letters in total. The ATLAS page records no
presentation length, so this figure states the transcribed data for a reviewer to compare with the
source, rather than checking it against a recorded number. -/
theorem fi22Presentation_totalLength : fi22Presentation.totalLength = 328 := by
  rw [GroupPresentation.totalLength_def, fi22Presentation_map_length_relators]
  decide

/-- Every compiled relator word for `Fi₂₂` is cyclically reduced. Thus cyclic reduction does not
shorten any relator, so `TauCeti.Sporadic.fi22Presentation_totalLength` is also the post-reduction
total. -/
theorem fi22Presentation_relatorsCyclicallyReduced :
    fi22Presentation.relatorsCyclicallyReduced := by
  simp only [GroupPresentation.relatorsCyclicallyReduced_iff, GroupPresentation.relators_def,
    fi22Presentation, List.map_cons, List.map_nil, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_inv, Relator.toWord_comm, Relator.toWord_gen]
  decide

end TauCeti.Sporadic
