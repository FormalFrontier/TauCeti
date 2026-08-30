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

The row is a sealed definition, so it publishes an equation for each of its fields: the transcribed
relator expressions with their generator indices written out, and the provenance a manifest row
exists to record. Together with `TauCeti.GroupPresentation.relators_def` and
`TauCeti.GroupPresentation.mem_relatorSet_iff` the first of those determines the compiled words and
the relations defining the presented group, so a consumer reasons about the row without unfolding
it.

Three decidable checks accompany those equations. The relator lengths and their total record the
compiled data one word at a time and in aggregate, and cyclic reducedness is what makes such a
letter count comparable with a published presentation length, since both are measured after free
and cyclic reduction of each relator. This row records no published length, so the total here
states the transcription for a reviewer to compare with the source, rather than checking it against
a recorded number.

## Main definitions and results

* `TauCeti.Sporadic.j1Presentation`: the ATLAS finite presentation of `J₁`.
* `TauCeti.Sporadic.j1Presentation_transcribed` and the equations for the remaining fields: the
  characterization of the sealed row.
* `TauCeti.Sporadic.j1Presentation_map_length_relators`,
  `TauCeti.Sporadic.j1Presentation_totalLength` and
  `TauCeti.Sporadic.j1Presentation_relatorsCyclicallyReduced`: the three checks on the compiled
  words.

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

/-- The generator names recorded for `J₁`. The row's body is sealed, so this is what lets a
consumer see that it is a two-generator presentation. -/
@[simp]
theorem j1Presentation_generatorNames : j1Presentation.generatorNames = ["a", "b"] := by
  simp [j1Presentation]

/-- The source recorded for `J₁`. The row's body is sealed, so this equation is what publishes the
citation itself, rather than only the row's name, to a downstream audit. -/
@[simp]
theorem j1Presentation_source :
    j1Presentation.source = "R. A. Wilson, R. A. Parker, and J. N. Bray, ATLAS of Finite Group \
      Representations, version 3" := by
  simp [j1Presentation]

/-- The locator recorded for `J₁`, pointing at the presentation inside its source. -/
@[simp]
theorem j1Presentation_sourceLocator :
    j1Presentation.sourceLocator =
      "J_1 page, Presentation section, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/J1/" := by
  simp [j1Presentation]

/-- The generator convention recorded for `J₁`, fixing which generator each relator index names. -/
@[simp]
theorem j1Presentation_generatorConvention :
    j1Presentation.generatorConvention = "The ATLAS standard generators a and b, in that order, \
      so index 0 is a and index 1 is b. Products are read left to right and negative exponents \
      denote inverses." := by
  simp [j1Presentation]

/-- The transcription notes recorded for `J₁`. -/
@[simp]
theorem j1Presentation_transcriptionNotes :
    j1Presentation.transcriptionNotes = "The five displayed words are stored as five relators \
      equal to the identity. GAP 4.15.1 checks them on the independent ATLAS 266-point \
      generators; enumeration of this abstract presentation gives order 175560 and an isomorphism \
      to the ATLAS group." := by
  simp [j1Presentation]

/-- The generator count `J₁`'s source states. With
`TauCeti.Sporadic.j1Presentation_generatorNames` this is what makes
`TauCeti.Sporadic.j1Presentation_matchesMetadata` an equation between two visible numbers. -/
@[simp]
theorem j1Presentation_expectedGeneratorCount : j1Presentation.expectedGeneratorCount = 2 := by
  simp [j1Presentation]

/-- The relator count `J₁`'s source states; see
`TauCeti.Sporadic.j1Presentation_expectedGeneratorCount`. -/
@[simp]
theorem j1Presentation_expectedRelatorCount : j1Presentation.expectedRelatorCount = 5 := by
  simp [j1Presentation]

/-- The relator expressions transcribed for `J₁`, with their generator indices written out and the
private abbreviations of this file expanded.

The row's body is sealed, so this is the equation that characterizes it: with
`TauCeti.GroupPresentation.relators_def` it determines the compiled words, and with
`TauCeti.GroupPresentation.mem_relatorSet_iff` it determines the relations defining
`TauCeti.GroupPresentation.Group`, so a consumer never has to unfold the row. Index `0` is the
generator `a` and index `1` is `b`, and the bounds come from
`TauCeti.Sporadic.j1Presentation_generatorNames`. -/
@[simp]
theorem j1Presentation_transcribed :
    j1Presentation.transcribed =
      [ -- a²
        .pow (.gen ⟨0, by simp⟩) 2,
        -- b³
        .pow (.gen ⟨1, by simp⟩) 3,
        -- (ab)⁷
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩) 7,
        -- (ab(abab⁻¹)³)⁵
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝
          .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝
            .inv (.gen ⟨1, by simp⟩)) 3) 5,
        -- (ab(abab⁻¹)⁶abab(ab⁻¹)²)²
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝
          .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝
            .inv (.gen ⟨1, by simp⟩)) 6 ⬝
          .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩ ⬝
          .pow (.gen ⟨0, by simp⟩ ⬝ .inv (.gen ⟨1, by simp⟩)) 2) 2 ] := by
  simp [j1Presentation]

/-- The generator and relator counts recorded for `J₁` agree with the transcribed data. -/
theorem j1Presentation_matchesMetadata : j1Presentation.matchesMetadata := by decide

/-- The lengths of the five compiled relator words for `J₁`, in the order of the source.

Reading the counts off one relator at a time is what lets a reviewer locate a discrepancy, rather
than only observe one in the total of `TauCeti.Sporadic.j1Presentation_totalLength`. -/
theorem j1Presentation_map_length_relators :
    j1Presentation.relators.map List.length = [2, 3, 14, 70, 68] := by
  simp [GroupPresentation.relators_def, j1Presentation]

/-- The compiled relator words for `J₁` have `157` letters in total. The row records no published
length, so this figure states the transcribed data for a reviewer to compare with the source,
rather than checking it against a recorded number. -/
theorem j1Presentation_totalLength : j1Presentation.totalLength = 157 := by
  rw [GroupPresentation.totalLength_def, j1Presentation_map_length_relators]
  decide

/-- Every compiled relator word for `J₁` is cyclically reduced. This is what makes the letter count
of `TauCeti.Sporadic.j1Presentation_totalLength` comparable with a published presentation length,
which is measured after free and cyclic reduction of each relator. -/
theorem j1Presentation_relatorsCyclicallyReduced :
    j1Presentation.relatorsCyclicallyReduced := by
  simp only [GroupPresentation.relatorsCyclicallyReduced_iff, GroupPresentation.relators_def,
    j1Presentation, List.map_cons, List.map_nil, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_inv, Relator.toWord_gen]
  decide

end TauCeti.Sporadic
