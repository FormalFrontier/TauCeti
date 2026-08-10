/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.GroupTheory.PresentedGroup
public import TauCeti.GroupTheory.Presentation.Relator

/-!
# Auditable finite group presentations

This file packages a finite group presentation together with the metadata needed to audit a
transcription from a published source. The generator-name list alone fixes the relator index type
to `Fin generatorNames.length`, so the relator arity cannot disagree with the generator names. The
generator and relator counts stated by the source are separate metadata, checked against the
transcribed data by `TauCeti.GroupPresentation.matchesMetadata`.

The stored relators are human-readable `TauCeti.Relator` expressions. They are compiled to
Mathlib's signed words and then interpreted by `FreeGroup.mk`; the resulting finite list of
relations, regarded as a set, defines `TauCeti.GroupPresentation.Group` using Mathlib's
`PresentedGroup`.

## Main definitions

* `TauCeti.GroupPresentation`: cited presentation data and its transcription metadata.
* `TauCeti.GroupPresentation.relators`: the compiled signed words.
* `TauCeti.GroupPresentation.totalLength`: the number of letters in the compiled words, for checking
  against a published presentation length.
* `TauCeti.GroupPresentation.relatorSet`: the relations as free-group elements.
* `TauCeti.GroupPresentation.Group`: the group defined by the presentation.
* `TauCeti.GroupPresentation.matchesMetadata`: the decidable generator and relator count check.

## References

This file implements the finite-presentation metadata format in milestone S0 of
`TauCetiRoadmap/CFSGStatement/README.md`. Its record fields and dependent-arity design are adapted
from the target signatures in the human-owned roadmap's `CFSGStatement/Suggested.lean`.
-/

public section

namespace TauCeti

/-- A finite group presentation together with auditable source and transcription metadata.

The source must be a full presentation of the abstract group, not a semi-presentation for
recognizing generators in a group already constructed elsewhere. `generatorNames` alone determines
the relator arity; `expectedGeneratorCount` is retained only as metadata checked by
`matchesMetadata`.

There is deliberately no checksum field: without a pinned normalization and algorithm, a checksum
would not be a reproducible check on the transcribed expressions. -/
structure GroupPresentation where
  /-- Generator names, in the order used by the relator indices. -/
  generatorNames : List String
  /-- Bibliographic citation or database name for the full presentation. -/
  source : String
  /-- Page, theorem number, or stable database identifier locating the presentation. -/
  sourceLocator : String
  /-- The source's generator and commutator conventions. -/
  generatorConvention : String
  /-- Notes explaining any normalization or conversion made during transcription. -/
  transcriptionNotes : String
  /-- The number of generators stated by the source. -/
  expectedGeneratorCount : ℕ
  /-- The number of relators stated by the source. -/
  expectedRelatorCount : ℕ
  /-- Relators transcribed in the generator order recorded by `generatorNames`. -/
  transcribed : List (Relator (Fin generatorNames.length))

namespace GroupPresentation

/-- The number of generators in a presentation, determined by its generator-name list. -/
abbrev generatorCount (P : GroupPresentation) : ℕ := P.generatorNames.length

/-- The relator expressions compiled to left-to-right signed words.

The body is exposed so that the compiled words of a transcribed presentation reduce in the module
that carries it, where they are checked letter by letter against the published source. -/
@[expose]
def relators (P : GroupPresentation) : List (PresentationWord (Fin P.generatorCount)) :=
  P.transcribed.map Relator.toWord

/-- Compilation preserves the number of relators. -/
@[simp]
theorem length_relators (P : GroupPresentation) : P.relators.length = P.transcribed.length := by
  simp [relators]

/-- The compiled words are exactly the compilations of the transcribed expressions. -/
@[simp]
theorem mem_relators_iff (P : GroupPresentation) (w : PresentationWord (Fin P.generatorCount)) :
    w ∈ P.relators ↔ ∃ t ∈ P.transcribed, t.toWord = w := by
  simp [relators]

/-- The compiled relator words, with each generator index displayed as a natural number.

A transcription is audited by comparing the compiled letters with the published relators, and this
form of them is the one to state such a comparison against: the index type of a word depends on the
generator-name list, whereas the letters here do not, so the comparison needs no arithmetic on that
dependency. -/
@[expose]
def relatorLetters (P : GroupPresentation) : List (List (ℕ × Bool)) :=
  P.relators.map (List.map fun letter => (letter.1.val, letter.2))

/-- The total number of letters in the compiled relator words.

Sources for finite presentations customarily publish this figure, usually calling it the length of
the presentation, so comparing it with the transcribed data is a third decidable check on a
transcription alongside the two counts of `TauCeti.GroupPresentation.matchesMetadata`. A published
length is normally measured after free and cyclic reduction of each relator, so a row using it as a
check should also record that its compiled words are reduced. -/
@[expose]
def totalLength (P : GroupPresentation) : ℕ := (P.relators.map List.length).sum

/-- The compiled relations, interpreted as elements of the free group. -/
def relatorSet (P : GroupPresentation) : Set (FreeGroup (Fin P.generatorCount)) :=
  {r | r ∈ P.relators.map FreeGroup.mk}

/-- The relations are exactly the free-group elements denoted by the transcribed expressions.

This is stated against `Relator.toFreeGroup` rather than against the compiled words, so a consumer
discharging the relations of `PresentedGroup` never has to unfold the compiler. -/
@[simp]
theorem mem_relatorSet_iff (P : GroupPresentation) (r : FreeGroup (Fin P.generatorCount)) :
    r ∈ P.relatorSet ↔ ∃ t ∈ P.transcribed, t.toFreeGroup = r := by
  simp [relatorSet]

/-- The group defined by the generators and compiled relations of a presentation. -/
abbrev Group (P : GroupPresentation) : Type :=
  PresentedGroup P.relatorSet

/-- The recorded generator and relator counts agree with the transcribed data.

This checks transcription metadata only; it makes no claim that the source presents a named group
or that the transcription agrees with the source. -/
def matchesMetadata (P : GroupPresentation) : Prop :=
  P.generatorCount = P.expectedGeneratorCount ∧
    P.transcribed.length = P.expectedRelatorCount

/-- The metadata check unfolds to its two count equalities. -/
@[simp]
theorem matchesMetadata_iff (P : GroupPresentation) :
    P.matchesMetadata ↔
      P.generatorCount = P.expectedGeneratorCount ∧
        P.transcribed.length = P.expectedRelatorCount :=
  Iff.rfl

instance (P : GroupPresentation) : Decidable P.matchesMetadata :=
  decidable_of_iff _ (matchesMetadata_iff P).symm

/-- A transcribed row discharges its count check by `decide`. The record below is an illustration
of the format, not a transcription of a published source. -/
example : GroupPresentation.matchesMetadata
    { generatorNames := ["a", "b"]
      source := "illustrative record"
      sourceLocator := "none"
      generatorConvention := "Mathlib's commutator bracket"
      transcriptionNotes := "no normalization was needed"
      expectedGeneratorCount := 2
      expectedRelatorCount := 3
      transcribed :=
        [.pow (.gen 0) 2, .pow (.gen 1) 3, .pow (.mul (.gen 0) (.gen 1)) 2] } := by
  decide

end GroupPresentation

end TauCeti
