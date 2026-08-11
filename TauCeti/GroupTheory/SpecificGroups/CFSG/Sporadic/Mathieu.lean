/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# Transcribed presentations of the Mathieu groups `M₁₁`, `M₁₂` and `M₂₂`

This file carries three rows of the sporadic presentation manifest: cited finite presentations of
the Mathieu groups `M₁₁`, `M₁₂` and `M₂₂`, transcribed from published sources in which each
presentation is *proved* to define the named group. Each row is a `TauCeti.GroupPresentation`, so it
records the generator names, the source and a locator inside it, the generator convention, the
transcription notes, and the generator and relator counts stated by the source, together with the
relator expressions themselves.

Four decidable checks accompany every row. The first is the generator and relator counts. The second
spells the compiled words out letter by letter, so that a reviewer comparing the Lean data with the
source never has to unfold the relator compiler. The third reads off from those letters the total
number of them, against the length published by the source. The fourth is that every compiled word
is cyclically reduced, which is what makes the letter count comparable with a published length: both
sources measure length after free and cyclic reduction of each relator.

The rows themselves are sealed definitions, so each also carries the equation that characterizes it,
spelling out its transcribed relator expressions with their generator indices. Together with
`TauCeti.GroupPresentation.relators_def` and `TauCeti.GroupPresentation.mem_relatorSet_iff`, and
with the interpretation equations of `TauCeti.Relator.toFreeGroup`, that equation determines the
compiled words and the relations defining the presented group, so a consumer downstream of this
file reasons about a row without unfolding it. Each row likewise publishes an equation for every
one of its metadata fields — the source, the locator, the generator convention, the transcription
notes and the two counts the source states — so an audit downstream sees the provenance a manifest
row exists to record, and not merely the row's name.

## The manifest rows

| Name | Source | Locator | Generators | Relators | Length |
| --- | --- | --- | --- | --- | --- |
| `M₁₁` | Campbell--Havas--Ramsay--Robertson | Table 2 row `M11`, Section 5.8 | 2 | 2 | 19 |
| `M₁₂` | Campbell--Havas--Ramsay--Robertson | Table 2 row `M12`, Section 5.17 | 2 | 3 | 29 |
| `M₂₂` | Conder--Havas--Ramsay | Section 3.4, p. 40 | 2 | 3 | 30 |

Both sources prove their presentations by coset enumeration over the trivial subgroup, and both
record the number of cosets that the enumeration used; those figures are part of the transcription
notes of each row. Each row is also an *efficient* presentation in the sense of its source, meaning
that its deficiency attains the lower bound coming from the Schur multiplier; that is the property
the sources are about, and it plays no role here beyond explaining why they list these words.

## What is and is not claimed

Nothing in this file asserts that the presented groups are nontrivial, finite, or simple, that they
have any particular order, or that they are isomorphic to any other construction of a Mathieu
group. Those are downstream statements which the CFSG roadmap deliberately does not ask for. What is
proved here is exactly the transcription arithmetic: the counts, the total length, the compiled
letters, and cyclic reducedness.

## Cross-checks

The correctness of a transcription is a review obligation, not something these theorems establish.
Two external checks are recorded below as provenance for a reviewer. Neither is a Lean proof, and
neither is claimed by any theorem in this file.

The first is an independent re-enumeration of the transcribed words outside Lean, with GAP 4.15.1.
Transcribing the compiled letters back into GAP's free-group syntax gives the input

```text
F := FreeGroup("a", "b");;  a := F.1;;  b := F.2;;
G11 := F / [ b*a^-3*b*a^-1*b^3, b*a*b^-1*a^-1*b^-1*a^-1*b*a*b^-1*a ];;
G12 := F / [ (b^-1*a)^3, a^5*b^6, a*b^2*a*b^-1*a^2*b*a^2*b^2 ];;
G22 := F / [ a^4*b*a^-1*b*a^-1*b, a^2*b*a^-1*b^-1*a*b^2*a^-1*b^-1, b^11 ];;
List([G11, G12, G22], Size);
List([G11, G12, G22], IsSimpleGroup);
List([[G11, 11], [G12, 12], [G22, 22]], p -> IsomorphismGroups(p[1], MathieuGroup(p[2])) <> fail);
```

on which Todd--Coxeter over the trivial subgroup returns the orders `7920`, `95040` and `443520`,
each group is simple, and an isomorphism to `MathieuGroup(11)`, `MathieuGroup(12)` and
`MathieuGroup(22)` is found. That reproduces the published claim about the words as transcribed
here, and a mistyped letter would be very unlikely to survive it.

The second is the comparison the CFSG roadmap asks a sporadic row to record, and these three rows
still owe it. The roadmap points at the Lean 4 permutation-group development
[FiniteSimpleGroups](https://github.com/KitaKen1/finite-simple-groups-lean), which builds `M₁₁`,
`M₁₂` and `M₂₂` as subgroups of `Equiv.Perm (Fin n)` with their orders and simplicity proved, and
asks whether the transcribed relators hold of its named generators. That is a review artifact rather
than a Lean target, since making it one would mean importing that development, which the roadmap
conditions on coordination with its author. It has not been carried out for these rows, and the GAP
re-enumeration above is an additional independent check rather than a substitute for it.

## Main definitions

* `TauCeti.Sporadic.m11Presentation`, `TauCeti.Sporadic.m12Presentation` and
  `TauCeti.Sporadic.m22Presentation`: the three transcribed rows.

## References

This is part of milestone S1 of `TauCetiRoadmap/CFSGStatement/README.md`, which asks for a complete
relator word list, with an admissible source, for each of the twenty-six sporadic names. It
populates the presentation data for three of those rows; the rows remain open until the required
comparisons against the FiniteSimpleGroups development are recorded. The two sources are:

* C. M. Campbell, G. Havas, C. Ramsay and E. F. Robertson, *Nice efficient presentations for all
  small simple groups and their covers*, LMS J. Comput. Math. **7** (2004), 266--283,
  <https://doi.org/10.1112/S1461157000001121>;
* M. D. E. Conder, G. Havas and C. Ramsay, *Efficient presentations for the Mathieu simple group
  `M₂₂` and its cover*, in *Finite Geometries, Groups, and Computation*, Walter de Gruyter, Berlin,
  2006, 33--41.

The Lean development named in the cross-check above is
[FiniteSimpleGroups](https://github.com/KitaKen1/finite-simple-groups-lean); nothing from it is
imported, copied, or adapted here.

The remaining two Mathieu names, `M₂₃` and `M₂₄`, are not transcribed here. The presentations on
their ATLAS version 3 pages are stated rather than proved there, and locating a source that proves
them is part of the S0 search that milestone still owes those rows.
-/

public section

namespace TauCeti.Sporadic

/-! ### The alphabet of a two-generator presentation

Both sources write relators as words in two generators `a` and `b`, with an upper-case letter
denoting an inverse, so that `A` is `a⁻¹`. The four expressions below are those four letters, and
`⬝` below is `TauCeti.Relator.mul`, so a transcribed relator reads left to right exactly as the
source prints it. -/

private abbrev genA : Relator (Fin 2) := .gen 0

private abbrev invA : Relator (Fin 2) := .inv genA

private abbrev genB : Relator (Fin 2) := .gen 1

private abbrev invB : Relator (Fin 2) := .inv genB

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-! ### `M₁₁` -/

/-- A finite presentation of the Mathieu group `M₁₁`, transcribed from row `M11` of Table 2 of
Campbell--Havas--Ramsay--Robertson.

The source's two relators are `b A³ b A b³` and `b a B A B A b a B a`. This is a two-generator,
two-relator presentation, which is efficient because `M₁₁` has trivial Schur multiplier. -/
def m11Presentation : GroupPresentation where
  generatorNames := ["a", "b"]
  source := "C. M. Campbell, G. Havas, C. Ramsay and E. F. Robertson, Nice efficient \
    presentations for all small simple groups and their covers, LMS J. Comput. Math. 7 (2004), \
    266-283"
  sourceLocator := "Table 2 (p. 269), row M11, with the discussion in Section 5.8 (p. 275); \
    doi:10.1112/S1461157000001121"
  generatorConvention := "The generators a and b of the source, in that order, so index 0 is a and \
    index 1 is b. An upper-case letter denotes the inverse of the corresponding generator, and \
    each relator is a word that the source sets equal to the identity."
  transcriptionNotes := "The relators are the source's b A^3 b A b^3 and b a B A B A b a B a, \
    transcribed letter by letter. No commutator constructor is used, so the commutator convention \
    of Relator does not enter. The source proves the presentation by coset enumeration over the \
    trivial subgroup, using a total of 10428 cosets, and records the resulting order 7920."
  expectedGeneratorCount := 2
  expectedRelatorCount := 2
  transcribed :=
    [ -- b A A A b A b b b
      genB ⬝ .pow invA 3 ⬝ genB ⬝ invA ⬝ .pow genB 3,
      -- b a B A B A b a B a
      genB ⬝ genA ⬝ invB ⬝ invA ⬝ invB ⬝ invA ⬝ genB ⬝ genA ⬝ invB ⬝ genA ]

/-- The generator names recorded for `M₁₁`. The row's body is sealed, so this is what lets a
consumer see that it is a two-generator presentation. -/
@[simp]
theorem m11Presentation_generatorNames : m11Presentation.generatorNames = ["a", "b"] := by
  simp [m11Presentation]

/-- The source recorded for `M₁₁`. The row's body is sealed, so this equation is what publishes the
citation itself, rather than only the row's name, to a downstream audit. -/
@[simp]
theorem m11Presentation_source :
    m11Presentation.source = "C. M. Campbell, G. Havas, C. Ramsay and E. F. Robertson, Nice \
      efficient presentations for all small simple groups and their covers, LMS J. Comput. Math. 7 \
      (2004), 266-283" := by
  simp [m11Presentation]

/-- The locator recorded for `M₁₁`, pointing at the presentation inside its source. -/
@[simp]
theorem m11Presentation_sourceLocator :
    m11Presentation.sourceLocator = "Table 2 (p. 269), row M11, with the discussion in Section 5.8 \
      (p. 275); doi:10.1112/S1461157000001121" := by
  simp [m11Presentation]

/-- The generator convention recorded for `M₁₁`, fixing which generator each relator index names. -/
@[simp]
theorem m11Presentation_generatorConvention :
    m11Presentation.generatorConvention = "The generators a and b of the source, in that order, so \
      index 0 is a and index 1 is b. An upper-case letter denotes the inverse of the corresponding \
      generator, and each relator is a word that the source sets equal to the identity." := by
  simp [m11Presentation]

/-- The transcription notes recorded for `M₁₁`, including the coset total of the source's
enumeration. -/
@[simp]
theorem m11Presentation_transcriptionNotes :
    m11Presentation.transcriptionNotes = "The relators are the source's b A^3 b A b^3 and b a B A \
      B A b a B a, transcribed letter by letter. No commutator constructor is used, so the \
      commutator convention of Relator does not enter. The source proves the presentation by coset \
      enumeration over the trivial subgroup, using a total of 10428 cosets, and records the \
      resulting order 7920." := by
  simp [m11Presentation]

/-- The generator count `M₁₁`'s source states. With
`TauCeti.Sporadic.m11Presentation_generatorNames` this is what makes
`TauCeti.Sporadic.m11Presentation_matchesMetadata` an equation between two visible numbers. -/
@[simp]
theorem m11Presentation_expectedGeneratorCount : m11Presentation.expectedGeneratorCount = 2 := by
  simp [m11Presentation]

/-- The relator count `M₁₁`'s source states; see
`TauCeti.Sporadic.m11Presentation_expectedGeneratorCount`. -/
@[simp]
theorem m11Presentation_expectedRelatorCount : m11Presentation.expectedRelatorCount = 2 := by
  simp [m11Presentation]

/-- The relator expressions transcribed for `M₁₁`, with their generator indices written out.

The row's body is sealed, so this is the equation that characterizes it: with
`TauCeti.GroupPresentation.relators_def` it determines the compiled words, and with
`TauCeti.GroupPresentation.mem_relatorSet_iff` it determines the relations defining
`TauCeti.GroupPresentation.Group`, so a consumer never has to unfold the row. Index `0` is the
generator `a` and index `1` is `b`, and the bounds come from
`TauCeti.Sporadic.m11Presentation_generatorNames`. -/
@[simp]
theorem m11Presentation_transcribed :
    m11Presentation.transcribed =
      [ -- b A A A b A b b b
        .gen ⟨1, by simp⟩ ⬝ .pow (.inv (.gen ⟨0, by simp⟩)) 3 ⬝ .gen ⟨1, by simp⟩ ⬝
          .inv (.gen ⟨0, by simp⟩) ⬝ .pow (.gen ⟨1, by simp⟩) 3,
        -- b a B A B A b a B a
        .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .inv (.gen ⟨1, by simp⟩) ⬝
          .inv (.gen ⟨0, by simp⟩) ⬝ .inv (.gen ⟨1, by simp⟩) ⬝ .inv (.gen ⟨0, by simp⟩) ⬝
          .gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .inv (.gen ⟨1, by simp⟩) ⬝
          .gen ⟨0, by simp⟩ ] := by
  simp [m11Presentation]

/-- The generator and relator counts recorded for `M₁₁` agree with the transcribed data. -/
theorem m11Presentation_matchesMetadata : m11Presentation.matchesMetadata := by decide

/-- The compiled relator words for `M₁₁`, spelled out. A letter `(i, true)` is the generator with
index `i` and `(i, false)` is its inverse, so the two words read `b A A A b A b b b` and
`b a B A B A b a B a`. -/
theorem m11Presentation_relatorLetters :
    m11Presentation.relatorLetters =
      [[(1, true), (0, false), (0, false), (0, false), (1, true), (0, false), (1, true),
          (1, true), (1, true)],
        [(1, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, true),
          (0, true), (1, false), (0, true)]] := by
  simp [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def,
    GroupPresentation.generatorCount, FreeGroup.invRev, m11Presentation]

/-- The compiled relator words for `M₁₁` have the total length `19` published by the source. This is
read off from the spelled-out letters rather than from the record. -/
theorem m11Presentation_totalLength : m11Presentation.totalLength = 19 := by
  rw [← GroupPresentation.sum_map_length_relatorLetters, m11Presentation_relatorLetters]
  decide

/-- Every compiled relator word for `M₁₁` is cyclically reduced. This is what makes the letter count
in `TauCeti.Sporadic.m11Presentation_totalLength` comparable with the length published for the
presentation, which is measured after free and cyclic reduction of each relator.

Only the compiler needs unfolding here: once the transcribed expressions are compiled away, the
words are closed data and the kernel decides the predicate. -/
theorem m11Presentation_relatorsCyclicallyReduced : m11Presentation.relatorsCyclicallyReduced := by
  simp only [GroupPresentation.relatorsCyclicallyReduced_iff, GroupPresentation.relators_def,
    m11Presentation, List.map_cons, List.map_nil, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_inv, Relator.toWord_gen]
  decide

/-! ### `M₁₂` -/

/-- A finite presentation of the Mathieu group `M₁₂`, transcribed from row `M12` of Table 2 of
Campbell--Havas--Ramsay--Robertson.

The source's three relators are `(B a)³`, `a⁵ b⁶` and `a b² a B a² b a² b²`. -/
def m12Presentation : GroupPresentation where
  generatorNames := ["a", "b"]
  source := "C. M. Campbell, G. Havas, C. Ramsay and E. F. Robertson, Nice efficient \
    presentations for all small simple groups and their covers, LMS J. Comput. Math. 7 (2004), \
    266-283"
  sourceLocator := "Table 2 (p. 269), row M12, with the discussion in Section 5.17 (p. 279); \
    doi:10.1112/S1461157000001121"
  generatorConvention := "The generators a and b of the source, in that order, so index 0 is a and \
    index 1 is b. An upper-case letter denotes the inverse of the corresponding generator, and \
    each relator is a word that the source sets equal to the identity."
  transcriptionNotes := "The relators are the source's (B a)^3, a^5 b^6 and a b^2 a B a^2 b a^2 \
    b^2, transcribed letter by letter; the bracketed cube is kept as a power expression rather \
    than expanded. No commutator constructor is used. The source proves the presentation by coset \
    enumeration over the trivial subgroup, using a total of 119334 cosets, and records the \
    resulting order 95040."
  expectedGeneratorCount := 2
  expectedRelatorCount := 3
  transcribed :=
    [ -- (B a)³
      .pow (invB ⬝ genA) 3,
      -- a⁵ b⁶
      .pow genA 5 ⬝ .pow genB 6,
      -- a b b a B a a b a a b b
      genA ⬝ .pow genB 2 ⬝ genA ⬝ invB ⬝ .pow genA 2 ⬝ genB ⬝ .pow genA 2 ⬝ .pow genB 2 ]

/-- The generator names recorded for `M₁₂`; see
`TauCeti.Sporadic.m11Presentation_generatorNames`. -/
@[simp]
theorem m12Presentation_generatorNames : m12Presentation.generatorNames = ["a", "b"] := by
  simp [m12Presentation]

/-- The source recorded for `M₁₂`; see `TauCeti.Sporadic.m11Presentation_source`. -/
@[simp]
theorem m12Presentation_source :
    m12Presentation.source = "C. M. Campbell, G. Havas, C. Ramsay and E. F. Robertson, Nice \
      efficient presentations for all small simple groups and their covers, LMS J. Comput. Math. 7 \
      (2004), 266-283" := by
  simp [m12Presentation]

/-- The locator recorded for `M₁₂`, pointing at the presentation inside its source. -/
@[simp]
theorem m12Presentation_sourceLocator :
    m12Presentation.sourceLocator = "Table 2 (p. 269), row M12, with the discussion in Section \
      5.17 (p. 279); doi:10.1112/S1461157000001121" := by
  simp [m12Presentation]

/-- The generator convention recorded for `M₁₂`, fixing which generator each relator index names. -/
@[simp]
theorem m12Presentation_generatorConvention :
    m12Presentation.generatorConvention = "The generators a and b of the source, in that order, so \
      index 0 is a and index 1 is b. An upper-case letter denotes the inverse of the corresponding \
      generator, and each relator is a word that the source sets equal to the identity." := by
  simp [m12Presentation]

/-- The transcription notes recorded for `M₁₂`, including the coset total of the source's
enumeration. -/
@[simp]
theorem m12Presentation_transcriptionNotes :
    m12Presentation.transcriptionNotes = "The relators are the source's (B a)^3, a^5 b^6 and a \
      b^2 a B a^2 b a^2 b^2, transcribed letter by letter; the bracketed cube is kept as a power \
      expression rather than expanded. No commutator constructor is used. The source proves the \
      presentation by coset enumeration over the trivial subgroup, using a total of 119334 cosets, \
      and records the resulting order 95040." := by
  simp [m12Presentation]

/-- The generator count `M₁₂`'s source states; see
`TauCeti.Sporadic.m11Presentation_expectedGeneratorCount`. -/
@[simp]
theorem m12Presentation_expectedGeneratorCount : m12Presentation.expectedGeneratorCount = 2 := by
  simp [m12Presentation]

/-- The relator count `M₁₂`'s source states; see
`TauCeti.Sporadic.m11Presentation_expectedGeneratorCount`. -/
@[simp]
theorem m12Presentation_expectedRelatorCount : m12Presentation.expectedRelatorCount = 3 := by
  simp [m12Presentation]

/-- The relator expressions transcribed for `M₁₂`, with their generator indices written out; see
`TauCeti.Sporadic.m11Presentation_transcribed` for what this equation is for. -/
@[simp]
theorem m12Presentation_transcribed :
    m12Presentation.transcribed =
      [ -- (B a)³
        .pow (.inv (.gen ⟨1, by simp⟩) ⬝ .gen ⟨0, by simp⟩) 3,
        -- a⁵ b⁶
        .pow (.gen ⟨0, by simp⟩) 5 ⬝ .pow (.gen ⟨1, by simp⟩) 6,
        -- a b b a B a a b a a b b
        .gen ⟨0, by simp⟩ ⬝ .pow (.gen ⟨1, by simp⟩) 2 ⬝ .gen ⟨0, by simp⟩ ⬝
          .inv (.gen ⟨1, by simp⟩) ⬝ .pow (.gen ⟨0, by simp⟩) 2 ⬝ .gen ⟨1, by simp⟩ ⬝
          .pow (.gen ⟨0, by simp⟩) 2 ⬝ .pow (.gen ⟨1, by simp⟩) 2 ] := by
  simp [m12Presentation]

/-- The generator and relator counts recorded for `M₁₂` agree with the transcribed data. -/
theorem m12Presentation_matchesMetadata : m12Presentation.matchesMetadata := by decide

/-- The compiled relator words for `M₁₂`, spelled out. A letter `(i, true)` is the generator with
index `i` and `(i, false)` is its inverse, so the three words read `B a B a B a`, then five copies
of `a` followed by six copies of `b`, and `a b b a B a a b a a b b`. -/
theorem m12Presentation_relatorLetters :
    m12Presentation.relatorLetters =
      [[(1, false), (0, true), (1, false), (0, true), (1, false), (0, true)],
        [(0, true), (0, true), (0, true), (0, true), (0, true), (1, true), (1, true), (1, true),
          (1, true), (1, true), (1, true)],
        [(0, true), (1, true), (1, true), (0, true), (1, false), (0, true), (0, true), (1, true),
          (0, true), (0, true), (1, true), (1, true)]] := by
  simp [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def,
    GroupPresentation.generatorCount, FreeGroup.invRev, m12Presentation]

/-- The compiled relator words for `M₁₂` have the total length `29` published by the source. This is
read off from the spelled-out letters rather than from the record. -/
theorem m12Presentation_totalLength : m12Presentation.totalLength = 29 := by
  rw [← GroupPresentation.sum_map_length_relatorLetters, m12Presentation_relatorLetters]
  decide

/-- Every compiled relator word for `M₁₂` is cyclically reduced; see
`TauCeti.Sporadic.m11Presentation_relatorsCyclicallyReduced`. -/
theorem m12Presentation_relatorsCyclicallyReduced : m12Presentation.relatorsCyclicallyReduced := by
  simp only [GroupPresentation.relatorsCyclicallyReduced_iff, GroupPresentation.relators_def,
    m12Presentation, List.map_cons, List.map_nil, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_inv, Relator.toWord_gen]
  decide

/-! ### `M₂₂` -/

/-- A finite presentation of the Mathieu group `M₂₂`, transcribed from Section 3.4 of
Conder--Havas--Ramsay.

The source's three relators are `a⁴ b A b A b`, `a a b A B a b b A B` and `b¹¹`. The first two of
them present the covering group of `M₂₂`, and the source obtains this presentation of `M₂₂` itself
by adjoining `b¹¹`, a central element of order twelve in that cover. -/
def m22Presentation : GroupPresentation where
  generatorNames := ["a", "b"]
  source := "M. D. E. Conder, G. Havas and C. Ramsay, Efficient presentations for the Mathieu \
    simple group M22 and its cover, in Finite Geometries, Groups, and Computation, Walter de \
    Gruyter, Berlin, 2006, 33-41"
  sourceLocator := "Section 3.4 (p. 40), the presentation obtained from the presentation P8 of \
    the cover by adjoining the central element b^11"
  generatorConvention := "The generators a and b of the source, in that order, so index 0 is a and \
    index 1 is b. An upper-case letter denotes the inverse of the corresponding generator, and \
    each relator is a word that the source sets equal to the identity."
  transcriptionNotes := "The relators are the source's a a a a b A b A b, a a b A B a b b A B and \
    b^11, transcribed letter by letter, with the two runs of equal letters kept as powers. No \
    commutator constructor is used. The source proves the presentation by coset enumeration over \
    the trivial subgroup, using a total of 2104858 cosets, and describes it as the shortest \
    presentation of M22 it found, of length 30."
  expectedGeneratorCount := 2
  expectedRelatorCount := 3
  transcribed :=
    [ -- a a a a b A b A b
      .pow genA 4 ⬝ genB ⬝ invA ⬝ genB ⬝ invA ⬝ genB,
      -- a a b A B a b b A B
      .pow genA 2 ⬝ genB ⬝ invA ⬝ invB ⬝ genA ⬝ .pow genB 2 ⬝ invA ⬝ invB,
      -- b¹¹
      .pow genB 11 ]

/-- The generator names recorded for `M₂₂`; see
`TauCeti.Sporadic.m11Presentation_generatorNames`. -/
@[simp]
theorem m22Presentation_generatorNames : m22Presentation.generatorNames = ["a", "b"] := by
  simp [m22Presentation]

/-- The source recorded for `M₂₂`; see `TauCeti.Sporadic.m11Presentation_source`. -/
@[simp]
theorem m22Presentation_source :
    m22Presentation.source = "M. D. E. Conder, G. Havas and C. Ramsay, Efficient presentations for \
      the Mathieu simple group M22 and its cover, in Finite Geometries, Groups, and Computation, \
      Walter de Gruyter, Berlin, 2006, 33-41" := by
  simp [m22Presentation]

/-- The locator recorded for `M₂₂`, pointing at the presentation inside its source. -/
@[simp]
theorem m22Presentation_sourceLocator :
    m22Presentation.sourceLocator = "Section 3.4 (p. 40), the presentation obtained from the \
      presentation P8 of the cover by adjoining the central element b^11" := by
  simp [m22Presentation]

/-- The generator convention recorded for `M₂₂`, fixing which generator each relator index names. -/
@[simp]
theorem m22Presentation_generatorConvention :
    m22Presentation.generatorConvention = "The generators a and b of the source, in that order, so \
      index 0 is a and index 1 is b. An upper-case letter denotes the inverse of the corresponding \
      generator, and each relator is a word that the source sets equal to the identity." := by
  simp [m22Presentation]

/-- The transcription notes recorded for `M₂₂`, including the coset total of the source's
enumeration. -/
@[simp]
theorem m22Presentation_transcriptionNotes :
    m22Presentation.transcriptionNotes = "The relators are the source's a a a a b A b A b, a a b A \
      B a b b A B and b^11, transcribed letter by letter, with the two runs of equal letters kept \
      as powers. No commutator constructor is used. The source proves the presentation by coset \
      enumeration over the trivial subgroup, using a total of 2104858 cosets, and describes it as \
      the shortest presentation of M22 it found, of length 30." := by
  simp [m22Presentation]

/-- The generator count `M₂₂`'s source states; see
`TauCeti.Sporadic.m11Presentation_expectedGeneratorCount`. -/
@[simp]
theorem m22Presentation_expectedGeneratorCount : m22Presentation.expectedGeneratorCount = 2 := by
  simp [m22Presentation]

/-- The relator count `M₂₂`'s source states; see
`TauCeti.Sporadic.m11Presentation_expectedGeneratorCount`. -/
@[simp]
theorem m22Presentation_expectedRelatorCount : m22Presentation.expectedRelatorCount = 3 := by
  simp [m22Presentation]

/-- The relator expressions transcribed for `M₂₂`, with their generator indices written out; see
`TauCeti.Sporadic.m11Presentation_transcribed` for what this equation is for. -/
@[simp]
theorem m22Presentation_transcribed :
    m22Presentation.transcribed =
      [ -- a a a a b A b A b
        .pow (.gen ⟨0, by simp⟩) 4 ⬝ .gen ⟨1, by simp⟩ ⬝ .inv (.gen ⟨0, by simp⟩) ⬝
          .gen ⟨1, by simp⟩ ⬝ .inv (.gen ⟨0, by simp⟩) ⬝ .gen ⟨1, by simp⟩,
        -- a a b A B a b b A B
        .pow (.gen ⟨0, by simp⟩) 2 ⬝ .gen ⟨1, by simp⟩ ⬝ .inv (.gen ⟨0, by simp⟩) ⬝
          .inv (.gen ⟨1, by simp⟩) ⬝ .gen ⟨0, by simp⟩ ⬝ .pow (.gen ⟨1, by simp⟩) 2 ⬝
          .inv (.gen ⟨0, by simp⟩) ⬝ .inv (.gen ⟨1, by simp⟩),
        -- b¹¹
        .pow (.gen ⟨1, by simp⟩) 11 ] := by
  simp [m22Presentation]

/-- The generator and relator counts recorded for `M₂₂` agree with the transcribed data. -/
theorem m22Presentation_matchesMetadata : m22Presentation.matchesMetadata := by decide

/-- The compiled relator words for `M₂₂`, spelled out. A letter `(i, true)` is the generator with
index `i` and `(i, false)` is its inverse, so the three words read `a a a a b A b A b`,
`a a b A B a b b A B` and eleven copies of `b`. -/
theorem m22Presentation_relatorLetters :
    m22Presentation.relatorLetters =
      [[(0, true), (0, true), (0, true), (0, true), (1, true), (0, false), (1, true), (0, false),
          (1, true)],
        [(0, true), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (1, true),
          (0, false), (1, false)],
        [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true), (1, true),
          (1, true), (1, true), (1, true)]] := by
  simp [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def,
    GroupPresentation.generatorCount, FreeGroup.invRev, m22Presentation]

/-- The compiled relator words for `M₂₂` have the total length `30` published by the source. This is
read off from the spelled-out letters rather than from the record. -/
theorem m22Presentation_totalLength : m22Presentation.totalLength = 30 := by
  rw [← GroupPresentation.sum_map_length_relatorLetters, m22Presentation_relatorLetters]
  decide

/-- Every compiled relator word for `M₂₂` is cyclically reduced; see
`TauCeti.Sporadic.m11Presentation_relatorsCyclicallyReduced`. -/
theorem m22Presentation_relatorsCyclicallyReduced : m22Presentation.relatorsCyclicallyReduced := by
  simp only [GroupPresentation.relatorsCyclicallyReduced_iff, GroupPresentation.relators_def,
    m22Presentation, List.map_cons, List.map_nil, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_inv, Relator.toWord_gen]
  decide

end TauCeti.Sporadic
