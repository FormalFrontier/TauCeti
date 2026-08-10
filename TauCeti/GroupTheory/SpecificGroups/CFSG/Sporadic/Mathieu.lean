/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Transcribed presentations of the Mathieu groups `M₁₁`, `M₁₂` and `M₂₂`

This file carries three rows of the sporadic presentation manifest: cited finite presentations of
the Mathieu groups `M₁₁`, `M₁₂` and `M₂₂`, transcribed from published sources in which each
presentation is *proved* to define the named group. Each row is a `TauCeti.GroupPresentation`, so it
records the generator names, the source and a locator inside it, the generator convention, the
transcription notes, and the generator and relator counts stated by the source, together with the
relator expressions themselves.

Four decidable checks accompany every row. The first is the generator and relator counts. The second
is the total number of letters in the compiled relator words, against the length published by the
source. The third spells the compiled words out letter by letter, so that a reviewer comparing the
Lean data with the source never has to unfold the relator compiler. The fourth is that every
compiled word is cyclically reduced, which is what makes the letter count comparable with a
published length: both sources measure length after free and cyclic reduction of each relator.

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

The correctness of a transcription is a review obligation, not something these theorems establish.
As an independent check on the relator words, and as the cross-check the roadmap asks a sporadic row
to record, each of the three presentations below was re-enumerated outside Lean with GAP 4.15.1:
Todd--Coxeter over the trivial subgroup returns a group of order `7920`, `95040` and `443520`
respectively, and in each case the resulting group is simple and isomorphic to GAP's
`MathieuGroup(11)`, `MathieuGroup(12)` and `MathieuGroup(22)`. That reproduces the published claim
about the transcribed words, and a mistyped letter would be very unlikely to survive it. It is
recorded here as provenance for a reviewer; no part of it is a Lean proof.

## Main definitions

* `TauCeti.Sporadic.m11Presentation`, `TauCeti.Sporadic.m12Presentation` and
  `TauCeti.Sporadic.m22Presentation`: the three transcribed rows.
* `TauCeti.Sporadic.genA`, `TauCeti.Sporadic.invA`, `TauCeti.Sporadic.genB`,
  `TauCeti.Sporadic.invB`: the two-letter alphabet the sources use, as relator expressions.

## References

This is part of milestone S1 of `TauCetiRoadmap/CFSGStatement/README.md`, which asks for a complete
relator word list, with an admissible source, for each of the twenty-six sporadic names. It fills
three of those rows. The two sources are:

* C. M. Campbell, G. Havas, C. Ramsay and E. F. Robertson, *Nice efficient presentations for all
  small simple groups and their covers*, LMS J. Comput. Math. **7** (2004), 266--283,
  <https://doi.org/10.1112/S1461157000001121>;
* M. D. E. Conder, G. Havas and C. Ramsay, *Efficient presentations for the Mathieu simple group
  `M₂₂` and its cover*, in *Finite Geometries, Groups, and Computation*, Walter de Gruyter, Berlin,
  2006, 33--41.

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

/-- The first generator of a two-generator presentation, printed `a` by the sources. -/
abbrev genA : Relator (Fin 2) := .gen 0

/-- The inverse of the first generator, printed `A` by the sources. -/
abbrev invA : Relator (Fin 2) := .inv genA

/-- The second generator of a two-generator presentation, printed `b` by the sources. -/
abbrev genB : Relator (Fin 2) := .gen 1

/-- The inverse of the second generator, printed `B` by the sources. -/
abbrev invB : Relator (Fin 2) := .inv genB

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

/-- The generator and relator counts recorded for `M₁₁` agree with the transcribed data. -/
theorem m11Presentation_matchesMetadata : m11Presentation.matchesMetadata := by decide

/-- The compiled relator words for `M₁₁` have the total length `19` published by the source. -/
theorem m11Presentation_totalLength : m11Presentation.totalLength = 19 := by decide

/-- The compiled relator words for `M₁₁`, spelled out. A letter `(i, true)` is the generator with
index `i` and `(i, false)` is its inverse, so the two words read `b A A A b A b b b` and
`b a B A B A b a B a`. -/
theorem m11Presentation_relatorLetters :
    m11Presentation.relatorLetters =
      [[(1, true), (0, false), (0, false), (0, false), (1, true), (0, false), (1, true),
          (1, true), (1, true)],
        [(1, true), (0, true), (1, false), (0, false), (1, false), (0, false), (1, true),
          (0, true), (1, false), (0, true)]] := by
  decide

/-- Every compiled relator word for `M₁₁` is cyclically reduced. This is what makes the letter count
in `TauCeti.Sporadic.m11Presentation_totalLength` comparable with the length published for the
presentation, which is measured after free and cyclic reduction of each relator. -/
theorem m11Presentation_isCyclicallyReduced :
    ∀ w ∈ m11Presentation.relators, FreeGroup.IsCyclicallyReduced w := by
  have hreduce : ∀ w ∈ m11Presentation.relators, FreeGroup.reduce w = w := by decide
  have hcyclic : ∀ w ∈ m11Presentation.relators, ∀ a ∈ w.getLast?, ∀ c ∈ w.head?,
      a.1 = c.1 → a.2 = c.2 := by decide
  exact fun w hw => ⟨.of_reduce_eq (hreduce w hw), hcyclic w hw⟩

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

/-- The generator and relator counts recorded for `M₁₂` agree with the transcribed data. -/
theorem m12Presentation_matchesMetadata : m12Presentation.matchesMetadata := by decide

/-- The compiled relator words for `M₁₂` have the total length `29` published by the source. -/
theorem m12Presentation_totalLength : m12Presentation.totalLength = 29 := by decide

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
  decide

/-- Every compiled relator word for `M₁₂` is cyclically reduced; see
`TauCeti.Sporadic.m11Presentation_isCyclicallyReduced`. -/
theorem m12Presentation_isCyclicallyReduced :
    ∀ w ∈ m12Presentation.relators, FreeGroup.IsCyclicallyReduced w := by
  have hreduce : ∀ w ∈ m12Presentation.relators, FreeGroup.reduce w = w := by decide
  have hcyclic : ∀ w ∈ m12Presentation.relators, ∀ a ∈ w.getLast?, ∀ c ∈ w.head?,
      a.1 = c.1 → a.2 = c.2 := by decide
  exact fun w hw => ⟨.of_reduce_eq (hreduce w hw), hcyclic w hw⟩

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

/-- The generator and relator counts recorded for `M₂₂` agree with the transcribed data. -/
theorem m22Presentation_matchesMetadata : m22Presentation.matchesMetadata := by decide

/-- The compiled relator words for `M₂₂` have the total length `30` published by the source. -/
theorem m22Presentation_totalLength : m22Presentation.totalLength = 30 := by decide

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
  decide

/-- Every compiled relator word for `M₂₂` is cyclically reduced; see
`TauCeti.Sporadic.m11Presentation_isCyclicallyReduced`. -/
theorem m22Presentation_isCyclicallyReduced :
    ∀ w ∈ m22Presentation.relators, FreeGroup.IsCyclicallyReduced w := by
  have hreduce : ∀ w ∈ m22Presentation.relators, FreeGroup.reduce w = w := by decide
  have hcyclic : ∀ w ∈ m22Presentation.relators, ∀ a ∈ w.getLast?, ∀ c ∈ w.head?,
      a.1 = c.1 → a.2 = c.2 := by decide
  exact fun w hw => ⟨.of_reduce_eq (hreduce w hw), hcyclic w hw⟩

end TauCeti.Sporadic
