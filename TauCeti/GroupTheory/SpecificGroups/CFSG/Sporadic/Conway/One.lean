/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# A transcribed presentation of the first Conway group

This file carries the `Co₁` row of the sporadic presentation data required by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. It records presentation `GPLTable.Co1.1` from Roderik
Lindenbergh's Group Presentations Library as a `TauCeti.GroupPresentation`, together with the exact
source, generator convention, transcription notes, expected counts, and decidable checks on the
transcription.

The presentation uses the Coxeter graph encoded by

```text
b4h3a3b5c3d3f4c3e4a, b4g4f, e6f6h.
```

All eight generators are involutions and every omitted edge has label two. Thus the graph
contributes eight square relations, thirteen labeled-edge relations, and fifteen omitted-edge
relations. The source then appends

```text
a = (cf)²,  e = (bg)²,  b = (ef)³,  d = (bh)²,  d = (eah)³,
(adfh)³,  (baefg)³,  (cef)⁷,  (adefcefgh)³⁹.
```

An equality `x = y` in the source is the relator `x⁻¹y`. The complete presentation therefore has
45 relators, whose compiled words have 611 signed letters. The theorems below check both figures
from the transcribed expressions.

The library identifies this record as a presentation of `Co₁` originating in Praeger--Soicher,
whose construction uses low-rank representations and graphs for sporadic groups. The stored data
is a full presentation of the abstract group, not a semi-presentation for recognizing generators
in an already constructed group. This file asserts no order, finiteness, simplicity, or
identification result.

## Independent source-to-Lean read-through

An independent read-through used the bytes of `gpl.g` whose SHA-256 digest is
`8b90a7a65317a585b5b74d015083bd2fa3db8a969c117a220d00d7e8773103c8`. The exact source record is

```text
presdef := [ "b4h3a3b5c3d3f4c3e4a,b4g4f,e6f6h", ,
    "a=(cf)^2,e=(bg)^2,b=(ef)^3,d=(bh)^2,d=(eah)^3,\
     (adfh)^3,(baefg)^3,(cef)^7,(adefcefgh)^(39)",,  ],
```

`GetGenerators` gives the decoder's first-occurrence order `b,h,a,c,d,f,e,g`; the Lean row instead
uses the alphabetical order `a,b,c,d,e,f,g,h`. After that explicit renaming, `DeCoxList` and its
calls to `AddTrivialRelations` and `AddNonEdgeRelations` give the same relation multiset recorded by
`co1Presentation_relatorLetters`, regrouped by kind. Entries 1--8 are the eight generator squares;
entries 9--21 are

```text
(ab)^3,(ae)^4,(ah)^3,(bc)^5,(bg)^4,(bh)^4,(cd)^3,
(ce)^3,(cf)^4,(df)^3,(ef)^6,(fg)^4,(fh)^6;
```

and entries 22--36 are the exponent-two nonedges

```text
ac,ad,af,ag, bd,be,bf, cg,ch, de,dg,dh, eg,eh, gh.
```

`MakeWordList` compiles an equality `x = y` as `x⁻¹y`. Entries 37--45 are therefore, in source
order, `a⁻¹(cf)²`, `e⁻¹(bg)²`, `b⁻¹(ef)³`, `d⁻¹(bh)²`, `d⁻¹(eah)³`, `(adfh)³`, `(baefg)³`,
`(cef)⁷`, and `(adefcefgh)³⁹`. There is no change to any word or exponent and no dropped or
duplicated relation, only the presentation-irrelevant renaming and regrouping just described. This
closes the row's S1 source-to-Lean read-through.

The independent `FiniteSimpleGroups` comparison does not apply: at commit
`7f09e33a9ceef6b59ce03e34cd4f0558c763e325`, that development has sporadic constructions for
`Co₂` and `Co₃` but not `Co₁`.

The row is a sealed definition, so it publishes an equation for each of its fields: the transcribed
relator expressions with their generator indices written out and this file's three private relator
lists concatenated, and the provenance a manifest row exists to record. Together with
`TauCeti.GroupPresentation.relators_def` and `TauCeti.GroupPresentation.mem_relatorSet_iff` the
first of those determines the compiled words and the relations defining the presented group, so a
consumer reasons about the row without unfolding it.

These field equations and the decidable checks beside them follow the shape that the
`TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko` modules established for a manifest row.

## Main definitions and results

* `TauCeti.Sporadic.co1Presentation`: the GPL finite presentation of the first Conway group `Co₁`.
* `TauCeti.Sporadic.co1Presentation_transcribed` and the equations for the remaining fields: the
  characterization of the sealed row.
* `TauCeti.Sporadic.co1Presentation_relatorLetters`: the forty-five compiled words checked against
  the decoder output in the independent source-to-Lean read-through.
* `TauCeti.Sporadic.co1Presentation_map_length_relators`,
  `TauCeti.Sporadic.co1Presentation_totalLength` and
  `TauCeti.Sporadic.co1Presentation_relatorsCyclicallyReduced`: the three checks on the compiled
  words.

## References

* R. Lindenbergh, *Group Presentations Library*, version 1.0, record `GPLTable.Co1.1`,
  <https://doris.tudelft.nl/~rlindenbergh/GPL/gpl.g>.
* C. E. Praeger and L. H. Soicher, *Low Rank Representations and Graphs for Sporadic Groups*,
  Cambridge University Press, 1997, Chapter 4, doi:10.1017/CBO9780511526039.005.
* KitaKen1, `finite-simple-groups-lean`, commit
  `7f09e33a9ceef6b59ce03e34cd4f0558c763e325`,
  <https://github.com/KitaKen1/finite-simple-groups-lean/tree/7f09e33a9ceef6b59ce03e34cd4f0558c763e325/FiniteSimpleGroups/Sporadic>.
-/

public section

namespace TauCeti.Sporadic

private abbrev a : Relator (Fin 8) := .gen 0

private abbrev b : Relator (Fin 8) := .gen 1

private abbrev c : Relator (Fin 8) := .gen 2

private abbrev d : Relator (Fin 8) := .gen 3

private abbrev e : Relator (Fin 8) := .gen 4

private abbrev f : Relator (Fin 8) := .gen 5

private abbrev g : Relator (Fin 8) := .gen 6

private abbrev h : Relator (Fin 8) := .gen 7

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-- The eight involution relations and thirteen labeled-edge relations decoded from the three
Coxeter paths of `GPLTable.Co1.1`. -/
private def co1NodeAndEdgeRelators : List (Relator (Fin 8)) :=
  [ .pow a 2,
    .pow b 2,
    .pow c 2,
    .pow d 2,
    .pow e 2,
    .pow f 2,
    .pow g 2,
    .pow h 2,
    .pow (a ⬝ b) 3,
    .pow (a ⬝ e) 4,
    .pow (a ⬝ h) 3,
    .pow (b ⬝ c) 5,
    .pow (b ⬝ g) 4,
    .pow (b ⬝ h) 4,
    .pow (c ⬝ d) 3,
    .pow (c ⬝ e) 3,
    .pow (c ⬝ f) 4,
    .pow (d ⬝ f) 3,
    .pow (e ⬝ f) 6,
    .pow (f ⬝ g) 4,
    .pow (f ⬝ h) 6 ]

/-- The fifteen omitted-edge relations decoded from the three Coxeter paths of
`GPLTable.Co1.1`. Each omitted edge has label two. -/
private def co1NonedgeRelators : List (Relator (Fin 8)) :=
  [ .pow (a ⬝ c) 2,
    .pow (a ⬝ d) 2,
    .pow (a ⬝ f) 2,
    .pow (a ⬝ g) 2,
    .pow (b ⬝ d) 2,
    .pow (b ⬝ e) 2,
    .pow (b ⬝ f) 2,
    .pow (c ⬝ g) 2,
    .pow (c ⬝ h) 2,
    .pow (d ⬝ e) 2,
    .pow (d ⬝ g) 2,
    .pow (d ⬝ h) 2,
    .pow (e ⬝ g) 2,
    .pow (e ⬝ h) 2,
    .pow (g ⬝ h) 2 ]

/-- The nine words following the Coxeter paths in `GPLTable.Co1.1`. An equality `x = y` is stored
as the relator `x⁻¹y`, following the GPL decoder. -/
private def co1AdditionalRelators : List (Relator (Fin 8)) :=
  [ .inv a ⬝ .pow (c ⬝ f) 2,
    .inv e ⬝ .pow (b ⬝ g) 2,
    .inv b ⬝ .pow (e ⬝ f) 3,
    .inv d ⬝ .pow (b ⬝ h) 2,
    .inv d ⬝ .pow (e ⬝ a ⬝ h) 3,
    .pow (a ⬝ d ⬝ f ⬝ h) 3,
    .pow (b ⬝ a ⬝ e ⬝ f ⬝ g) 3,
    .pow (c ⬝ e ⬝ f) 7,
    .pow (a ⬝ d ⬝ e ⬝ f ⬝ c ⬝ e ⬝ f ⬝ g ⬝ h) 39 ]

/-- The Group Presentations Library finite presentation `GPLTable.Co1.1` of the first Conway
group `Co₁` on generators `a`, `b`, `c`, `d`, `e`, `f`, `g`, and `h`.

The source describes this as a full presentation of the abstract group and identifies its origin
as Praeger--Soicher. No structural property of the presented group is asserted here: this
definition records only the cited generators and relations. -/
def co1Presentation : GroupPresentation where
  generatorNames := ["a", "b", "c", "d", "e", "f", "g", "h"]
  source := "R. Lindenbergh, Group Presentations Library, version 1.0; presentation attributed \
    there to C. E. Praeger and L. H. Soicher, Low Rank Representations and Graphs for Sporadic \
    Groups, Cambridge University Press, 1997"
  sourceLocator := "GPLTable.Co1.1 in \
    https://doris.tudelft.nl/~rlindenbergh/GPL/gpl.g; Praeger--Soicher, Chapter 4, \
    doi:10.1017/CBO9780511526039.005"
  generatorConvention := "The source generators are indexed alphabetically in Lean: indices 0 \
    through 7 are a,b,c,d,e,f,g,h. This is a relabeling of the GPL decoder's first-occurrence map \
    b,h,a,c,d,f,e,g and preserves every named relation. A Coxeter path declares each node to be \
    an involution, a labeled edge x-m-y declares (x*y)^m = 1, and an omitted edge declares \
    (x*y)^2 = 1. An equality x = y compiles to x^-1*y, and products are read left to right."
  transcriptionNotes := "Expand the paths b4h3a3b5c3d3f4c3e4a, b4g4f, and e6f6h to eight square \
    relations, thirteen labeled-edge relations, and fifteen omitted-edge relations. Append the \
    nine words in presdef[3], interpreting each equality as left-hand inverse times right-hand \
    side, and reindex the named generators alphabetically. The expected relator count and total \
    length are derived from this exact expansion. The module documentation records the completed \
    itemized source-to-Lean read-through. FiniteSimpleGroups does not cover Co1, so its separate \
    permutation-group comparison does not apply."
  expectedGeneratorCount := 8
  expectedRelatorCount := 45
  transcribed := co1NodeAndEdgeRelators ++ co1NonedgeRelators ++ co1AdditionalRelators

/-- The generator names recorded for `Co₁`. The row's body is sealed, so this is what lets a
consumer see that it is an eight-generator presentation. -/
@[simp]
theorem co1Presentation_generatorNames :
    co1Presentation.generatorNames = ["a", "b", "c", "d", "e", "f", "g", "h"] := by
  simp [co1Presentation]

/-- The source recorded for `Co₁`. The row's body is sealed, so this equation is what publishes the
citation itself, rather than only the row's name, to a downstream audit. -/
@[simp]
theorem co1Presentation_source :
    co1Presentation.source = "R. Lindenbergh, Group Presentations Library, version 1.0; \
      presentation attributed there to C. E. Praeger and L. H. Soicher, Low Rank Representations \
      and Graphs for Sporadic Groups, Cambridge University Press, 1997" := by
  simp [co1Presentation]

/-- The locator recorded for `Co₁`, pointing at the presentation inside its source. -/
@[simp]
theorem co1Presentation_sourceLocator :
    co1Presentation.sourceLocator = "GPLTable.Co1.1 in \
      https://doris.tudelft.nl/~rlindenbergh/GPL/gpl.g; Praeger--Soicher, Chapter 4, \
      doi:10.1017/CBO9780511526039.005" := by
  simp [co1Presentation]

/-- The generator convention recorded for `Co₁`, fixing which involution each relator index names
and how a Coxeter path decodes to relations. -/
@[simp]
theorem co1Presentation_generatorConvention :
    co1Presentation.generatorConvention = "The source generators are indexed alphabetically in \
      Lean: indices 0 through 7 are a,b,c,d,e,f,g,h. This is a relabeling of the GPL decoder's \
      first-occurrence map b,h,a,c,d,f,e,g and preserves every named relation. A Coxeter path \
      declares each node to be an involution, a labeled edge x-m-y declares (x*y)^m = 1, and an \
      omitted edge declares (x*y)^2 = 1. An equality x = y compiles to x^-1*y, and products are \
      read left to right." := by
  simp [co1Presentation]

/-- The transcription notes recorded for `Co₁`. -/
@[simp]
theorem co1Presentation_transcriptionNotes :
    co1Presentation.transcriptionNotes = "Expand the paths b4h3a3b5c3d3f4c3e4a, b4g4f, and e6f6h \
      to eight square relations, thirteen labeled-edge relations, and fifteen omitted-edge \
      relations. Append the nine words in presdef[3], interpreting each equality as left-hand \
      inverse times right-hand side, and reindex the named generators alphabetically. The \
      expected relator count and total length are derived from this exact expansion. The module \
      documentation records the completed itemized source-to-Lean read-through. \
      FiniteSimpleGroups does not cover Co1, so its separate permutation-group comparison does \
      not apply." := by
  simp [co1Presentation]

/-- The generator count `Co₁`'s source states. With
`TauCeti.Sporadic.co1Presentation_generatorNames` this is what makes
`TauCeti.Sporadic.co1Presentation_matchesMetadata` an equation between two visible numbers. -/
@[simp]
theorem co1Presentation_expectedGeneratorCount : co1Presentation.expectedGeneratorCount = 8 := by
  simp [co1Presentation]

/-- The relator count `Co₁`'s source states; see
`TauCeti.Sporadic.co1Presentation_expectedGeneratorCount`. -/
@[simp]
theorem co1Presentation_expectedRelatorCount : co1Presentation.expectedRelatorCount = 45 := by
  simp [co1Presentation]

/-- The relator expressions transcribed for `Co₁`, with their generator indices written out and the
three private relator lists of this file concatenated.

The row's body is sealed, so this is the equation that characterizes it: with
`TauCeti.GroupPresentation.relators_def` it determines the compiled words, and with
`TauCeti.GroupPresentation.mem_relatorSet_iff` it determines the relations defining
`TauCeti.GroupPresentation.Group`, so a consumer never has to unfold the row. Indices `0` through
`7` are the involutions `a` through `h`, and the bounds come from
`TauCeti.Sporadic.co1Presentation_generatorNames`. -/
@[simp]
theorem co1Presentation_transcribed :
    co1Presentation.transcribed =
      [ -- a², b², c², d², e², f², g², h²
        .pow (.gen ⟨0, by simp⟩) 2,
        .pow (.gen ⟨1, by simp⟩) 2,
        .pow (.gen ⟨2, by simp⟩) 2,
        .pow (.gen ⟨3, by simp⟩) 2,
        .pow (.gen ⟨4, by simp⟩) 2,
        .pow (.gen ⟨5, by simp⟩) 2,
        .pow (.gen ⟨6, by simp⟩) 2,
        .pow (.gen ⟨7, by simp⟩) 2,
        -- the thirteen labeled edges
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨1, by simp⟩) 3,
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨4, by simp⟩) 4,
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨7, by simp⟩) 3,
        .pow (.gen ⟨1, by simp⟩ ⬝ .gen ⟨2, by simp⟩) 5,
        .pow (.gen ⟨1, by simp⟩ ⬝ .gen ⟨6, by simp⟩) 4,
        .pow (.gen ⟨1, by simp⟩ ⬝ .gen ⟨7, by simp⟩) 4,
        .pow (.gen ⟨2, by simp⟩ ⬝ .gen ⟨3, by simp⟩) 3,
        .pow (.gen ⟨2, by simp⟩ ⬝ .gen ⟨4, by simp⟩) 3,
        .pow (.gen ⟨2, by simp⟩ ⬝ .gen ⟨5, by simp⟩) 4,
        .pow (.gen ⟨3, by simp⟩ ⬝ .gen ⟨5, by simp⟩) 3,
        .pow (.gen ⟨4, by simp⟩ ⬝ .gen ⟨5, by simp⟩) 6,
        .pow (.gen ⟨5, by simp⟩ ⬝ .gen ⟨6, by simp⟩) 4,
        .pow (.gen ⟨5, by simp⟩ ⬝ .gen ⟨7, by simp⟩) 6,
        -- the fifteen omitted edges
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨2, by simp⟩) 2,
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨3, by simp⟩) 2,
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨5, by simp⟩) 2,
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨6, by simp⟩) 2,
        .pow (.gen ⟨1, by simp⟩ ⬝ .gen ⟨3, by simp⟩) 2,
        .pow (.gen ⟨1, by simp⟩ ⬝ .gen ⟨4, by simp⟩) 2,
        .pow (.gen ⟨1, by simp⟩ ⬝ .gen ⟨5, by simp⟩) 2,
        .pow (.gen ⟨2, by simp⟩ ⬝ .gen ⟨6, by simp⟩) 2,
        .pow (.gen ⟨2, by simp⟩ ⬝ .gen ⟨7, by simp⟩) 2,
        .pow (.gen ⟨3, by simp⟩ ⬝ .gen ⟨4, by simp⟩) 2,
        .pow (.gen ⟨3, by simp⟩ ⬝ .gen ⟨6, by simp⟩) 2,
        .pow (.gen ⟨3, by simp⟩ ⬝ .gen ⟨7, by simp⟩) 2,
        .pow (.gen ⟨4, by simp⟩ ⬝ .gen ⟨6, by simp⟩) 2,
        .pow (.gen ⟨4, by simp⟩ ⬝ .gen ⟨7, by simp⟩) 2,
        .pow (.gen ⟨6, by simp⟩ ⬝ .gen ⟨7, by simp⟩) 2,
        -- the nine words following the Coxeter paths
        .inv (.gen ⟨0, by simp⟩) ⬝ .pow (.gen ⟨2, by simp⟩ ⬝ .gen ⟨5, by simp⟩) 2,
        .inv (.gen ⟨4, by simp⟩) ⬝ .pow (.gen ⟨1, by simp⟩ ⬝ .gen ⟨6, by simp⟩) 2,
        .inv (.gen ⟨1, by simp⟩) ⬝ .pow (.gen ⟨4, by simp⟩ ⬝ .gen ⟨5, by simp⟩) 3,
        .inv (.gen ⟨3, by simp⟩) ⬝ .pow (.gen ⟨1, by simp⟩ ⬝ .gen ⟨7, by simp⟩) 2,
        .inv (.gen ⟨3, by simp⟩) ⬝
          .pow (.gen ⟨4, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨7, by simp⟩) 3,
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨3, by simp⟩ ⬝ .gen ⟨5, by simp⟩ ⬝ .gen ⟨7, by simp⟩) 3,
        .pow (.gen ⟨1, by simp⟩ ⬝ .gen ⟨0, by simp⟩ ⬝ .gen ⟨4, by simp⟩ ⬝ .gen ⟨5, by simp⟩ ⬝
          .gen ⟨6, by simp⟩) 3,
        .pow (.gen ⟨2, by simp⟩ ⬝ .gen ⟨4, by simp⟩ ⬝ .gen ⟨5, by simp⟩) 7,
        .pow (.gen ⟨0, by simp⟩ ⬝ .gen ⟨3, by simp⟩ ⬝ .gen ⟨4, by simp⟩ ⬝ .gen ⟨5, by simp⟩ ⬝
          .gen ⟨2, by simp⟩ ⬝ .gen ⟨4, by simp⟩ ⬝ .gen ⟨5, by simp⟩ ⬝ .gen ⟨6, by simp⟩ ⬝
          .gen ⟨7, by simp⟩) 39 ] := by
  simp [co1Presentation, co1NodeAndEdgeRelators, co1NonedgeRelators, co1AdditionalRelators]

/-- The compiled relator words of `Co₁`, generated from the nodes, edges, nonedges, and nine
additional words of `GPLTable.Co1.1`. A letter `(i, true)` is generator `i`, while `(i, false)` is
its inverse. -/
theorem co1Presentation_relatorLetters :
    co1Presentation.relatorLetters =
      let powWord (w : List (Nat × Bool)) (n : ℕ) := (List.replicate n w).flatten
      let squareWords := (List.range 8).map fun k => powWord [(k, true)] 2
      let edgeSpecs : List (Nat × Nat × Nat) :=
        [(0, 1, 3), (0, 4, 4), (0, 7, 3), (1, 2, 5), (1, 6, 4), (1, 7, 4),
          (2, 3, 3), (2, 4, 3), (2, 5, 4), (3, 5, 3), (4, 5, 6), (5, 6, 4), (5, 7, 6)]
      let edgeWords := edgeSpecs.map fun (r, s, n) => powWord [(r, true), (s, true)] n
      let nonedgePairs : List (Nat × Nat) :=
        [(0, 2), (0, 3), (0, 5), (0, 6), (1, 3), (1, 4), (1, 5), (2, 6),
          (2, 7), (3, 4), (3, 6), (3, 7), (4, 6), (4, 7), (6, 7)]
      let nonedgeWords := nonedgePairs.map fun (r, s) => powWord [(r, true), (s, true)] 2
      squareWords ++ edgeWords ++ nonedgeWords ++
        [[(0, false)] ++ powWord [(2, true), (5, true)] 2,
          [(4, false)] ++ powWord [(1, true), (6, true)] 2,
          [(1, false)] ++ powWord [(4, true), (5, true)] 3,
          [(3, false)] ++ powWord [(1, true), (7, true)] 2,
          [(3, false)] ++ powWord [(4, true), (0, true), (7, true)] 3,
          powWord [(0, true), (3, true), (5, true), (7, true)] 3,
          powWord [(1, true), (0, true), (4, true), (5, true), (6, true)] 3,
          powWord [(2, true), (4, true), (5, true)] 7,
          powWord [(0, true), (3, true), (4, true), (5, true), (2, true), (4, true),
            (5, true), (6, true), (7, true)] 39] := by
  simp only [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def,
    co1Presentation_transcribed, List.map_cons, List.map_nil, Relator.toWord_mul,
    Relator.toWord_pow, Relator.toWord_gen, Relator.toWord_inv, FreeGroup.invRev,
    List.map_flatten, List.map_replicate, List.reverse_cons, List.reverse_nil, Bool.not_true,
    List.cons_append, List.nil_append, List.range_succ, List.range_zero]

/-- The generator and relator counts recorded for `Co₁` agree with the transcribed data. -/
theorem co1Presentation_matchesMetadata : co1Presentation.matchesMetadata := by
  decide

/-- The lengths of the forty-five compiled relator words for `Co₁`, in the order in which the three
Coxeter paths and the nine trailing words are decoded.

Reading the counts off one relator at a time is what lets a reviewer locate a discrepancy, rather
than only observe one in the total of `TauCeti.Sporadic.co1Presentation_totalLength`, which sums
exactly this list. The lengths are computed through `TauCeti.Relator.length_toWord`, which
multiplies rather than repeats, so the thirty-ninth power at the end never has to be expanded. -/
theorem co1Presentation_map_length_relators :
    co1Presentation.relators.map List.length =
      [2, 2, 2, 2, 2, 2, 2, 2,
       6, 8, 6, 10, 8, 8, 6, 6, 8, 6, 12, 8, 12,
       4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
       5, 5, 7, 5, 10, 12, 15, 21, 351] := by
  simp only [GroupPresentation.relators_def, co1Presentation, co1NodeAndEdgeRelators,
    co1NonedgeRelators, co1AdditionalRelators, List.map_cons, List.map_nil,
    Relator.length_toWord, Relator.length_gen, Relator.length_inv, Relator.length_mul,
    Relator.length_pow, List.cons_append, List.nil_append]

/-- The compiled relators of the `Co₁` presentation contain `611` signed letters in total: the sum
of the per-relator lengths of `TauCeti.Sporadic.co1Presentation_map_length_relators`. -/
theorem co1Presentation_totalLength : co1Presentation.totalLength = 611 := by
  rw [GroupPresentation.totalLength_def, co1Presentation_map_length_relators]
  decide

/-- The involution and labeled-edge relators compile to cyclically reduced words. -/
private theorem isCyclicallyReduced_toWord_of_mem_co1NodeAndEdgeRelators :
    ∀ r ∈ co1NodeAndEdgeRelators, FreeGroup.IsCyclicallyReduced (Relator.toWord r) := by
  simp [co1NodeAndEdgeRelators, FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced]

/-- The omitted-edge relators compile to cyclically reduced words. -/
private theorem isCyclicallyReduced_toWord_of_mem_co1NonedgeRelators :
    ∀ r ∈ co1NonedgeRelators, FreeGroup.IsCyclicallyReduced (Relator.toWord r) := by
  simp [co1NonedgeRelators, FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced]

/-- The relators taken from `presdef[3]` compile to cyclically reduced words.

Each alternative is dispatched by the shape of its relator, not by goal position: a relator that
is a power is checked on its base through `TauCeti.Relator.isCyclicallyReduced_toWord_pow`, and
every other relator is checked by direct computation, so inserting, removing, or reordering
relators cannot redirect a branch. The power route is also what makes the last relator tractable
at all: it is a thirty-ninth power whose expansion has three hundred and fifty-one of the
presentation's letters, and expanding it exhausts the elaborator. -/
private theorem isCyclicallyReduced_toWord_of_mem_co1AdditionalRelators :
    ∀ r ∈ co1AdditionalRelators, FreeGroup.IsCyclicallyReduced (Relator.toWord r) := by
  intro r hr
  simp only [co1AdditionalRelators, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  first
  | exact Relator.isCyclicallyReduced_toWord_pow
      (by simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced]) _
  | simp [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced, FreeGroup.invRev]

/-- Every transcribed `Co₁` relator expression compiles to a cyclically reduced word. -/
private theorem isCyclicallyReduced_toWord_of_mem_co1Transcribed :
    ∀ r ∈ co1Presentation.transcribed, FreeGroup.IsCyclicallyReduced (Relator.toWord r) := by
  intro r hr
  rcases List.mem_append.mp hr with h | h
  · rcases List.mem_append.mp h with h | h
    · exact isCyclicallyReduced_toWord_of_mem_co1NodeAndEdgeRelators r h
    · exact isCyclicallyReduced_toWord_of_mem_co1NonedgeRelators r h
  · exact isCyclicallyReduced_toWord_of_mem_co1AdditionalRelators r h

/-- Every compiled `Co₁` relator is cyclically reduced, hence by
`FreeGroup.IsCyclicallyReduced.isReduced` freely reduced, so the letter count recorded by
`TauCeti.Sporadic.co1Presentation_totalLength` is comparable with a published presentation length,
which is normally measured on freely reduced relators. -/
theorem co1Presentation_relatorsCyclicallyReduced :
    co1Presentation.relatorsCyclicallyReduced := by
  rw [GroupPresentation.relatorsCyclicallyReduced_iff, GroupPresentation.relators_def]
  intro w hw
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
  exact isCyclicallyReduced_toWord_of_mem_co1Transcribed r hr

end TauCeti.Sporadic
