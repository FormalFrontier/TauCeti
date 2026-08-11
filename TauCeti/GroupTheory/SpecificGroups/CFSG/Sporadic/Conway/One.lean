/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# A transcribed presentation of the first Conway group

This file carries the `Co₁` row of the sporadic presentation data required by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. It records the Coxeter-type presentation of the first
Conway group `Co₁` on eight involutory generators `a, …, h` published as record `GPLTable.Co1.1` of
Lindenbergh's Group Presentations Library, whose presentations are those of Praeger and Soicher's
book, as a `TauCeti.GroupPresentation`: the source, a locator inside it, the generator convention,
the transcription notes, the two counts the source determines, and the relator expressions
themselves.

## The source data and how it decodes

The library stores the presentation as three Coxeter paths together with nine further relations:

```text
b4h3a3b5c3d3f4c3e4a,  b4g4f,  e6f6h

a = (cf)²,  e = (bg)²,  b = (ef)³,  d = (bh)²,  d = (eah)³,
(adfh)³ = (baefg)³ = (cef)⁷ = (adefcefgh)³⁹ = 1
```

Its decoder reads a path `x m y n z` as a Coxeter graph on the nodes `x, y, z` with the edges
`x y` and `y z` labelled `m` and `n`. Every node of the graph is an involution, every labelled edge
`x m y` contributes the relator `(xy) ^ m`, and every pair of nodes that no path joins by an edge
contributes `(xy) ²`; an equation `u = v` contributes `u⁻¹ v`. The three paths above therefore give
the eight generators

```text
a, b, c, d, e, f, g, h
```

and the thirteen labelled edges

```text
(bh)⁴, (ha)³, (ab)³, (bc)⁵, (cd)³, (df)³, (fc)⁴, (ce)³, (ea)⁴, (bg)⁴, (gf)⁴, (ef)⁶, (fh)⁶,
```

leaving the fifteen pairs

```text
ac, ad, af, ag, bd, be, bf, cg, ch, de, dg, dh, eg, eh, gh
```

to commute. With the nine further relations appended that is `8 + 13 + 15 + 9 = 45` relators in
eight generators, of total compiled length `611`.

The library holds its Coxeter relators in GAP sets, so the source fixes no order on the relator
list. The order transcribed below is a choice, recorded in the row's transcription notes: the eight
involutions in generator order, the thirteen labelled edges in the order the paths print them, the
fifteen commuting pairs in lexicographic order, and then the nine further relations in source order.
Only `Relator.pow`, `Relator.mul` and `Relator.inv` are used, so the row needs no commutator
convention.

## What makes the source admissible

The library's documentation states that all of its presentations are found in Praeger and Soicher,
and that it distinguishes presentations of simple sporadic groups from presentations of their
automorphism groups; `Co₁` is listed among the former, with two presentations, of which this is the
first. These are presentations of the abstract groups, not ATLAS-style semi-presentations for
recognizing standard generators inside an already constructed group, and the ATLAS `Co₁` page
carries only a semi-presentation, so no ATLAS page could serve this row.

Two computations with GAP 4.15.1 are recorded as provenance for the transcription. Neither is a Lean
proof and neither is asserted by any theorem here. First, enumerating the compiled relators over the
subgroup that the library records as a `Co₂` in this presentation, namely
`⟨a, b, c, d, e, f, g, (adefcefgh)³⁹⟩`, closes on `98280` cosets, and the resulting degree-`98280`
permutation image of the presented group is simple of order `4157776806543360000 = |Co₁|`; the only
nonisomorphic finite simple groups of equal order are `A₈` with `L₃(4)` and `Bₙ(q)` with `Cₙ(q)`, so
that image is `Co₁` and the presented group has `Co₁` as a quotient, which is what a transcription
error in any relator would be expected to destroy. Second, in that image every
generator has order exactly `2`, every labelled edge's product has order exactly its label, every
commuting pair's product has order exactly `2`, and `cef` and `adefcefgh` have orders exactly `7`
and `39`, so no exponent transcribed above is larger than the order it records. The abelianization
of the presented group is trivial, as it must be for a presentation of a nonabelian simple group.

## What is and is not claimed

Nothing here asserts that the presented group is nontrivial, finite or simple, that it has any
particular order, or that it is isomorphic to any other construction of `Co₁`; those are downstream
statements the roadmap deliberately does not ask of this lane. What is proved is the transcription
arithmetic: the two counts, the compiled length of each relator and their total, and that every
compiled word is cyclically reduced, which is what makes those lengths comparable with a published
length. The library records a second presentation of `Co₁`, `GPLTable.Co1.2`, on nine generators;
it is not transcribed, since one presentation fills the row, and the record transcribed here is the
one whose recorded subgroup words admit the coset enumeration above. The comparison against the
`FiniteSimpleGroups` development that `TauCetiRoadmap/CFSGStatement/README.md` asks for on the names
that development covers is not available here, since it does not cover `Co₁`.

## Main definition

* `TauCeti.Sporadic.co1Presentation`: the Praeger--Soicher finite presentation of `Co₁` recorded as
  `GPLTable.Co1.1`.

## References

* R. Lindenbergh, *Group Presentations Library*, version 1.0, record `GPLTable.Co1.1`,
  <https://doris.tudelft.nl/~rlindenbergh/GPL/gpl.g>, documented at
  <https://doris.tudelft.nl/~rlindenbergh/GPL/GPL.html>;
* C. E. Praeger and L. H. Soicher, *Low Rank Representations and Graphs for Sporadic Groups*,
  Australian Mathematical Society Lecture Series 8, Cambridge University Press, 1997, Chapter 4
  *The Individual Groups*, pp. 29--128, <https://doi.org/10.1017/CBO9780511526039.005>, which the
  library cites as the origin of this presentation.
-/

public section

namespace TauCeti.Sporadic

/-! ### The alphabet of the presentation

The source writes its relators as words in eight involutory generators `a` to `h`, so the eight
expressions below are those eight letters and `⬝` is `TauCeti.Relator.mul`. A transcribed relator
then reads left to right exactly as the source prints it. -/

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

/-- The Praeger--Soicher finite presentation of the first Conway group `Co₁` on the eight involutory
generators of its Coxeter-type diagram, as recorded by `GPLTable.Co1.1`.

The list is the decoding of the source's three Coxeter paths — eight involutions, thirteen labelled
edges, fifteen commuting pairs — followed by the source's nine further relations. No structural
property of the presented group is asserted here: this definition records only the cited generators
and relations. -/
def co1Presentation : GroupPresentation where
  generatorNames := ["a", "b", "c", "d", "e", "f", "g", "h"]
  source := "R. Lindenbergh, Group Presentations Library, version 1.0, which cites C. E. Praeger \
    and L. H. Soicher, Low Rank Representations and Graphs for Sporadic Groups, Australian \
    Mathematical Society Lecture Series 8, Cambridge University Press, 1997, Chapter 4 (The \
    Individual Groups, pp. 29-128, doi:10.1017/CBO9780511526039.005) as the origin of the \
    presentation"
  sourceLocator := "record GPLTable.Co1.1 of https://doris.tudelft.nl/~rlindenbergh/GPL/gpl.g, \
    holding the Coxeter paths b4h3a3b5c3d3f4c3e4a, b4g4f, e6f6h and the nine relations \
    a=(cf)^2, e=(bg)^2, b=(ef)^3, d=(bh)^2, d=(eah)^3, (adfh)^3, (baefg)^3, (cef)^7, \
    (adefcefgh)^(39); the library is documented at \
    https://doris.tudelft.nl/~rlindenbergh/GPL/GPL.html"
  generatorConvention := "The eight nodes a, b, c, d, e, f, g, h of the source's Coxeter graph, in \
    alphabetical order, so index 0 is a and index 7 is h. Products are read left to right and \
    negative exponents denote inverses. Every node is an involution, a path x m y contributes \
    (xy)^m, a pair of nodes that no path joins contributes (xy)^2, and an equation u = v \
    contributes the relator u^-1 v. No commutator constructor is used."
  transcriptionNotes := "The 45 relators are the decoding of the source's three Coxeter paths \
    followed by its nine further relations: the 8 involutions in generator order, then the 13 \
    labelled edges (bh)^4, (ha)^3, (ab)^3, (bc)^5, (cd)^3, (df)^3, (fc)^4, (ce)^3, (ea)^4, \
    (bg)^4, (gf)^4, (ef)^6, (fh)^6 in the order the paths print them, then the 15 pairs ac, ad, \
    af, ag, bd, be, bf, cg, ch, de, dg, dh, eg, eh, gh that no path joins, in lexicographic order, \
    then the nine relations in source order. The library stores its Coxeter relators in GAP sets, \
    so that order is a transcription choice and not part of the source. The 45 relators and the \
    total compiled length 611 are the counts this decoding determines; the source publishes \
    neither. GAP 4.15.1 checks the transcription by enumerating 98280 cosets of the subgroup \
    (a, b, c, d, e, f, g, (adefcefgh)^39) that the library records as a Co2, whose degree-98280 \
    permutation image of the presented group is simple of order 4157776806543360000 = |Co1|, and \
    by confirming in that image that every generator has order exactly 2, that each labelled edge \
    and each unjoined pair has product of order exactly its label and exactly 2 respectively, and \
    that cef and adefcefgh have orders exactly 7 and 39."
  expectedGeneratorCount := 8
  expectedRelatorCount := 45
  transcribed :=
    [ -- the eight nodes are involutions
      .pow a 2,
      .pow b 2,
      .pow c 2,
      .pow d 2,
      .pow e 2,
      .pow f 2,
      .pow g 2,
      .pow h 2,
      -- the thirteen labelled edges of the paths b4h3a3b5c3d3f4c3e4a, b4g4f and e6f6h
      .pow (b ⬝ h) 4,
      .pow (h ⬝ a) 3,
      .pow (a ⬝ b) 3,
      .pow (b ⬝ c) 5,
      .pow (c ⬝ d) 3,
      .pow (d ⬝ f) 3,
      .pow (f ⬝ c) 4,
      .pow (c ⬝ e) 3,
      .pow (e ⬝ a) 4,
      .pow (b ⬝ g) 4,
      .pow (g ⬝ f) 4,
      .pow (e ⬝ f) 6,
      .pow (f ⬝ h) 6,
      -- the fifteen pairs of nodes that no path joins commute
      .pow (a ⬝ c) 2,
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
      .pow (g ⬝ h) 2,
      -- a = (cf)², e = (bg)², b = (ef)³, d = (bh)², d = (eah)³
      .inv a ⬝ .pow (c ⬝ f) 2,
      .inv e ⬝ .pow (b ⬝ g) 2,
      .inv b ⬝ .pow (e ⬝ f) 3,
      .inv d ⬝ .pow (b ⬝ h) 2,
      .inv d ⬝ .pow (e ⬝ a ⬝ h) 3,
      -- (adfh)³ = (baefg)³ = (cef)⁷ = (adefcefgh)³⁹ = 1
      .pow (a ⬝ d ⬝ f ⬝ h) 3,
      .pow (b ⬝ a ⬝ e ⬝ f ⬝ g) 3,
      .pow (c ⬝ e ⬝ f) 7,
      .pow (a ⬝ d ⬝ e ⬝ f ⬝ c ⬝ e ⬝ f ⬝ g ⬝ h) 39 ]

/-- The generator names recorded for `Co₁`. The row is a sealed definition, so this equation and the
six below are how a consumer downstream of this file reads off the provenance that a manifest row
exists to record. -/
@[simp]
theorem co1Presentation_generatorNames :
    co1Presentation.generatorNames = ["a", "b", "c", "d", "e", "f", "g", "h"] := by
  simp [co1Presentation]

/-- The source recorded for `Co₁`, naming both the library holding the relator data and the book it
credits with the presentation. -/
@[simp]
theorem co1Presentation_source :
    co1Presentation.source = "R. Lindenbergh, Group Presentations Library, version 1.0, which \
      cites C. E. Praeger and L. H. Soicher, Low Rank Representations and Graphs for Sporadic \
      Groups, Australian Mathematical Society Lecture Series 8, Cambridge University Press, 1997, \
      Chapter 4 (The Individual Groups, pp. 29-128, doi:10.1017/CBO9780511526039.005) as the \
      origin of the presentation" := by
  simp [co1Presentation]

/-- The locator recorded for `Co₁`, pinning the library record and reproducing its encoded
presentation. -/
@[simp]
theorem co1Presentation_sourceLocator :
    co1Presentation.sourceLocator = "record GPLTable.Co1.1 of \
      https://doris.tudelft.nl/~rlindenbergh/GPL/gpl.g, holding the Coxeter paths \
      b4h3a3b5c3d3f4c3e4a, b4g4f, e6f6h and the nine relations a=(cf)^2, e=(bg)^2, b=(ef)^3, \
      d=(bh)^2, d=(eah)^3, (adfh)^3, (baefg)^3, (cef)^7, (adefcefgh)^(39); the library is \
      documented at https://doris.tudelft.nl/~rlindenbergh/GPL/GPL.html" := by
  simp [co1Presentation]

/-- The generator convention recorded for `Co₁`, fixing which generator each relator index names and
how the source's Coxeter paths decode. -/
@[simp]
theorem co1Presentation_generatorConvention :
    co1Presentation.generatorConvention = "The eight nodes a, b, c, d, e, f, g, h of the source's \
      Coxeter graph, in alphabetical order, so index 0 is a and index 7 is h. Products are read \
      left to right and negative exponents denote inverses. Every node is an involution, a path \
      x m y contributes (xy)^m, a pair of nodes that no path joins contributes (xy)^2, and an \
      equation u = v contributes the relator u^-1 v. No commutator constructor is used." := by
  simp [co1Presentation]

/-- The transcription notes recorded for `Co₁`, including the order chosen for the decoded relators
and the outcome of the coset enumeration checking them. -/
@[simp]
theorem co1Presentation_transcriptionNotes :
    co1Presentation.transcriptionNotes = "The 45 relators are the decoding of the source's three \
      Coxeter paths followed by its nine further relations: the 8 involutions in generator order, \
      then the 13 labelled edges (bh)^4, (ha)^3, (ab)^3, (bc)^5, (cd)^3, (df)^3, (fc)^4, (ce)^3, \
      (ea)^4, (bg)^4, (gf)^4, (ef)^6, (fh)^6 in the order the paths print them, then the 15 pairs \
      ac, ad, af, ag, bd, be, bf, cg, ch, de, dg, dh, eg, eh, gh that no path joins, in \
      lexicographic order, then the nine relations in source order. The library stores its Coxeter \
      relators in GAP sets, so that order is a transcription choice and not part of the source. \
      The 45 relators and the total compiled length 611 are the counts this decoding determines; \
      the source publishes neither. GAP 4.15.1 checks the transcription by enumerating 98280 \
      cosets of the subgroup (a, b, c, d, e, f, g, (adefcefgh)^39) that the library records as a \
      Co2, whose degree-98280 permutation image of the presented group is simple of order \
      4157776806543360000 = |Co1|, and by confirming in that image that every generator has order \
      exactly 2, that each labelled edge and each unjoined pair has product of order exactly its \
      label and exactly 2 respectively, and that cef and adefcefgh have orders exactly 7 and \
      39." := by
  simp [co1Presentation]

/-- The generator count the source's Coxeter paths determine for `Co₁`. -/
@[simp]
theorem co1Presentation_expectedGeneratorCount : co1Presentation.expectedGeneratorCount = 8 := by
  simp [co1Presentation]

/-- The relator count the source's Coxeter paths and further relations determine for `Co₁`. -/
@[simp]
theorem co1Presentation_expectedRelatorCount : co1Presentation.expectedRelatorCount = 45 := by
  simp [co1Presentation]

/-- The generator and relator counts recorded for `Co₁` agree with the transcribed data. -/
theorem matchesMetadata_co1Presentation : co1Presentation.matchesMetadata := by decide

/-- The compiled length of each transcribed relator for `Co₁`, in the order of the list.

For a relator of the form `(xy) ^ m` this length is `2 * m`, so the twenty-eight lengths after the
eight `2`s of the involutions read off the label of every pair of nodes of the source's Coxeter
graph: a mislabelled edge, or a pair of nodes wrongly recorded as commuting, changes one of them. -/
theorem co1Presentation_map_length_relators :
    co1Presentation.relators.map List.length =
      [2, 2, 2, 2, 2, 2, 2, 2,
        8, 6, 6, 10, 6, 6, 8, 6, 8, 8, 8, 12, 12,
        4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
        5, 5, 7, 5, 10, 12, 15, 21, 351] := by
  rw [GroupPresentation.relators_def]
  simp only [co1Presentation, List.map_cons, List.map_nil, Relator.toWord_pow, Relator.toWord_mul,
    Relator.toWord_inv, Relator.toWord_gen, List.length_flatten, List.map_replicate,
    List.sum_replicate, List.length_append, List.length_cons, List.length_nil, List.length_reverse,
    FreeGroup.invRev, smul_eq_mul]

/-- The compiled relator words for `Co₁` have total length `611`, read off from the individual
lengths rather than from the record. The source publishes no length, so this figure is one the
transcription determines; it is recomputable from the relator list by the same route. -/
theorem co1Presentation_totalLength : co1Presentation.totalLength = 611 := by
  rw [GroupPresentation.totalLength_def, co1Presentation_map_length_relators]
  decide

/-- Every compiled relator word for `Co₁` is cyclically reduced. This is what makes the total length
above comparable with a published presentation length, which is measured after free and cyclic
reduction of each relator. -/
theorem co1Presentation_relatorsCyclicallyReduced : co1Presentation.relatorsCyclicallyReduced := by
  simp only [GroupPresentation.relatorsCyclicallyReduced_iff, GroupPresentation.relators_def,
    co1Presentation, List.map_cons, List.map_nil, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_inv, Relator.toWord_gen]
  decide +kernel

end TauCeti.Sporadic
