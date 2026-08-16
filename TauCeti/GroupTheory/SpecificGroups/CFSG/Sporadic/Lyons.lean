/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# A transcribed presentation of the Lyons group

This file carries the `Ly` row of the sporadic presentation data required by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. It records Volker Gebhardt's five-generator,
twenty-five-relator presentation of the Lyons sporadic group as a `TauCeti.GroupPresentation`,
together with its exact source, conventions, expected counts, and decidable checks.

Gebhardt constructs the presentation in three stages. The first nine relators present a subgroup
`5^(1+4) : GL₂(5)` on `a`, `b`, and `c`; seven more extend this to `G₂(5)` on `a`, `b`, `c`, and
`d`; the final nine extend it to `Ly` on `a`, `b`, `c`, `d`, and `z`. Double-coset enumeration
proves at each stage that the displayed relations define the claimed group. The three blocks have
freely reduced lengths `80`, `160`, and `309`, giving the published total length `549`.

The source writes `x̄` for `x⁻¹`, `x^y` for `y⁻¹xy`, which is `TauCeti.Relator.conj`, and `[x,y]`
for `x⁻¹y⁻¹xy`, transcribed as `TauCeti.Relator.comm (.inv x) (.inv y)`. An equation `r = s` is
stored as the relator `r * s⁻¹`, which is `TauCeti.Relator.div`. The structured expressions below
preserve the source's powers, conjugates, commutators, and equations. Since their direct compilation
need not perform free cancellation, decidable checks apply Mathlib's `FreeGroup.reduce` before
checking the three block lengths and their total, and then check that the reduced words are
cyclically reduced.

The proved `TauCeti.Relator.toWord_toFreeGroup` is the audit boundary between the expressions and
the signed words consumed by `PresentedGroup`. This file asserts no order, finiteness, simplicity,
or identification theorem for the presented group. The independent `FiniteSimpleGroups`
development named by the roadmap does not cover `Ly`, so that cross-check is unavailable here.

## Main definition

* `TauCeti.Sporadic.lyPresentation`: Gebhardt's finite presentation of `Ly`.

## References

* V. Gebhardt, *Two Short Presentations for Lyons' Sporadic Simple Group*, Experimental
  Mathematics **9** (2000), no. 3, 333--338, especially Section 3B and p. 336,
  <https://doi.org/10.1080/10586458.2000.10504410>.
* The article is also catalogued with full-text access at
  <https://eudml.org/doc/222733>.
-/

public section

namespace TauCeti.Sporadic

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

private abbrev sourceComm {α : Type*} (r s : Relator α) : Relator α :=
  .comm (.inv r) (.inv s)

/-- The nine relators in the source's `R_H2` block, on its generator expressions `a`, `b`, and
`c`. -/
private def lyH2Relators {α : Type*} (a b c : Relator α) : List (Relator α) :=
  let bInv := .inv b
  [ .pow a 8,
    .pow b 5,
    .pow (a ⬝ b) 4,
    sourceComm (.pow a 2) b,
    .pow (sourceComm a b) 3,
    .pow c 5,
    Relator.div (Relator.conj c (.pow a 2)) (.pow c 3),
    Relator.div (Relator.conj c (b ⬝ a))
      (Relator.conj c (.pow a 2 ⬝ b) ⬝ c ⬝ b ⬝ c ⬝ bInv),
    Relator.div (Relator.conj c (.pow b 2))
      (.pow c 2 ⬝ Relator.conj c bInv ⬝ .pow (.inv (Relator.conj c b)) 2) ]

/-- The seven relators in the source's `R_H1` block, on its generator expressions `a`, `b`, `c`,
and `d`. -/
private def lyH1Relators {α : Type*} (a b c d : Relator α) : List (Relator α) :=
  let aInv := .inv a
  let bInv := .inv b
  let cInv := .inv c
  let dInv := .inv d
  [ Relator.div (Relator.conj (a ⬝ bInv ⬝ a) d) (a ⬝ bInv ⬝ .pow a 5),
    Relator.div (Relator.conj (.pow b 2 ⬝ aInv) d) (.pow aInv 2 ⬝ .pow b 2 ⬝ aInv),
    Relator.div
      (Relator.conj (b ⬝ a ⬝ cInv ⬝ b ⬝ a ⬝ .pow bInv 2 ⬝ a) (d ⬝ c ⬝ d))
      (aInv ⬝ b ⬝ aInv ⬝ bInv ⬝ a ⬝ .pow bInv 2 ⬝ a ⬝ c ⬝ bInv ⬝ c ⬝ b ⬝
        a ⬝ cInv),
    Relator.div
      (Relator.conj (.pow a 2 ⬝ cInv ⬝ b ⬝ a ⬝ cInv ⬝ b ⬝ aInv ⬝ bInv)
        (d ⬝ c ⬝ d))
      (.pow aInv 2 ⬝ bInv ⬝ aInv ⬝ .pow (bInv ⬝ c) 2 ⬝ .pow b 2),
    Relator.div
      (Relator.conj (.pow b 2 ⬝ a ⬝ c ⬝ b ⬝ a) (d ⬝ c ⬝ aInv ⬝ b ⬝ c ⬝ d))
      (aInv ⬝ b ⬝ aInv ⬝ bInv ⬝ a ⬝ .pow bInv 2 ⬝ c ⬝ aInv ⬝ bInv ⬝ c ⬝
        b ⬝ a),
    Relator.div
      (Relator.conj (a ⬝ .pow cInv 2 ⬝ b) (d ⬝ c ⬝ aInv ⬝ b ⬝ c ⬝ d))
      (.pow aInv 4 ⬝ .pow b 2 ⬝ cInv ⬝ bInv ⬝ a ⬝ bInv ⬝ c ⬝ a ⬝ bInv),
    c ⬝ aInv ⬝ cInv ⬝ a ⬝ cInv ⬝ aInv ⬝ c ⬝ a ⬝ dInv ⬝ cInv ⬝ aInv ⬝
      cInv ⬝ a ⬝ c ⬝ aInv ⬝ c ⬝ d ⬝ c ⬝ a ⬝ cInv ⬝ aInv ⬝ cInv ⬝ a ⬝ c ⬝ d ]

/-- The nine relators in the source's final `R_G` block extending the presentation to `Ly`, on its
generator expressions `a`, `b`, `c`, `d`, and `z`. -/
private def lyExtensionRelators {α : Type*} (a b c d z : Relator α) : List (Relator α) :=
  let aInv := .inv a
  let bInv := .inv b
  let cInv := .inv c
  let dInv := .inv d
  let zInv := .inv z
  [ Relator.div (Relator.conj a z) (.pow aInv 3),
    Relator.div (Relator.conj a (z ⬝ d ⬝ z)) (.pow a 3),
    Relator.div
      (Relator.conj
        (cInv ⬝ dInv ⬝ c ⬝ b ⬝ a ⬝ .pow b 2 ⬝ .pow (c ⬝ b) 2 ⬝ cInv ⬝ d)
        (z ⬝ d ⬝ z))
      (cInv ⬝ b ⬝ .pow c 2 ⬝ a ⬝ cInv ⬝ b ⬝ dInv ⬝ c ⬝ a ⬝ cInv ⬝ b ⬝ c ⬝
        .pow bInv 2 ⬝ c ⬝ a ⬝ c ⬝ dInv ⬝ c ⬝ .pow bInv 2 ⬝ c ⬝ d ⬝ a ⬝
        dInv ⬝ cInv ⬝ dInv ⬝ c ⬝ b ⬝ aInv ⬝ b),
    Relator.div
      (sourceComm z
        (dInv ⬝ cInv ⬝ b ⬝ a ⬝ bInv ⬝ d ⬝ c ⬝ d ⬝ cInv ⬝ d ⬝ cInv ⬝ b ⬝
          a ⬝ bInv ⬝ c ⬝ d ⬝ c ⬝ d))
      (b ⬝ c ⬝ bInv ⬝ cInv),
    Relator.div (Relator.conj a (z ⬝ d ⬝ bInv ⬝ z))
      (aInv ⬝ dInv ⬝ cInv ⬝ b ⬝ .pow cInv 2 ⬝ a ⬝ bInv ⬝ c ⬝ a ⬝
        .pow bInv 2 ⬝ c ⬝ bInv ⬝ c ⬝ a ⬝ cInv ⬝ d ⬝ bInv ⬝ aInv),
    Relator.div
      (Relator.conj
        (cInv ⬝ aInv ⬝ dInv ⬝ cInv ⬝ b ⬝ a ⬝ bInv ⬝ a ⬝ cInv ⬝ b ⬝ c ⬝ a ⬝
          cInv ⬝ dInv ⬝ c ⬝ d ⬝ a ⬝ c ⬝ bInv ⬝ a ⬝ b ⬝ a ⬝ c)
        (z ⬝ d ⬝ bInv ⬝ z))
      (aInv ⬝ c ⬝ .pow aInv 3 ⬝ cInv ⬝ .pow bInv 2 ⬝ cInv ⬝ d ⬝ cInv ⬝ a ⬝
        cInv ⬝ .pow b 2 ⬝ c ⬝ bInv ⬝ c ⬝ aInv ⬝ cInv ⬝ d ⬝ bInv ⬝ cInv ⬝
        dInv ⬝ cInv ⬝ b ⬝ a ⬝ b ⬝ d ⬝ c ⬝ aInv),
    Relator.div
      (Relator.conj
        (aInv ⬝ b ⬝ d ⬝ c ⬝ aInv ⬝ bInv ⬝ a ⬝ b ⬝ aInv ⬝ cInv ⬝ bInv ⬝ c ⬝ a)
        (z ⬝ d ⬝ c ⬝ d ⬝ z))
      (cInv ⬝ .pow a 3 ⬝ b ⬝ cInv ⬝ bInv ⬝ aInv ⬝ c ⬝ dInv ⬝ cInv ⬝ b ⬝
        aInv ⬝ bInv),
    Relator.div (Relator.conj (dInv ⬝ c ⬝ b ⬝ aInv ⬝ bInv) (z ⬝ d ⬝ c ⬝ d ⬝ z))
      (a ⬝ c ⬝ aInv ⬝ b ⬝ a ⬝ cInv ⬝ b ⬝ c ⬝ a ⬝ cInv ⬝ bInv ⬝ aInv ⬝
        bInv ⬝ a ⬝ b ⬝ dInv ⬝ c ⬝ a ⬝ cInv ⬝ bInv ⬝ cInv ⬝ a),
    a ⬝ dInv ⬝ cInv ⬝ b ⬝ .pow aInv 2 ⬝ dInv ⬝ cInv ⬝ .pow bInv 2 ⬝ cInv ⬝
      d ⬝ cInv ⬝ .pow (a ⬝ cInv) 2 ⬝ b ⬝ aInv ⬝ .pow c 2 ⬝ bInv ⬝ c ⬝ dInv ⬝
      c ⬝ a ⬝ c ⬝ bInv ⬝ a ⬝ dInv ⬝ zInv ⬝ b ⬝ z ⬝ bInv ⬝ z ]

private abbrev a : Relator (Fin 5) := .gen 0
private abbrev b : Relator (Fin 5) := .gen 1
private abbrev c : Relator (Fin 5) := .gen 2
private abbrev d : Relator (Fin 5) := .gen 3
private abbrev z : Relator (Fin 5) := .gen 4

private abbrev h2Relators : List (Relator (Fin 5)) := lyH2Relators a b c
private abbrev h1Relators : List (Relator (Fin 5)) := lyH1Relators a b c d
private abbrev extensionRelators : List (Relator (Fin 5)) := lyExtensionRelators a b c d z

private theorem reducedH2Length :
    (h2Relators.map fun r => (FreeGroup.reduce r.toWord).length).sum = 80 := by
  simp only [h2Relators, lyH2Relators, List.map_cons, List.map_nil,
    Relator.toWord_gen, Relator.toWord_inv, Relator.toWord_mul, Relator.toWord_pow,
    sourceComm, Relator.toWord_comm, Relator.toWord_conj, Relator.toWord_div]
  decide

private theorem reducedH1Length :
    (h1Relators.map fun r => (FreeGroup.reduce r.toWord).length).sum = 160 := by
  simp only [h1Relators, lyH1Relators, List.map_cons, List.map_nil,
    Relator.toWord_gen, Relator.toWord_inv, Relator.toWord_mul, Relator.toWord_pow,
    Relator.toWord_conj, Relator.toWord_div]
  decide

private theorem reducedLyExtensionLength :
    (extensionRelators.map fun r => (FreeGroup.reduce r.toWord).length).sum = 309 := by
  simp only [extensionRelators, lyExtensionRelators,
    List.map_cons, List.map_nil, Relator.toWord_gen, Relator.toWord_inv,
    Relator.toWord_mul, Relator.toWord_pow, sourceComm, Relator.toWord_comm,
    Relator.toWord_conj, Relator.toWord_div]
  decide

private theorem reducedTotalLength :
    ((h2Relators ++ h1Relators ++ extensionRelators).map fun r =>
      (FreeGroup.reduce r.toWord).length).sum = 549 := by
  simp only [List.map_append, List.sum_append]
  rw [reducedH2Length, reducedH1Length, reducedLyExtensionLength]

/-- Gebhardt's finite presentation of the Lyons sporadic group `Ly` on five generators.

Section 3B of the source proves that these twenty-five relators define `Ly` by extending the
presentations of `5^(1+4) : GL₂(5)` and `G₂(5)` through two double-coset enumerations. No
structural property of the resulting `PresentedGroup` is asserted here; the definition records
only the cited generators and relators. -/
def lyPresentation : GroupPresentation where
  generatorNames := ["a", "b", "c", "d", "z"]
  source := "V. Gebhardt, Two Short Presentations for Lyons' Sporadic Simple Group, \
    Experimental Mathematics 9 (2000), no. 3, 333--338"
  sourceLocator := "Section 3B, especially p. 336, sets R_H2, R_H1, and R_G; \
    https://doi.org/10.1080/10586458.2000.10504410; full-text catalogue at \
    https://eudml.org/doc/222733"
  generatorConvention := "The source's generators a, b, c, d, z, in that order, so indices 0, \
    1, 2, 3, 4 denote a, b, c, d, z. A barred letter is its inverse, x^y means y^-1*x*y, \
    [x,y] means x^-1*y^-1*x*y, and products are read left to right."
  transcriptionNotes := "The nine R_H2 relators, seven R_H1 relators, and nine R_G relators are \
    stored in the source's order. An equation r=s is compiled as r*s^-1. Free reduction gives \
    block lengths 80, 160, and 309, matching the figures printed by the source and its total 549; \
    decidable checks verify these lengths and that every reduced word is cyclically reduced. In \
    R_G relator 4 the source prints the right side as the literal word b*c*b^-1*c^-1, not as a \
    bracketed commutator. The paper proves the presentation by double-coset enumeration. The \
    independent FiniteSimpleGroups development does not cover Ly."
  expectedGeneratorCount := 5
  expectedRelatorCount := 25
  transcribed :=
    lyH2Relators (.gen 0) (.gen 1) (.gen 2) ++
      lyH1Relators (.gen 0) (.gen 1) (.gen 2) (.gen 3) ++
      lyExtensionRelators (.gen 0) (.gen 1) (.gen 2) (.gen 3) (.gen 4)

/-- The generator names recorded for `Ly`. -/
@[simp]
theorem lyPresentation_generatorNames :
    lyPresentation.generatorNames = ["a", "b", "c", "d", "z"] := by
  rfl

/-- The source recorded for `Ly`. -/
@[simp]
theorem lyPresentation_source :
    lyPresentation.source =
      "V. Gebhardt, Two Short Presentations for Lyons' Sporadic Simple Group, \
        Experimental Mathematics 9 (2000), no. 3, 333--338" := by
  rfl

/-- The locator recorded for `Ly`, including the DOI and full-text catalogue entry. -/
@[simp]
theorem lyPresentation_sourceLocator :
    lyPresentation.sourceLocator = "Section 3B, especially p. 336, sets R_H2, R_H1, and R_G; \
      https://doi.org/10.1080/10586458.2000.10504410; full-text catalogue at \
      https://eudml.org/doc/222733" := by
  rfl

/-- The generator and source-notation convention recorded for `Ly`. -/
@[simp]
theorem lyPresentation_generatorConvention :
    lyPresentation.generatorConvention = "The source's generators a, b, c, d, z, in that order, \
      so indices 0, 1, 2, 3, 4 denote a, b, c, d, z. A barred letter is its inverse, x^y means \
      y^-1*x*y, [x,y] means x^-1*y^-1*x*y, and products are read left to right." := by
  rfl

/-- The transcription and verification notes recorded for `Ly`. -/
@[simp]
theorem lyPresentation_transcriptionNotes :
    lyPresentation.transcriptionNotes = "The nine R_H2 relators, seven R_H1 relators, and nine \
      R_G relators are stored in the source's order. An equation r=s is compiled as r*s^-1. Free \
      reduction gives block lengths 80, 160, and 309, matching the figures printed by the source \
      and its total 549; decidable checks verify these lengths and that every reduced word is \
      cyclically reduced. In R_G relator 4 the source prints the right side as the literal word \
      b*c*b^-1*c^-1, not as a bracketed commutator. The paper proves the presentation by \
      double-coset enumeration. The independent FiniteSimpleGroups development does not cover \
      Ly." := by
  rfl

/-- The generator count recorded for `Ly`. -/
@[simp]
theorem lyPresentation_expectedGeneratorCount : lyPresentation.expectedGeneratorCount = 5 := by
  rfl

/-- The relator count recorded for `Ly`. -/
@[simp]
theorem lyPresentation_expectedRelatorCount : lyPresentation.expectedRelatorCount = 25 := by
  rfl

/-- The twenty-five relator expressions transcribed for `Ly`, written out in the source's order.

The row's body is sealed, so this is the equation that characterizes it: with
`TauCeti.GroupPresentation.relators_def` it determines the compiled words, and with
`TauCeti.GroupPresentation.mem_relatorSet_iff` it determines the relations defining
`TauCeti.GroupPresentation.Group`, so a consumer never has to unfold the row. Indices `0` through
`4` are the generators `a`, `b`, `c`, `d`, and `z`, and the bounds come from
`TauCeti.Sporadic.lyPresentation_generatorNames`. The first nine entries are the source's `R_H2`
block, the next seven its `R_H1` block, and the last nine its `R_G` block. -/
@[simp]
theorem lyPresentation_transcribed :
    lyPresentation.transcribed =
      let a : Relator (Fin lyPresentation.generatorNames.length) :=
        .gen ⟨0, by simp [lyPresentation]⟩
      let b : Relator (Fin lyPresentation.generatorNames.length) :=
        .gen ⟨1, by simp [lyPresentation]⟩
      let c : Relator (Fin lyPresentation.generatorNames.length) :=
        .gen ⟨2, by simp [lyPresentation]⟩
      let d : Relator (Fin lyPresentation.generatorNames.length) :=
        .gen ⟨3, by simp [lyPresentation]⟩
      let z : Relator (Fin lyPresentation.generatorNames.length) :=
        .gen ⟨4, by simp [lyPresentation]⟩
      let aInv := Relator.inv a
      let bInv := Relator.inv b
      let cInv := Relator.inv c
      let dInv := Relator.inv d
      let zInv := Relator.inv z
      [ .pow a 8,
        .pow b 5,
        .pow (a ⬝ b) 4,
        Relator.comm (.inv (.pow a 2)) (.inv b),
        .pow (Relator.comm (.inv a) (.inv b)) 3,
        .pow c 5,
        Relator.div (Relator.conj c (.pow a 2)) (.pow c 3),
        Relator.div (Relator.conj c (b ⬝ a))
          (Relator.conj c (.pow a 2 ⬝ b) ⬝ c ⬝ b ⬝ c ⬝ bInv),
        Relator.div (Relator.conj c (.pow b 2))
          (.pow c 2 ⬝ Relator.conj c bInv ⬝ .pow (.inv (Relator.conj c b)) 2),
        Relator.div (Relator.conj (a ⬝ bInv ⬝ a) d) (a ⬝ bInv ⬝ .pow a 5),
        Relator.div (Relator.conj (.pow b 2 ⬝ aInv) d) (.pow aInv 2 ⬝ .pow b 2 ⬝ aInv),
        Relator.div
          (Relator.conj (b ⬝ a ⬝ cInv ⬝ b ⬝ a ⬝ .pow bInv 2 ⬝ a) (d ⬝ c ⬝ d))
          (aInv ⬝ b ⬝ aInv ⬝ bInv ⬝ a ⬝ .pow bInv 2 ⬝ a ⬝ c ⬝ bInv ⬝ c ⬝ b ⬝
            a ⬝ cInv),
        Relator.div
          (Relator.conj (.pow a 2 ⬝ cInv ⬝ b ⬝ a ⬝ cInv ⬝ b ⬝ aInv ⬝ bInv)
            (d ⬝ c ⬝ d))
          (.pow aInv 2 ⬝ bInv ⬝ aInv ⬝ .pow (bInv ⬝ c) 2 ⬝ .pow b 2),
        Relator.div
          (Relator.conj (.pow b 2 ⬝ a ⬝ c ⬝ b ⬝ a) (d ⬝ c ⬝ aInv ⬝ b ⬝ c ⬝ d))
          (aInv ⬝ b ⬝ aInv ⬝ bInv ⬝ a ⬝ .pow bInv 2 ⬝ c ⬝ aInv ⬝ bInv ⬝ c ⬝
            b ⬝ a),
        Relator.div
          (Relator.conj (a ⬝ .pow cInv 2 ⬝ b) (d ⬝ c ⬝ aInv ⬝ b ⬝ c ⬝ d))
          (.pow aInv 4 ⬝ .pow b 2 ⬝ cInv ⬝ bInv ⬝ a ⬝ bInv ⬝ c ⬝ a ⬝ bInv),
        c ⬝ aInv ⬝ cInv ⬝ a ⬝ cInv ⬝ aInv ⬝ c ⬝ a ⬝ dInv ⬝ cInv ⬝ aInv ⬝
          cInv ⬝ a ⬝ c ⬝ aInv ⬝ c ⬝ d ⬝ c ⬝ a ⬝ cInv ⬝ aInv ⬝ cInv ⬝ a ⬝ c ⬝ d,
        Relator.div (Relator.conj a z) (.pow aInv 3),
        Relator.div (Relator.conj a (z ⬝ d ⬝ z)) (.pow a 3),
        Relator.div
          (Relator.conj
            (cInv ⬝ dInv ⬝ c ⬝ b ⬝ a ⬝ .pow b 2 ⬝ .pow (c ⬝ b) 2 ⬝ cInv ⬝ d)
            (z ⬝ d ⬝ z))
          (cInv ⬝ b ⬝ .pow c 2 ⬝ a ⬝ cInv ⬝ b ⬝ dInv ⬝ c ⬝ a ⬝ cInv ⬝ b ⬝ c ⬝
            .pow bInv 2 ⬝ c ⬝ a ⬝ c ⬝ dInv ⬝ c ⬝ .pow bInv 2 ⬝ c ⬝ d ⬝ a ⬝
            dInv ⬝ cInv ⬝ dInv ⬝ c ⬝ b ⬝ aInv ⬝ b),
        Relator.div
          (Relator.comm (.inv z) (.inv
            (dInv ⬝ cInv ⬝ b ⬝ a ⬝ bInv ⬝ d ⬝ c ⬝ d ⬝ cInv ⬝ d ⬝ cInv ⬝ b ⬝
              a ⬝ bInv ⬝ c ⬝ d ⬝ c ⬝ d)))
          (b ⬝ c ⬝ bInv ⬝ cInv),
        Relator.div (Relator.conj a (z ⬝ d ⬝ bInv ⬝ z))
          (aInv ⬝ dInv ⬝ cInv ⬝ b ⬝ .pow cInv 2 ⬝ a ⬝ bInv ⬝ c ⬝ a ⬝
            .pow bInv 2 ⬝ c ⬝ bInv ⬝ c ⬝ a ⬝ cInv ⬝ d ⬝ bInv ⬝ aInv),
        Relator.div
          (Relator.conj
            (cInv ⬝ aInv ⬝ dInv ⬝ cInv ⬝ b ⬝ a ⬝ bInv ⬝ a ⬝ cInv ⬝ b ⬝ c ⬝ a ⬝
              cInv ⬝ dInv ⬝ c ⬝ d ⬝ a ⬝ c ⬝ bInv ⬝ a ⬝ b ⬝ a ⬝ c)
            (z ⬝ d ⬝ bInv ⬝ z))
          (aInv ⬝ c ⬝ .pow aInv 3 ⬝ cInv ⬝ .pow bInv 2 ⬝ cInv ⬝ d ⬝ cInv ⬝ a ⬝
            cInv ⬝ .pow b 2 ⬝ c ⬝ bInv ⬝ c ⬝ aInv ⬝ cInv ⬝ d ⬝ bInv ⬝ cInv ⬝
            dInv ⬝ cInv ⬝ b ⬝ a ⬝ b ⬝ d ⬝ c ⬝ aInv),
        Relator.div
          (Relator.conj
            (aInv ⬝ b ⬝ d ⬝ c ⬝ aInv ⬝ bInv ⬝ a ⬝ b ⬝ aInv ⬝ cInv ⬝ bInv ⬝ c ⬝ a)
            (z ⬝ d ⬝ c ⬝ d ⬝ z))
          (cInv ⬝ .pow a 3 ⬝ b ⬝ cInv ⬝ bInv ⬝ aInv ⬝ c ⬝ dInv ⬝ cInv ⬝ b ⬝
            aInv ⬝ bInv),
        Relator.div (Relator.conj (dInv ⬝ c ⬝ b ⬝ aInv ⬝ bInv) (z ⬝ d ⬝ c ⬝ d ⬝ z))
          (a ⬝ c ⬝ aInv ⬝ b ⬝ a ⬝ cInv ⬝ b ⬝ c ⬝ a ⬝ cInv ⬝ bInv ⬝ aInv ⬝
            bInv ⬝ a ⬝ b ⬝ dInv ⬝ c ⬝ a ⬝ cInv ⬝ bInv ⬝ cInv ⬝ a),
        a ⬝ dInv ⬝ cInv ⬝ b ⬝ .pow aInv 2 ⬝ dInv ⬝ cInv ⬝ .pow bInv 2 ⬝ cInv ⬝
          d ⬝ cInv ⬝ .pow (a ⬝ cInv) 2 ⬝ b ⬝ aInv ⬝ .pow c 2 ⬝ bInv ⬝ c ⬝ dInv ⬝
      c ⬝ a ⬝ c ⬝ bInv ⬝ a ⬝ dInv ⬝ zInv ⬝ b ⬝ z ⬝ bInv ⬝ z ] := by
  rfl

/-- Free reduction makes every compiled relator word cyclically reduced.

The structured equation relators can contain cancellations at their concatenation boundary, so
this checks the reduced words used for comparison with the source's published length figures. -/
theorem isCyclicallyReduced_reduce_mem_lyPresentation_relators :
    ∀ w ∈ lyPresentation.relators,
      FreeGroup.IsCyclicallyReduced (FreeGroup.reduce w) := by
  simp only [GroupPresentation.relators_def, lyPresentation_transcribed, List.map_cons,
    List.map_nil, Relator.toWord_gen, Relator.toWord_inv, Relator.toWord_mul,
    Relator.toWord_pow, Relator.toWord_comm, Relator.toWord_conj, Relator.toWord_div]
  decide

private theorem lyPresentation_blockDecomposition :
    lyPresentation.transcribed = h2Relators ++ h1Relators ++ extensionRelators := by
  rfl

private theorem lyPresentation_h2Block :
    lyPresentation.transcribed.take 9 = h2Relators := by
  rw [lyPresentation_blockDecomposition]
  rfl

private theorem lyPresentation_h1Block :
    (lyPresentation.transcribed.drop 9).take 7 = h1Relators := by
  rw [lyPresentation_blockDecomposition]
  rfl

private theorem lyPresentation_extensionBlock :
    lyPresentation.transcribed.drop 16 = extensionRelators := by
  rw [lyPresentation_blockDecomposition]
  rfl

/-- The freely reduced lengths of the first nine relators sum to `80`, as recorded for the
`R_H2` block in the source. -/
theorem lyPresentation_reducedH2Length :
    ((lyPresentation.transcribed.take 9).map fun r =>
      (FreeGroup.reduce r.toWord).length).sum = 80 := by
  rw [lyPresentation_h2Block]
  exact reducedH2Length

/-- The freely reduced lengths of relators 10 through 16 sum to `160`, as recorded for the
`R_H1` block in the source. -/
theorem lyPresentation_reducedH1Length :
    (((lyPresentation.transcribed.drop 9).take 7).map fun r =>
      (FreeGroup.reduce r.toWord).length).sum = 160 := by
  rw [lyPresentation_h1Block]
  exact reducedH1Length

/-- The freely reduced lengths of the final nine relators sum to `309`, as recorded for the
`R_G` block in the source. -/
theorem lyPresentation_reducedExtensionLength :
    ((lyPresentation.transcribed.drop 16).map fun r =>
      (FreeGroup.reduce r.toWord).length).sum = 309 := by
  rw [lyPresentation_extensionBlock]
  exact reducedLyExtensionLength

/-- The freely reduced lengths of all twenty-five relators sum to the source's total `549`. -/
theorem lyPresentation_reducedTotalLength :
    (lyPresentation.transcribed.map fun r =>
      (FreeGroup.reduce r.toWord).length).sum = 549 := by
  rw [lyPresentation_blockDecomposition]
  exact reducedTotalLength

/-- The generator and relator counts recorded for `Ly` agree with the transcribed data. -/
theorem matchesMetadata_lyPresentation : lyPresentation.matchesMetadata := by
  decide

end TauCeti.Sporadic
