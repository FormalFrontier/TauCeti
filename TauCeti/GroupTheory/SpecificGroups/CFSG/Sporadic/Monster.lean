/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.Coxeter

/-!
# A transcribed presentation of the Monster group

This file carries the `M` row of the sporadic presentation data required by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. It records the `Y₄₄₃` presentation of the Monster as a
`TauCeti.GroupPresentation`, together with the exact diagram, source conventions, expected counts,
and decidable transcription checks.

The twelve involutory generators are the central node `a` and the nodes on three arms of lengths
four, four, and three:

```text
e₁ -- d₁ -- c₁ -- b₁ -- a -- b₂ -- c₂ -- d₂ -- e₂
                         |
                         b₃ -- c₃ -- d₃
```

The Coxeter relations contribute `12` square relations, `11` order-three edge relations, and `55`
order-two nonedge relations. The spider relation

```text
(a b₁ c₁ a b₂ c₂ a b₃ c₃)¹⁰ = 1
```

gives the `79`-relator presentation of `M × 2` displayed by Bray. Ivanov defines

```text
f₃₁₂ = (a b₃ c₃ d₃ b₁ c₁ b₂)⁹,
```

proves that it is central, and in Section 3.9 identifies the quotient `Y₄₄₃ / ⟨f₃₁₂⟩` with the
Monster. Appending `f₃₁₂ = 1` therefore gives the required `80`-relator presentation of `M`.

The source records length `400` for the `M × 2` presentation. The Coxeter words and spider word
below reproduce that figure; the final central relator has length `63`, giving total length `463`.

This file asserts no order, finiteness, or simplicity result for the presented group. The roadmap's
independent permutation-group cross-check does not cover `M`, whose smallest faithful permutation
representation is far too large for that construction.

## Main definitions

* `TauCeti.Sporadic.Monster.coxeterMatrix`: the explicitly numbered `Y₄₄₃` Coxeter matrix.
* `TauCeti.Sporadic.Monster.spiderRelator`: the `Y₄₄₃` spider relation.
* `TauCeti.Sporadic.Monster.centralInvolutionRelator`: Ivanov's element `f₃₁₂`.
* `TauCeti.Sporadic.Monster.presentation`: the resulting finite presentation of `M`.

## References

* J. N. Bray, *Sporadic (Fischer--Griess) Monster group M = F₁*, especially the `Y₄₄₃`
  presentation of `M × 2`,
  <https://webspace.maths.qmul.ac.uk/j.n.bray/web/Pres/Mnst.html>.
* A. A. Ivanov, *Y-groups via Transitive Extension*, Journal of Algebra **218** (1999), 412--435,
  especially the definition of `Yₚᵩᵣ` on p. 413, Lemma 3.2 on p. 419, and Section 3.9 on
  pp. 430--431, <https://doi.org/10.1006/jabr.1999.7882>.
-/

public section

namespace TauCeti.Sporadic.Monster

/-! ### The numbered `Y₄₄₃` diagram -/

/-- The eleven edges of the `Y₄₄₃` diagram. The numbering is
`a = 0`, `b₁,c₁,d₁,e₁ = 1,2,3,4`, `b₂,c₂,d₂,e₂ = 5,6,7,8`, and
`b₃,c₃,d₃ = 9,10,11`. Each pair is oriented away from the central node. -/
def edges : List (Fin 12 × Fin 12) :=
  [(0, 1), (1, 2), (2, 3), (3, 4),
    (0, 5), (5, 6), (6, 7), (7, 8),
    (0, 9), (9, 10), (10, 11)]

/-- The explicit edge list of the numbered `Y₄₄₃` diagram. This is the unfolding lemma for the
sealed body. -/
theorem edges_def : edges =
    [(0, 1), (1, 2), (2, 3), (3, 4),
      (0, 5), (5, 6), (6, 7), (7, 8),
      (0, 9), (9, 10), (10, 11)] := by
  rw [edges]

/-- The Coxeter matrix of `Y₄₄₃`, the simply laced matrix of its edge list: diagonal entries are
one, an edge has label three, and every other pair has label two. -/
def coxeterMatrix : CoxeterMatrix (Fin 12) := coxeterMatrixOfEdges edges

/-- Evaluation of the `Y₄₄₃` Coxeter matrix directly from its edge list. -/
@[simp]
theorem coxeterMatrix_apply (i j : Fin 12) :
    coxeterMatrix i j =
      if i = j then 1 else if (i, j) ∈ edges ∨ (j, i) ∈ edges then 3 else 2 := by
  rw [coxeterMatrix, coxeterMatrixOfEdges_apply]

/-! ### The two non-Coxeter relators -/

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

private abbrev a : Relator (Fin 12) := .gen 0
private abbrev b1 : Relator (Fin 12) := .gen 1
private abbrev c1 : Relator (Fin 12) := .gen 2
private abbrev d1 : Relator (Fin 12) := .gen 3
private abbrev e1 : Relator (Fin 12) := .gen 4
private abbrev b2 : Relator (Fin 12) := .gen 5
private abbrev c2 : Relator (Fin 12) := .gen 6
private abbrev d2 : Relator (Fin 12) := .gen 7
private abbrev e2 : Relator (Fin 12) := .gen 8
private abbrev b3 : Relator (Fin 12) := .gen 9
private abbrev c3 : Relator (Fin 12) := .gen 10
private abbrev d3 : Relator (Fin 12) := .gen 11

/-- The spider relator `(a b₁ c₁ a b₂ c₂ a b₃ c₃)¹⁰` of the `Y₄₄₃` presentation. -/
def spiderRelator : Relator (Fin 12) :=
  .pow (a ⬝ b1 ⬝ c1 ⬝ a ⬝ b2 ⬝ c2 ⬝ a ⬝ b3 ⬝ c3) 10

/-- The spider relator spelled out in the numbered alphabet. This is the unfolding lemma for the
sealed body. -/
theorem spiderRelator_def : spiderRelator =
    .pow (.gen 0 ⬝ .gen 1 ⬝ .gen 2 ⬝ .gen 0 ⬝ .gen 5 ⬝ .gen 6 ⬝ .gen 0 ⬝
      .gen 9 ⬝ .gen 10) 10 := by
  rw [spiderRelator]

/-- Ivanov's central element `f₃₁₂ = (a b₃ c₃ d₃ b₁ c₁ b₂)⁹`, imposed as a relator to pass
from `Y₄₄₃ ≅ M × 2` to the Monster group `M`. -/
def centralInvolutionRelator : Relator (Fin 12) :=
  .pow (a ⬝ b3 ⬝ c3 ⬝ d3 ⬝ b1 ⬝ c1 ⬝ b2) 9

/-- Ivanov's element `f₃₁₂` spelled out in the numbered alphabet. This is the unfolding lemma for
the sealed body. -/
theorem centralInvolutionRelator_def : centralInvolutionRelator =
    .pow (.gen 0 ⬝ .gen 9 ⬝ .gen 10 ⬝ .gen 11 ⬝ .gen 1 ⬝ .gen 2 ⬝ .gen 5) 9 := by
  rw [centralInvolutionRelator]

/-- The eighty relators of the Monster presentation: the `Y₄₄₃` Coxeter relations, followed by
the spider and central-involution relators. -/
def relatorList : List (Relator (Fin 12)) :=
  coxeterRelators coxeterMatrix ++ [spiderRelator, centralInvolutionRelator]

/-- The relator list decomposes into the `Y₄₄₃` Coxeter relations, the spider relator, and the
central-involution relator. This is the unfolding lemma for the sealed body. -/
theorem relatorList_def : relatorList =
    coxeterRelators coxeterMatrix ++ [spiderRelator, centralInvolutionRelator] := by
  rw [relatorList]

/-! ### The presentation row and its audit interface -/

/-- The `Y₄₄₃` finite presentation of the Fischer--Griess Monster group `M` on twelve involutions.

Ivanov proves that `Y₄₄₃` is `M × 2` and that quotienting by the central element `f₃₁₂` gives `M`.
No structural property of the resulting `PresentedGroup` is asserted here; this definition records
only the cited generators and complete relator data. -/
def presentation : GroupPresentation where
  generatorNames := ["a", "b1", "c1", "d1", "e1", "b2", "c2", "d2", "e2", "b3", "c3", "d3"]
  source := "J. N. Bray, Sporadic (Fischer-Griess) Monster group M = F1; A. A. Ivanov, Y-groups \
    via Transitive Extension, Journal of Algebra 218 (1999), 412-435"
  sourceLocator := "Bray's Y443 presentation at \
    https://webspace.maths.qmul.ac.uk/j.n.bray/web/Pres/Mnst.html; Ivanov, definition on p. 413, \
    Lemma 3.2 on p. 419, and Section 3.9 on pp. 430-431; doi:10.1006/jabr.1999.7882"
  generatorConvention := "Indices 0 through 11 are a,b1,c1,d1,e1,b2,c2,d2,e2,b3,c3,d3. Every \
    node is an involution, adjacent nodes have product of order dividing three, and nonadjacent \
    nodes commute. Products are read left to right. Ivanov writes f_ijk = \
    (a*b_i*c_i*d_i*b_j*c_j*b_k)^9."
  transcriptionNotes := "The Coxeter matrix expands the displayed Y443 diagram to 78 relators. \
    Append Bray's spider relator to present M x 2, then Ivanov's f_312 to quotient its central \
    factor and present M. The first 79 relators have the source's length 400; f_312 has length 63. \
    The independent FiniteSimpleGroups permutation construction does not cover M."
  expectedGeneratorCount := 12
  expectedRelatorCount := 80
  transcribed := relatorList

/-- The generator names recorded for the Monster presentation. -/
@[simp]
theorem presentation_generatorNames : presentation.generatorNames =
    ["a", "b1", "c1", "d1", "e1", "b2", "c2", "d2", "e2", "b3", "c3", "d3"] := by
  rw [presentation]

/-- The source recorded for the Monster presentation. -/
@[simp]
theorem presentation_source : presentation.source =
    "J. N. Bray, Sporadic (Fischer-Griess) Monster group M = F1; A. A. Ivanov, Y-groups via \
      Transitive Extension, Journal of Algebra 218 (1999), 412-435" := by
  rw [presentation]

/-- The exact source locator recorded for the Monster presentation. -/
@[simp]
theorem presentation_sourceLocator : presentation.sourceLocator =
    "Bray's Y443 presentation at \
      https://webspace.maths.qmul.ac.uk/j.n.bray/web/Pres/Mnst.html; Ivanov, definition on p. 413, \
      Lemma 3.2 on p. 419, and Section 3.9 on pp. 430-431; doi:10.1006/jabr.1999.7882" := by
  rw [presentation]

/-- The generator and Coxeter conventions recorded for the Monster presentation. -/
@[simp]
theorem presentation_generatorConvention : presentation.generatorConvention =
    "Indices 0 through 11 are a,b1,c1,d1,e1,b2,c2,d2,e2,b3,c3,d3. Every node is an involution, \
      adjacent nodes have product of order dividing three, and nonadjacent nodes commute. Products \
      are read left to right. Ivanov writes f_ijk = (a*b_i*c_i*d_i*b_j*c_j*b_k)^9." := by
  rw [presentation]

/-- The transcription notes recorded for the Monster presentation. -/
@[simp]
theorem presentation_transcriptionNotes : presentation.transcriptionNotes =
    "The Coxeter matrix expands the displayed Y443 diagram to 78 relators. Append Bray's spider \
      relator to present M x 2, then Ivanov's f_312 to quotient its central factor and present M. \
      The first 79 relators have the source's length 400; f_312 has length 63. The independent \
      FiniteSimpleGroups permutation construction does not cover M." := by
  rw [presentation]

/-- The expected generator count recorded for the Monster presentation. -/
@[simp]
theorem presentation_expectedGeneratorCount : presentation.expectedGeneratorCount = 12 := by
  rw [presentation]

/-- The expected relator count recorded for the Monster presentation. -/
@[simp]
theorem presentation_expectedRelatorCount : presentation.expectedRelatorCount = 80 := by
  rw [presentation]

/-- The relator expressions carried by the Monster presentation are exactly the transcribed
relator list, whose decomposition is `relatorList_def`. -/
@[simp]
theorem presentation_transcribed : presentation.transcribed = cast (by simp) relatorList := by
  rfl

/-- The compiled relators carried by the Monster presentation, with generator bounds forgotten. -/
theorem presentation_relatorLetters : presentation.relatorLetters =
    relatorList.map fun r => r.toWord.map fun letter => (letter.1.val, letter.2) := by
  rw [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def, presentation]
  simp only [List.map_map, Function.comp_def]
  rfl

/-! ### Decidable transcription checks -/

/-- The `Y₄₄₃` Coxeter diagram contributes seventy-eight relators. -/
theorem length_coxeterRelators : (coxeterRelators coxeterMatrix).length = 78 := by
  simp
  norm_num [Nat.choose]

/-- The full Monster presentation has eighty relators. -/
theorem length_relatorList : relatorList.length = 80 := by
  simp [relatorList_def]
  norm_num [Nat.choose]

/-- The generator and relator counts recorded for the Monster agree with the transcribed data. -/
theorem presentation_matchesMetadata : presentation.matchesMetadata := by
  rw [GroupPresentation.matchesMetadata_iff]
  refine ⟨?_, ?_⟩
  · rw [GroupPresentation.generatorCount, presentation_generatorNames,
      presentation_expectedGeneratorCount]
    rfl
  · rw [presentation_transcribed, presentation_expectedRelatorCount]
    exact length_relatorList

/-- The spider relator has ninety letters. -/
theorem length_spiderRelator : spiderRelator.toWord.length = 90 := by
  simp [spiderRelator]

/-- The seventy-nine relators presenting `M × 2` have the source's total length `400`. -/
theorem coxeterAndSpider_totalLength :
    ((coxeterRelators coxeterMatrix ++ [spiderRelator]).map
      fun r => r.toWord.length).sum = 400 := by
  rw [coxeterRelators_def, coxeterRelatorsOfList_def]
  rw [List.map_append, List.sum_append, List.map_map]
  simp_rw [Function.comp_def, length_toWord_coxeterRelator]
  simp only [coxeterMatrix_apply]
  rw [edges_def]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    length_spiderRelator]
  decide

/-- The central-involution relator `f₃₁₂` has sixty-three letters. -/
theorem length_centralInvolutionRelator : centralInvolutionRelator.toWord.length = 63 := by
  simp [centralInvolutionRelator]

/-- The compiled relators of the Monster presentation contain `463` signed letters in total. -/
theorem presentation_totalLength : presentation.totalLength = 463 := by
  have h : (relatorList.map fun r => r.toWord.length).sum = 463 := by
    rw [relatorList_def, ← List.singleton_append, ← List.append_assoc, List.map_append,
      List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [coxeterAndSpider_totalLength, length_centralInvolutionRelator]
  rw [← GroupPresentation.sum_map_length_relatorLetters, presentation_relatorLetters,
    List.map_map]
  simpa only [Function.comp_def, List.length_map] using h

/-- Every expression in the Monster relator list compiles to a cyclically reduced word. -/
theorem isCyclicallyReduced_toWord_of_mem_relatorList (r : Relator (Fin 12))
    (hr : r ∈ relatorList) : FreeGroup.IsCyclicallyReduced r.toWord := by
  rw [relatorList_def, List.mem_append] at hr
  rcases hr with hr | hr
  · rw [mem_coxeterRelators_iff] at hr
    obtain ⟨i, j, rfl⟩ := hr
    exact isCyclicallyReduced_toWord_coxeterRelator coxeterMatrix _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      simp [spiderRelator, centralInvolutionRelator, FreeGroup.IsCyclicallyReduced,
        FreeGroup.IsReduced]

/-- Every compiled Monster relator is cyclically reduced, so the letter counts above agree with
the usual presentation-length convention. -/
theorem presentation_relatorsCyclicallyReduced :
    presentation.relatorsCyclicallyReduced := by
  simpa [GroupPresentation.relatorsCyclicallyReduced_iff, GroupPresentation.relators_def,
    presentation] using isCyclicallyReduced_toWord_of_mem_relatorList

end TauCeti.Sporadic.Monster
