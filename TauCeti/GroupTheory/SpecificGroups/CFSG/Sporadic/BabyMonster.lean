/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.GroupTheory.Presentation.Coxeter

/-!
# A transcribed presentation of the Baby Monster

This file carries the `B` row of the sporadic presentation data required by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`. It records the `Y₄₃₃` presentation of the Baby Monster
as a `TauCeti.GroupPresentation`, together with the diagram it expands, the exact source, the
generator convention, the transcription notes, and decidable checks on the transcribed data.

The eleven involutory generators are the nodes of a `Y`-shaped Coxeter diagram: a chain of eight
nodes with a further arm of three nodes attached to its fifth node,

```text
t₁ -- t₂ -- t₃ -- t₄ -- t₅ -- t₆ -- t₇ -- t₈
                        |
                        t₉ -- t₁₀ -- t₁₁
```

so that the branch node `t₅` carries three arms, of lengths four, three and three; this is what the
name `Y₄₃₃` records. The Coxeter relations contribute `11` square relators and one relator
`(tᵢ tⱼ) ^ m` for each of the `55` unordered pairs of distinct nodes, with `m = 3` on the ten edges
and `m = 2` off them. Adjoining the spider relation

```text
(t₅ t₄ t₃ t₅ t₆ t₇ t₅ t₉ t₁₀) ^ 10 = 1
```

presents `2 × 2·B`, and adjoining the two further relations

```text
(t₅ t₄ t₃ t₆ t₇ t₈ t₉) ^ 9 = 1,      (t₅ t₄ t₃ t₆ t₉ t₁₀ t₁₁) ^ 9 = 1
```

presents the Baby Monster itself. The `69` relators are therefore `66 + 1 + 2`.

The source is admissible in the sense the roadmap requires: it presents the abstract group rather
than recognizing generators inside a group constructed elsewhere. The presentation was conjectured
in the ATLAS of Finite Groups and proved by Ivanov, subject to the Monster having no proper double
cover; that hypothesis is Griess's determination of the Schur multiplier of the Monster. The row
below records that chain of attributions rather than reproving any part of it.

Nothing here asserts that the presented group is nontrivial, finite or simple, that it has any
particular order, or that it is isomorphic to any other construction of the Baby Monster. The
roadmap's independent permutation-group cross-check does not cover `B`, whose smallest faithful
permutation representation has degree `13 571 955 000`, so for this row an independent
source-to-Lean read-through remains the whole of the S1 review obligation.

## Main definitions

* `TauCeti.Sporadic.BabyMonster.arms` and `TauCeti.Sporadic.BabyMonster.edges`: the three arms of
  the `Y₄₃₃` diagram and the edges they contribute.
* `TauCeti.Sporadic.BabyMonster.coxeterMatrix`: the Coxeter matrix of the numbered diagram.
* `TauCeti.Sporadic.BabyMonster.spiderRelator`: the spider relation of the source.
* `TauCeti.Sporadic.BabyMonster.extraRelatorOne` and
  `TauCeti.Sporadic.BabyMonster.extraRelatorTwo`: the two further relations the source adjoins to
  pass from `2 × 2·B` to `B`.
* `TauCeti.Sporadic.BabyMonster.presentation`: the transcribed row.

## Main results

* `TauCeti.Sporadic.BabyMonster.map_length_neighbors`: the degree sequence of the transcribed
  diagram, a check consistent with the published `Y`-shape; `edges_eq` and `map_length_arms` pin
  the shape itself.
* `TauCeti.Sporadic.BabyMonster.length_relatorList` and
  `TauCeti.Sporadic.BabyMonster.matchesMetadata_presentation`: the transcription count checks.
* `TauCeti.Sporadic.BabyMonster.mulEquivPresentedGroupCoxeterAppend`: the row presents the Coxeter
  group of the diagram cut down by the three adjoined relations, which is the shape of the source's
  statement.

## References

* T. Breuer, K. Magaard, and R. A. Wilson, *Verification of the ordinary character table of the
  Baby Monster*, Journal of Algebra **561** (2020), 111--130,
  <https://doi.org/10.1016/j.jalgebra.2019.06.047>, also <https://arxiv.org/abs/1902.07758>.
  Section 3.1 states the `Y₄₃₃` presentation used here.
* A. A. Ivanov, *Presenting the Baby Monster*, Journal of Algebra **163** (1994), 88--108,
  <https://doi.org/10.1006/jabr.1994.1005>, which proves that the diagram with the spider relation
  presents `2 × 2·B`. This is the work Breuer--Magaard--Wilson cite for the proof.
* R. L. Griess, Jr., *The Schur multipliers of the known finite simple groups, III*, in Proceedings
  of the Rutgers Group Theory Year, 1983--1984, Cambridge University Press, 1985, 69--80, which is
  the work Breuer--Magaard--Wilson cite for the Schur multiplier of the Monster.
* J. H. Conway, R. T. Curtis, S. P. Norton, R. A. Parker, and R. A. Wilson, *Atlas of Finite
  Groups*, Clarendon Press, Oxford, 1985, where the presentation was conjectured.
-/

public section

namespace TauCeti.Sporadic.BabyMonster

/-! ### The numbered `Y₄₃₃` diagram

The source numbers its involutions `t₁` to `t₁₁`; the relator index `Fin 11` follows that
numbering with the customary offset, so `tᵢ` is index `i - 1`. -/

/-- The branch node of the diagram, the source's `t₅`. -/
def branchNode : Fin 11 := 4

/-- The branch node is index four, corresponding to the source's `t₅`. -/
@[simp]
theorem branchNode_def : branchNode = 4 := (rfl)

/-- The three arms of the diagram, each listed outwards from the branch node: `t₄ t₃ t₂ t₁`, then
`t₆ t₇ t₈`, then `t₉ t₁₀ t₁₁`. -/
def arms : List (List (Fin 11)) := [[3, 2, 1, 0], [5, 6, 7], [8, 9, 10]]

/-- The three arms, spelled out in the numbered alphabet. -/
@[simp]
theorem arms_def : arms = [[3, 2, 1, 0], [5, 6, 7], [8, 9, 10]] := (rfl)

/-- **The three arms have lengths four, three and three**, which is what the name `Y₄₃₃`
records. -/
theorem map_length_arms : arms.map List.length = [4, 3, 3] := by decide

/-- The branch node and the arms use each of the eleven nodes at most once. -/
theorem nodup_branchNode_cons_flatten_arms : (branchNode :: arms.flatten).Nodup := by decide

/-- The branch node and the arms use every node, so with
`TauCeti.Sporadic.BabyMonster.nodup_branchNode_cons_flatten_arms` each generator of the
presentation occupies exactly one position of the diagram. -/
theorem mem_branchNode_cons_flatten_arms (i : Fin 11) : i ∈ branchNode :: arms.flatten := by
  revert i; decide

/-- The edges of the diagram: each arm contributes the edge joining it to the branch node and an
edge between each pair of nodes consecutive along it. Pairs are oriented outwards; the Coxeter
matrix below reads them symmetrically. -/
def edges : List (Fin 11 × Fin 11) := arms.flatMap fun arm => (branchNode :: arm).zip arm

/-- The ten edges of the numbered diagram, written out.

Read with the offset `tᵢ ↦ i - 1`, these are the source's ten adjacent pairs
`(1,2), (2,3), (3,4), (4,5), (5,6), (6,7), (7,8), (5,9), (9,10), (10,11)`. The first arm's four
edges appear in reverse order and reverse orientation because that arm is listed outwards from the
branch node. -/
@[simp]
theorem edges_eq :
    edges = [(4, 3), (3, 2), (2, 1), (1, 0), (4, 5), (5, 6), (6, 7), (4, 8), (8, 9), (9, 10)] := by
  decide

/-- The diagram has ten edges. -/
theorem length_edges : edges.length = 10 := by decide

/-- The Coxeter matrix of the numbered `Y₄₃₃` diagram, the simply laced matrix of its edge list: a
node with itself has entry one, an edge has entry three, and every other pair of nodes has entry
two. -/
def coxeterMatrix : CoxeterMatrix (Fin 11) := coxeterMatrixOfEdges edges

/-- Evaluation of the Coxeter matrix directly from the edge list. -/
@[simp]
theorem coxeterMatrix_apply (i j : Fin 11) :
    coxeterMatrix i j = if i = j then 1 else if (i, j) ∈ edges ∨ (j, i) ∈ edges then 3 else 2 := by
  rw [coxeterMatrix, coxeterMatrixOfEdges_apply]

/-- The nodes joined to a given node by an edge, read off the Coxeter matrix rather than off the
edge list, so that a comparison with the diagram sees the matrix that the relators are built
from. -/
def neighbors (i : Fin 11) : List (Fin 11) :=
  (List.finRange 11).filter fun j => coxeterMatrix i j = 3

/-- Membership in `neighbors i` is characterized by the corresponding Coxeter-matrix entry. -/
@[simp]
theorem mem_neighbors_iff (i j : Fin 11) : j ∈ neighbors i ↔ coxeterMatrix i j = 3 := by
  simp [neighbors]

/-- The branch node is joined to the first node of each of the three arms. -/
theorem neighbors_branchNode : neighbors branchNode = [3, 5, 8] := by decide

/-- **The degree sequence of the transcribed diagram.** Node `t₅`, that is index `4`, has three
neighbors; the three arm ends `t₁`, `t₈` and `t₁₁`, that is indices `0`, `7` and `10`, have one
each; and the remaining seven nodes have two each. Thus the matrix that the relators are built from
has a degree sequence consistent with the `Y`-shape. The shape itself is pinned by `edges_eq`
together with `map_length_arms` and `nodup_branchNode_cons_flatten_arms`, from which the edges are
built. -/
theorem map_length_neighbors :
    (List.finRange 11).map (fun i => (neighbors i).length) =
      [1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 1] := by
  decide

/-! ### The three adjoined relations -/

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

private abbrev t1 : Relator (Fin 11) := .gen 0
private abbrev t2 : Relator (Fin 11) := .gen 1
private abbrev t3 : Relator (Fin 11) := .gen 2
private abbrev t4 : Relator (Fin 11) := .gen 3
private abbrev t5 : Relator (Fin 11) := .gen 4
private abbrev t6 : Relator (Fin 11) := .gen 5
private abbrev t7 : Relator (Fin 11) := .gen 6
private abbrev t8 : Relator (Fin 11) := .gen 7
private abbrev t9 : Relator (Fin 11) := .gen 8
private abbrev t10 : Relator (Fin 11) := .gen 9
private abbrev t11 : Relator (Fin 11) := .gen 10

/-- The spider relator `(t₅ t₄ t₃ t₅ t₆ t₇ t₅ t₉ t₁₀) ^ 10` of the source. Adjoining it to the
Coxeter relations of the diagram gives a presentation of `2 × 2·B`. -/
def spiderRelator : Relator (Fin 11) :=
  .pow (t5 ⬝ t4 ⬝ t3 ⬝ t5 ⬝ t6 ⬝ t7 ⬝ t5 ⬝ t9 ⬝ t10) 10

/-- The spider relator spelled out in the numbered alphabet. -/
@[simp]
theorem spiderRelator_eq :
    spiderRelator =
      .pow (.gen 4 ⬝ .gen 3 ⬝ .gen 2 ⬝ .gen 4 ⬝ .gen 5 ⬝ .gen 6 ⬝ .gen 4 ⬝ .gen 8 ⬝ .gen 9) 10 := by
  rw [spiderRelator]

/-- The first of the two relators `(t₅ t₄ t₃ t₆ t₇ t₈ t₉) ^ 9` that the source adjoins to the
spider relation to pass from `2 × 2·B` to `B`. -/
def extraRelatorOne : Relator (Fin 11) := .pow (t5 ⬝ t4 ⬝ t3 ⬝ t6 ⬝ t7 ⬝ t8 ⬝ t9) 9

/-- The first adjoined relator spelled out in the numbered alphabet. -/
@[simp]
theorem extraRelatorOne_eq :
    extraRelatorOne =
      .pow (.gen 4 ⬝ .gen 3 ⬝ .gen 2 ⬝ .gen 5 ⬝ .gen 6 ⬝ .gen 7 ⬝ .gen 8) 9 := by
  rw [extraRelatorOne]

/-- The second of the two relators `(t₅ t₄ t₃ t₆ t₉ t₁₀ t₁₁) ^ 9` that the source adjoins to the
spider relation to pass from `2 × 2·B` to `B`. -/
def extraRelatorTwo : Relator (Fin 11) := .pow (t5 ⬝ t4 ⬝ t3 ⬝ t6 ⬝ t9 ⬝ t10 ⬝ t11) 9

/-- The second adjoined relator spelled out in the numbered alphabet. -/
@[simp]
theorem extraRelatorTwo_eq :
    extraRelatorTwo =
      .pow (.gen 4 ⬝ .gen 3 ⬝ .gen 2 ⬝ .gen 5 ⬝ .gen 8 ⬝ .gen 9 ⬝ .gen 10) 9 := by
  rw [extraRelatorTwo]

/-- The three relators the source adjoins to the Coxeter relations of the diagram, in the order it
introduces them. -/
def adjoinedRelators : List (Relator (Fin 11)) :=
  [spiderRelator, extraRelatorOne, extraRelatorTwo]

/-- The adjoined-relator list, in source order. -/
@[simp]
theorem adjoinedRelators_def :
    adjoinedRelators = [spiderRelator, extraRelatorOne, extraRelatorTwo] := (rfl)

/-- The sixty-nine relators of the presentation: the Coxeter relations of the `Y₄₃₃` diagram
followed by the spider relator and the two further relators. -/
def relatorList : List (Relator (Fin 11)) := coxeterRelators coxeterMatrix ++ adjoinedRelators

/-- The relator list is the Coxeter list followed by the three adjoined relators. -/
@[simp]
theorem relatorList_def :
    relatorList = coxeterRelators coxeterMatrix ++ adjoinedRelators := (rfl)

/-! ### The transcribed row and its checks -/

/-- The `Y₄₃₃` finite presentation of the Baby Monster `B` on eleven involutions, with the source
and transcription metadata that make the row auditable.

Ivanov proves that the diagram with the spider relation presents `2 × 2·B`; the source adjoins two
further relations to present `B`. No structural property of the resulting `PresentedGroup` is
asserted here: this definition records only the cited generators and the complete relator data. -/
@[expose]
def presentation : GroupPresentation where
  generatorNames := ["t1", "t2", "t3", "t4", "t5", "t6", "t7", "t8", "t9", "t10", "t11"]
  source := "T. Breuer, K. Magaard, and R. A. Wilson, Verification of the ordinary character \
    table of the Baby Monster, Journal of Algebra 561 (2020), 111-130; A. A. Ivanov, Presenting \
    the Baby Monster, Journal of Algebra 163 (1994), 88-108"
  sourceLocator := "Breuer-Magaard-Wilson, Section 3.1, doi:10.1016/j.jalgebra.2019.06.047, \
    also arXiv:1902.07758v2; Ivanov, doi:10.1006/jabr.1994.1005. The presentation was conjectured \
    in the Atlas of Finite Groups (Conway, Curtis, Norton, Parker, Wilson, 1985) and proved by \
    Ivanov, subject to the Monster having no proper double cover, which is Griess's computation of \
    the Schur multiplier of the Monster (The Schur multipliers of the known finite simple groups, \
    III, Proceedings of the Rutgers Group Theory Year 1983-1984, Cambridge University Press, 1985, \
    69-80)."
  generatorConvention := "Indices 0 through 10 are the source's involutions t1 through t11, so \
    t_i is index i-1. The Coxeter diagram is the chain t1-t2-t3-t4-t5-t6-t7-t8 together with the \
    arm t5-t9-t10-t11, so t5 is the branch node and the three arms have lengths 4, 3 and 3. \
    Products are read left to right."
  transcriptionNotes := "The Coxeter matrix expands the diagram into 66 relators: eleven squares \
    t_i^2, one relator (t_i t_j)^3 for each of the ten edges, and one relator (t_i t_j)^2 for each \
    of the remaining 45 unordered pairs of distinct nodes. Appended to them are the source's \
    spider relation, which presents 2 x 2.B, and then its two further relations, which present B. \
    The source displays its relations by family rather than as a numbered list and records no \
    total length, so the expected relator count is the sum 11 + 55 + 1 + 2 over those families. \
    The independent FiniteSimpleGroups permutation construction does not cover B, so a \
    source-to-Lean read-through remains an S1 review obligation for this row."
  expectedGeneratorCount := 11
  expectedRelatorCount := 69
  transcribed := relatorList

/-- The relators of the row are the Coxeter relations of the diagram followed by the three
adjoined relators. The record's body is exposed, so its metadata fields are read off it directly;
this equation is the one field projection that is not read off it, because
`TauCeti.Sporadic.BabyMonster.relatorList` is sealed. -/
@[simp]
theorem presentation_transcribed : presentation.transcribed = relatorList := rfl

/-- **The relators of the row are the Coxeter relators of the `Y₄₃₃` diagram followed by the three
adjoined relators.** This is the form in which the source states the presentation, and the
hypothesis that `TauCeti.Sporadic.BabyMonster.mulEquivPresentedGroupCoxeterAppend` below
consumes. -/
theorem presentation_transcribed_append :
    presentation.transcribed = coxeterRelators coxeterMatrix ++ adjoinedRelators := by
  rw [presentation_transcribed, relatorList_def]

/-- **The transcribed presentation has sixty-nine relators**, the `(11 + 1).choose 2 = 66` Coxeter
relators of a diagram on eleven nodes together with the three adjoined relators. -/
theorem length_relatorList : relatorList.length = 69 := by
  rw [relatorList_def, List.length_append, length_coxeterRelators, adjoinedRelators_def]
  decide

/-- **The recorded generator and relator counts agree with the transcribed data.** -/
theorem matchesMetadata_presentation : presentation.matchesMetadata :=
  (GroupPresentation.matchesMetadata_iff presentation).mpr ⟨by decide, length_relatorList⟩

/-- **The row presents the Coxeter group of the `Y₄₃₃` diagram cut down by the three adjoined
relations**, which is the shape in which the source states the presentation: the Coxeter relations
of the diagram, the spider relation, and the two further relations.

This is an identification of the presented group with a quotient built from Mathlib's
`CoxeterMatrix.relationsSet`; it asserts nothing about the order or the structure of either
side. -/
def mulEquivPresentedGroupCoxeterAppend :
    presentation.Group ≃*
      PresentedGroup (coxeterMatrix.relationsSet ∪ Relator.relatorSet adjoinedRelators) :=
  presentation.mulEquivPresentedGroupCoxeterAppend coxeterMatrix adjoinedRelators
    presentation_transcribed_append

/-- The Coxeter equivalence sends each canonical generator to the corresponding canonical
generator. -/
@[simp]
theorem mulEquivPresentedGroupCoxeterAppend_apply_of (i : Fin presentation.generatorCount) :
    mulEquivPresentedGroupCoxeterAppend (PresentedGroup.of i) = PresentedGroup.of i :=
  GroupPresentation.mulEquivPresentedGroupCoxeterAppend_apply_of _ _ _
    presentation_transcribed_append i

end TauCeti.Sporadic.BabyMonster
