/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.GroupPresentation

/-!
# A transcribed presentation of the Thompson sporadic simple group

This file carries one row of the sporadic presentation manifest: the finite presentation of the
Thompson group `Th` on eight generators determined by Havas, Soicher and Wilson, transcribed into
the auditable format of `TauCeti.GroupPresentation`. The row records the generator names, the
source and a locator inside it, the source's generator and commutator conventions, the
transcription notes, and the generator and relator counts, together with the relator expressions
themselves.

The source is admissible in the sense the CFSG roadmap requires of a manifest row: it is a full
presentation of the abstract group, not a semi-presentation for recognizing generators inside an
already constructed group, and it is *proved* there to define `Th`. The proof is Theorem 3.1 of the
source, whose final step is a coset enumeration of the `143 127 000` cosets of the maximal subgroup
`³D₄(2):3`. Until that paper appeared, `Th` was the only sporadic simple group with no published
presentation for it or for its automorphism group.

## The relator groups

The source displays its relators in six numbered groups, and this file keeps that division, since
each group is what a reviewer compares against one displayed line of the source. The source also
records what the initial segments present, which is why the division is mathematically meaningful
rather than typographical.

| Group | Relators | The source's statement about it |
| --- | --- | --- |
| `relatorsOne` | 14 | with generators `a, b, c, d, e` these present `U₃(3):2` |
| `relatorsTwo` | 6 | adjoining `s`, groups (1) and (2) present `³D₄(2)` |
| `relatorsThree` | 7 | adjoining `t`, groups (1) to (3) present `³D₄(2):3` |
| `relatorsFour` | 7 | with generators `a, b, c, d, e, u`, groups (1) and (4) present `G₂(3):2` |
| `relatorsFive` | 1 | `u` inverts `t`, so `u` lies outside the subgroup presented so far |
| `relatorsSix` | 4 | the remaining relators, which cut the group down to `Th` |

## The transcription conventions

The source writes an equation `w₁ = w₂` for the relator `w₁ w₂⁻¹`, which is
`TauCeti.Relator.div`; it writes `w₁ ^ w₂` for `w₂⁻¹ w₁ w₂`, which is `TauCeti.Relator.conj`; and
it writes `[w₁, w₂]` for `w₁⁻¹ w₂⁻¹ w₁ w₂`, which is
`TauCeti.Sporadic.Thompson.sourceCommutator`, that is, Mathlib's commutator applied to the two
inverses. The three conventions are pinned by `TauCeti.Relator.toFreeGroup_div` (with Mathlib's
`div_eq_one`, which turns the relator `w₁ w₂⁻¹` back into the source's equation),
`TauCeti.Relator.toFreeGroup_conj` and `TauCeti.Relator.toFreeGroup_comm_inv_inv`, so no step
between the printed source and the free-group element used as a relation is left unstated.

## What is and is not claimed

Nothing here asserts that the presented group is nontrivial, finite or simple, that it has any
particular order, or that it is isomorphic to any other construction of the Thompson group. Those
are downstream statements that the CFSG roadmap deliberately does not ask for; what this file
supplies is a named group built from explicit, cited relator data.

The checks that are proved are transcription arithmetic. `TauCeti.Sporadic.Thompson.presentation`
has eight generators and thirty-nine relators, split as `14 + 6 + 7 + 7 + 1 + 4` over the source's
six displayed groups. Beyond those counts, the source states a figure that the transcribed data
reproduces independently: it observes that its presentation gives a coset table with eleven columns,
which is the number of involutory generators plus twice the number of the others.
`TauCeti.Sporadic.Thompson.cosetTableColumns` recomputes that figure from the relator list, reading
the involutory generators off it as those carrying an explicit square relator, and
`TauCeti.Sporadic.Thompson.generatorsWithSquareRelator_eq` identifies those five as `a, b, c, d, e`.
A transposed or dropped power relator would show up in one of these.

Correctness of the transcription beyond that is a review obligation, exactly as the roadmap
describes: a reviewer reads the six lists below against Theorem 3.1 of the source. Note that the
source states that some of its relators are redundant, kept for clarity or to help the enumeration,
so the list is deliberately not minimal.

## Main definitions

* `TauCeti.Sporadic.Thompson.genA` to `TauCeti.Sporadic.Thompson.genU`: the source's eight letters
  as relator expressions.
* `TauCeti.Sporadic.Thompson.sourceCommutator`: the source's commutator convention.
* `TauCeti.Sporadic.Thompson.relatorsOne` to `TauCeti.Sporadic.Thompson.relatorsSix`: the six
  displayed relator groups, and `TauCeti.Sporadic.Thompson.relatorList`, their concatenation.
* `TauCeti.Sporadic.Thompson.presentation`: the transcribed row.
* `TauCeti.Sporadic.Thompson.generatorsWithSquareRelator`: the generators carrying an explicit
  square relator in the transcribed data.

## References

This fills one of the twenty-six rows owed by milestone S1 of
`TauCetiRoadmap/CFSGStatement/README.md`, which asks for the complete relator words of an
admissible source for each sporadic name. The source is

* G. Havas, L. H. Soicher and R. A. Wilson, *A presentation for the Thompson sporadic simple
  group*, in *Groups and Computation III* (Columbus, OH, 1999), Ohio State University Mathematical
  Research Institute Publications **8**, de Gruyter, Berlin, 2001, 193--200.

Theorem 3.1 there states the presentation as relators (1) to (6) and proves that the group it
presents is `Th`.
-/

public section

namespace TauCeti.Sporadic.Thompson

/-! ### The source's alphabet

The source uses eight generators `a, b, c, d, e, s, t, u`, in that order, and the relator index
`Fin 8` follows it: index `0` is `a` and index `7` is `u`. -/

/-- The generator printed `a` by the source, an involution centralizing `c, d, e, s, t, u`. -/
abbrev genA : Relator (Fin 8) := .gen 0

/-- The generator printed `b` by the source. -/
abbrev genB : Relator (Fin 8) := .gen 1

/-- The generator printed `c` by the source. -/
abbrev genC : Relator (Fin 8) := .gen 2

/-- The generator printed `d` by the source. -/
abbrev genD : Relator (Fin 8) := .gen 3

/-- The generator printed `e` by the source, an outer involution of `U₃(3)`. -/
abbrev genE : Relator (Fin 8) := .gen 4

/-- The generator printed `s` by the source, of order seven. -/
abbrev genS : Relator (Fin 8) := .gen 5

/-- The generator printed `t` by the source, of order three; it is a `3C`-element of `Th`. -/
abbrev genT : Relator (Fin 8) := .gen 6

/-- The generator printed `u` by the source; it inverts `t` and so lies outside `³D₄(2):3`. -/
abbrev genU : Relator (Fin 8) := .gen 7

/-- The source's commutator `[r, s] = r⁻¹ s⁻¹ r s`.

Mathlib's bracket, carried by `TauCeti.Relator.comm`, is `⁅r, s⁆ = r s r⁻¹ s⁻¹`, so the source's
convention is Mathlib's applied to the two inverses; `TauCeti.Relator.toFreeGroup_comm_inv_inv`
proves that this denotes `r⁻¹ s⁻¹ r s` in the free group. -/
abbrev sourceCommutator (r s : Relator (Fin 8)) : Relator (Fin 8) := .comm (.inv r) (.inv s)

@[inherit_doc Relator.mul]
local infixl:70 " ⬝ " => Relator.mul

/-! ### The six relator groups of Theorem 3.1 -/

/-- Relators (1) of the source: `a², b², c², d², e², (ab)³, (ae)², (bc)³, (bd)², (be)²,
a = (cd)⁴, (ce)², (de)³, (bcde)⁸`.

On the generators `a, b, c, d, e` alone these present `U₃(3):2`, a group of order `12 096`; the
source records this as essentially the presentation of `U₃(3):2` in Soicher's earlier paper. -/
@[expose]
def relatorsOne : List (Relator (Fin 8)) :=
  [genA.pow 2,
    genB.pow 2,
    genC.pow 2,
    genD.pow 2,
    genE.pow 2,
    (genA ⬝ genB).pow 3,
    (genA ⬝ genE).pow 2,
    (genB ⬝ genC).pow 3,
    (genB ⬝ genD).pow 2,
    (genB ⬝ genE).pow 2,
    genA.div ((genC ⬝ genD).pow 4),
    (genC ⬝ genE).pow 2,
    (genD ⬝ genE).pow 3,
    (genB ⬝ genC ⬝ genD ⬝ genE).pow 8]

/-- Relators (2) of the source: `s⁷, [s, a], [s, b], [s, c], (sd)², [e, s] = e ^ (s³)`.

Together with relators (1), on the generators `a, b, c, d, e, s`, these present `³D₄(2)`. -/
@[expose]
def relatorsTwo : List (Relator (Fin 8)) :=
  [genS.pow 7,
    sourceCommutator genS genA,
    sourceCommutator genS genB,
    sourceCommutator genS genC,
    (genS ⬝ genD).pow 2,
    (sourceCommutator genE genS).div (genE.conj (genS.pow 3))]

/-- Relators (3) of the source: `t³, [t, a], [t, b], [t, c], [t, d], [t, e], s ^ t = s²`.

Together with relators (1) and (2) these present `³D₄(2):3`, the maximal subgroup of `Th` over
which the final coset enumeration is run. -/
@[expose]
def relatorsThree : List (Relator (Fin 8)) :=
  [genT.pow 3,
    sourceCommutator genT genA,
    sourceCommutator genT genB,
    sourceCommutator genT genC,
    sourceCommutator genT genD,
    sourceCommutator genT genE,
    (genS.conj genT).div (genS.pow 2)]

/-- Relators (4) of the source: `u² = ac, [u, a], [u, c], [u, e], (d e d ^ u)²,
[u, (ac) ^ b] = e, [u ^ d, (ac) ^ b] = u e (ac) ^ b u ^ d e c`.

Together with relators (1), on the generators `a, b, c, d, e, u`, these present `G₂(3):2`. The last
relator is the one the source singles out as the crucial one, found with GAP's
`PresentationViaCosetTable`. -/
@[expose]
def relatorsFour : List (Relator (Fin 8)) :=
  [(genU.pow 2).div (genA ⬝ genC),
    sourceCommutator genU genA,
    sourceCommutator genU genC,
    sourceCommutator genU genE,
    (genD ⬝ genE ⬝ genD.conj genU).pow 2,
    (sourceCommutator genU ((genA ⬝ genC).conj genB)).div genE,
    (sourceCommutator (genU.conj genD) ((genA ⬝ genC).conj genB)).div
      (genU ⬝ genE ⬝ (genA ⬝ genC).conj genB ⬝ genU.conj genD ⬝ genE ⬝ genC)]

/-- Relator (5) of the source: `t ^ u = t⁻¹`.

This is the relator from which the source concludes that `u` lies outside the subgroup `³D₄(2):3`
presented by relators (1) to (3), so that the eight generators generate the whole of `Th`. -/
@[expose]
def relatorsFive : List (Relator (Fin 8)) :=
  [(genT.conj genU).div (Relator.inv genT)]

/-- Relators (6) of the source: `[e, u ^ (s²)]`, the chain `ac = (us)³ = [u, s]⁴` read as its two
equations, and `(d u ^ (s²))⁴ = a c c ^ d c ^ (d e s⁻¹) c ^ (d e s²)`.

The source obtained these last relators from explicit `248`-dimensional matrices over `GF(2)`
generating `Th` and satisfying relators (1) to (5). -/
@[expose]
def relatorsSix : List (Relator (Fin 8)) :=
  [sourceCommutator genE (genU.conj (genS.pow 2)),
    (genA ⬝ genC).div ((genU ⬝ genS).pow 3),
    ((genU ⬝ genS).pow 3).div ((sourceCommutator genU genS).pow 4),
    ((genD ⬝ genU.conj (genS.pow 2)).pow 4).div
      (genA ⬝ genC ⬝ genC.conj genD ⬝ genC.conj (genD ⬝ genE ⬝ Relator.inv genS) ⬝
        genC.conj (genD ⬝ genE ⬝ genS.pow 2))]

/-- The six displayed relator groups of Theorem 3.1, concatenated in the printed order.

This is the list carried by `TauCeti.Sporadic.Thompson.presentation`. It is named separately
because the field of that record has index type `Fin presentation.generatorNames.length`, and the
checks below are about the list as written, over `Fin 8`. -/
@[expose]
def relatorList : List (Relator (Fin 8)) :=
  relatorsOne ++ relatorsTwo ++ relatorsThree ++ relatorsFour ++ relatorsFive ++ relatorsSix

/-! ### The transcribed row -/

/-- The finite presentation of the Thompson sporadic simple group `Th` given by Theorem 3.1 of
Havas--Soicher--Wilson, with the source and transcription metadata that make the row auditable.

The relators are the six displayed groups of that theorem, concatenated in the printed order. -/
@[expose]
def presentation : GroupPresentation where
  generatorNames := ["a", "b", "c", "d", "e", "s", "t", "u"]
  source := "G. Havas, L. H. Soicher and R. A. Wilson, A presentation for the Thompson sporadic \
    simple group, in Groups and Computation III (Columbus, OH, 1999), Ohio State University \
    Mathematical Research Institute Publications 8, de Gruyter, Berlin, 2001, 193-200"
  sourceLocator := "Theorem 3.1, relators (1) to (6), Section 3 (pp. 193-194)"
  generatorConvention := "The generators a, b, c, d, e, s, t, u of the source, in that order, so \
    index 0 is a and index 7 is u. The source writes w1 = w2 for the relator w1 * w2⁻¹, w1 ^ w2 \
    for w2⁻¹ * w1 * w2, and [w1, w2] for w1⁻¹ * w2⁻¹ * w1 * w2."
  transcriptionNotes := "The source proves that these relators present Th (Theorem 3.1), the final \
    step being a coset enumeration of the 143127000 cosets of the maximal subgroup ³D₄(2):3 \
    generated by a, b, c, d, e, s, t. The source displays its relators in six numbered groups and \
    prints no total, so the expected relator count is the sum 14 + 6 + 7 + 7 + 1 + 4 of the \
    displayed groups; the chain ac = (us)³ = [u, s]⁴ in group (6) is counted as its two equations. \
    The source states that some of its relators are redundant, kept for clarity or to aid the \
    coset enumeration, so the list is deliberately not minimal."
  expectedGeneratorCount := 8
  expectedRelatorCount := 39
  transcribed := relatorList

/-! ### The transcription checks -/

/-- Relators (1) of the source are fourteen relators. -/
theorem length_relatorsOne : relatorsOne.length = 14 := rfl

/-- Relators (2) of the source are six relators. -/
theorem length_relatorsTwo : relatorsTwo.length = 6 := rfl

/-- Relators (3) of the source are seven relators. -/
theorem length_relatorsThree : relatorsThree.length = 7 := rfl

/-- Relators (4) of the source are seven relators. -/
theorem length_relatorsFour : relatorsFour.length = 7 := rfl

/-- Relator (5) of the source is a single relator. -/
theorem length_relatorsFive : relatorsFive.length = 1 := rfl

/-- Relators (6) of the source are four relators, the chain `ac = (us)³ = [u, s]⁴` contributing
two of them. -/
theorem length_relatorsSix : relatorsSix.length = 4 := rfl

/-- The transcribed presentation has thirty-nine relators. -/
theorem length_relatorList : relatorList.length = 39 := rfl

/-- **The recorded generator and relator counts agree with the transcribed data.** -/
theorem matchesMetadata_presentation : presentation.matchesMetadata :=
  (GroupPresentation.matchesMetadata_iff presentation).mpr ⟨rfl, rfl⟩

/-- The indices `i` for which the relator `gᵢ²` occurs literally in the transcribed list.

This is a syntactic test on the data as written, not a statement about element orders in the
presented group: it neither proves that such a generator has order exactly two rather than one, nor
detects a generator whose square is forced by the other relators. What it is for is the column count
below, which the source computes from exactly this syntactic reading of its own displayed
relators. -/
@[expose]
def generatorsWithSquareRelator : List (Fin 8) :=
  relatorList.filterMap fun r =>
    match r with
    | .pow (.gen i) 2 => some i
    | _ => none

/-- **The generators carrying a square relator are exactly `a`, `b`, `c`, `d` and `e`**, the first
five of the eight, which are the source's involutory generators. A power relator dropped from, or
transposed within, relators (1) would change this list. -/
theorem generatorsWithSquareRelator_eq : generatorsWithSquareRelator = [0, 1, 2, 3, 4] := rfl

/-- **The source's column-count formula evaluates to eleven on the transcribed relators**, the
figure the source records for its enumeration: one column for each generator carrying a square
relator, its involutory generators, and two for each of the others.

Like `TauCeti.Sporadic.Thompson.generatorsWithSquareRelator`, this is arithmetic on the data as
written; it asserts nothing about an actual coset table, nor that enumerating this presentation
terminates. Its value is that it checks the transcription against a published number that the counts
of `TauCeti.Sporadic.Thompson.matchesMetadata_presentation` do not see. -/
theorem cosetTableColumns :
    generatorsWithSquareRelator.length +
      2 * (presentation.generatorCount - generatorsWithSquareRelator.length) = 11 := rfl

end TauCeti.Sporadic.Thompson
