/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ExactChecker
public import TauCeti.RingTheory.Cyclotomic.Conjugation

/-!
# An exact checker for cyclotomic character tables

The general stage of the Burnside--Dixon--Schneider algorithm returns central-character and
ordinary character tables in the computable coefficient-vector ring `TauCeti.Cyclotomic e`.
This file specializes the generic exact character-table certificate to that ring.  All certificate
conditions, including Hermitian row orthogonality, are decidable computations on integer
coefficient vectors.

Only after the exact certificate has been checked is the table sent to `ℂ` through the
distinguished cyclotomic embedding.  Exact conjugation commutes with that embedding, so the generic
soundness bridge proves that the embedded table satisfies `TauCeti.IsCharacterTableSpec`.

## Main definitions

* `TauCeti.ClassData.IsCyclotomicCharacterTableSpec`: the exact numbered cyclotomic certificate.
* `TauCeti.ClassData.cyclotomicCharacterTableChecker`: its executable Boolean checker.
* `TauCeti.ClassData.complexTableOfCyclotomic`: embed and reindex an exact cyclotomic table.

## Main result

* `TauCeti.ClassData.IsCyclotomicCharacterTableSpec.isCharacterTableSpec`: a successful exact
  cyclotomic certificate identifies the embedded output as the character table up to row order.

This is the exact-checker step in Layer 6, “The assembled solver”, of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).
-/

public section

namespace TauCeti

namespace ClassData

universe u

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable (d : ClassData G)
variable (e : ℕ) [NeZero e]

/-- An exact character-table certificate specialized to `e`-th cyclotomic integer entries. -/
abbrev IsCyclotomicCharacterTableSpec
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e))
    (degree : Fin d.numClasses → ℕ) : Prop :=
  d.IsExactCharacterTableSpec star omega table degree

/-- The executable Boolean checker for an exact cyclotomic central-character table, ordinary
table, and their character degrees. -/
def cyclotomicCharacterTableChecker
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e))
    (degree : Fin d.numClasses → ℕ) : Bool :=
  d.exactCharacterTableChecker star omega table degree

omit [NeZero e] in
/-- The Boolean cyclotomic checker succeeds precisely when the exact cyclotomic certificate
holds. -/
@[simp]
theorem cyclotomicCharacterTableChecker_eq_true_iff
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e))
    (degree : Fin d.numClasses → ℕ) :
    d.cyclotomicCharacterTableChecker e omega table degree = true ↔
      d.IsCyclotomicCharacterTableSpec e omega table degree :=
  d.exactCharacterTableChecker_eq_true_iff star omega table degree

/-- Embed a numbered exact cyclotomic table into `ℂ`, reindexing its rows by the number of
conjugacy classes and its columns by the conjugacy classes themselves. -/
noncomputable def complexTableOfCyclotomic
    (table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e)) :
    Matrix (Fin (Nat.card (ConjClasses G))) (ConjClasses G) ℂ :=
  d.reindexTableOfMap Cyclotomic.complexEmbedding table

/-- The embedded and reindexed cyclotomic table evaluated at arbitrary row and column indices. -/
@[simp]
theorem complexTableOfCyclotomic_apply
    (table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e))
    (i : Fin (Nat.card (ConjClasses G))) (C : ConjClasses G) :
    d.complexTableOfCyclotomic e table i C =
      Cyclotomic.complexEmbedding
        (table ((finCongr d.numClasses_eq_card_conjClasses).symm i)
          (d.equivConjClasses.symm C)) :=
  d.reindexTableOfMap_apply Cyclotomic.complexEmbedding table i C

/-- The embedded and reindexed cyclotomic table evaluated at a numbered row and numbered class. -/
theorem complexTableOfCyclotomic_apply_classOf
    (table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e))
    (i j : Fin d.numClasses) :
    d.complexTableOfCyclotomic e table
        (finCongr d.numClasses_eq_card_conjClasses i) (d.classOf j) =
      Cyclotomic.complexEmbedding (table i j) :=
  d.reindexTableOfMap_apply_classOf Cyclotomic.complexEmbedding table i j

namespace IsCyclotomicCharacterTableSpec

variable {d : ClassData G} {e : ℕ} [NeZero e]
variable {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e)}
variable {degree : Fin d.numClasses → ℕ}
variable (h : d.IsCyclotomicCharacterTableSpec e omega table degree)
include h

omit [NeZero e] in
/-- The identity column of a certified cyclotomic table is its supplied degree vector. -/
theorem table_index_one (i : Fin d.numClasses) : table i (d.index 1) = degree i :=
  IsExactCharacterTableSpec.table_index_one h i

/-- The normalized row of the embedded ordinary table is the corresponding embedded
central-character row. -/
theorem centralCharacterRow_complexTableOfCyclotomic
    (i : Fin (Nat.card (ConjClasses G))) :
    centralCharacterRow (d.complexTableOfCyclotomic e table) i =
      d.reindexModularRow (fun j => Cyclotomic.complexEmbedding
        (omega ((finCongr d.numClasses_eq_card_conjClasses).symm i) j)) :=
  IsExactCharacterTableSpec.centralCharacterRow_reindexTableOfMap h
    Cyclotomic.complexEmbedding i

/-- **A certified exact cyclotomic table satisfies the complex character-table specification.** -/
theorem isCharacterTableSpec :
    IsCharacterTableSpec G (d.complexTableOfCyclotomic e table) :=
  IsExactCharacterTableSpec.isCharacterTableSpec h Cyclotomic.complexEmbedding
    Cyclotomic.complexEmbedding_star

end IsCyclotomicCharacterTableSpec

end ClassData

end TauCeti
