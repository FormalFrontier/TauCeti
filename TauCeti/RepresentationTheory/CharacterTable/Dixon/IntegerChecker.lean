/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ExactChecker

/-!
# An exact checker for integer-valued character tables

The rational stage of the Dixon--Schneider algorithm produces integer central-character and
ordinary character tables.  This file specializes the coefficient-independent exact certificate
from `TauCeti.RepresentationTheory.CharacterTable.Dixon.ExactChecker` to `ℤ`, where `star` is the
identity, and preserves the integer-stage API used by the rational solver.

## Main definitions

* `TauCeti.ClassData.IsIntegerCharacterTableSpec`: the exact numbered certificate over `ℤ`.
* `TauCeti.ClassData.integerCharacterTableChecker`: its executable Boolean checker.
* `TauCeti.ClassData.complexTableOfInteger`: cast and reindex an integer table into the type
  expected by `TauCeti.IsCharacterTableSpec`.

## Main result

* `TauCeti.ClassData.IsIntegerCharacterTableSpec.isCharacterTableSpec`: a successful integer
  certificate yields the complex character-table specification.
-/

public section

namespace TauCeti

namespace ClassData

universe u

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable (d : ClassData G)

/-- An exact character-table certificate specialized to integer entries. -/
abbrev IsIntegerCharacterTableSpec
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ)
    (degree : Fin d.numClasses → ℕ) : Prop :=
  d.IsExactCharacterTableSpec (fun x => x) omega table degree

/-- The executable Boolean checker for an integer central-character table, ordinary table, and
their character degrees. -/
def integerCharacterTableChecker
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ)
    (degree : Fin d.numClasses → ℕ) : Bool :=
  d.exactCharacterTableChecker (fun x => x) omega table degree

/-- The Boolean integer checker succeeds precisely when the integer certificate holds. -/
@[simp]
theorem integerCharacterTableChecker_eq_true_iff
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ)
    (degree : Fin d.numClasses → ℕ) :
    d.integerCharacterTableChecker omega table degree = true ↔
      d.IsIntegerCharacterTableSpec omega table degree :=
  d.exactCharacterTableChecker_eq_true_iff (fun x => x) omega table degree

/-- Cast a numbered integer table to `ℂ`, reindexing its rows by the cardinality of the conjugacy
classes and its columns by the conjugacy classes themselves. -/
noncomputable def complexTableOfInteger
    (table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ) :
    Matrix (Fin (Nat.card (ConjClasses G))) (ConjClasses G) ℂ :=
  d.reindexTableOfMap (Int.castRingHom ℂ) table

/-- The cast-and-reindexed integer table evaluated at arbitrary row and column indices. -/
@[simp]
theorem complexTableOfInteger_apply
    (table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ)
    (i : Fin (Nat.card (ConjClasses G))) (C : ConjClasses G) :
    d.complexTableOfInteger table i C =
      (table ((finCongr d.numClasses_eq_card_conjClasses).symm i)
        (d.equivConjClasses.symm C) : ℂ) :=
  d.reindexTableOfMap_apply (Int.castRingHom ℂ) table i C

/-- The cast-and-reindexed integer table evaluated at a numbered row and numbered class. -/
theorem complexTableOfInteger_apply_classOf
    (table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ) (i j : Fin d.numClasses) :
    d.complexTableOfInteger table
        (finCongr d.numClasses_eq_card_conjClasses i) (d.classOf j) = (table i j : ℂ) :=
  d.reindexTableOfMap_apply_classOf (Int.castRingHom ℂ) table i j

namespace IsIntegerCharacterTableSpec

variable {d : ClassData G}
variable {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ}
variable {degree : Fin d.numClasses → ℕ}
variable (h : d.IsIntegerCharacterTableSpec omega table degree)
include h

/-- The identity column of a certified integer table is its supplied degree vector. -/
theorem table_index_one (i : Fin d.numClasses) : table i (d.index 1) = degree i := by
  exact_mod_cast IsExactCharacterTableSpec.table_index_one h i

/-- The normalized row of the cast ordinary table is the corresponding cast central-character
row, with both transported from the numbering of `d` to conjugacy classes. -/
theorem centralCharacterRow_complexTableOfInteger
    (i : Fin (Nat.card (ConjClasses G))) :
    centralCharacterRow (d.complexTableOfInteger table) i =
      d.reindexModularRow
        (fun j => (omega ((finCongr d.numClasses_eq_card_conjClasses).symm i) j : ℂ)) :=
  IsExactCharacterTableSpec.centralCharacterRow_reindexTableOfMap h (Int.castRingHom ℂ) i

/-- **A certified integer table satisfies the complex character-table specification.** -/
theorem isCharacterTableSpec :
    IsCharacterTableSpec G (d.complexTableOfInteger table) :=
  IsExactCharacterTableSpec.isCharacterTableSpec h (Int.castRingHom ℂ) fun x => by simp

end IsIntegerCharacterTableSpec

end ClassData

end TauCeti
