/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Values
public import TauCeti.RepresentationTheory.Symmetric.Partitions
public import TauCeti.RepresentationTheory.Symmetric.Specht.Module

/-!
# The integer character of a Specht module, and the character table of `Sₙ`

The Specht module `S^μ` is a representation of `Sₙ` over `ℚ`, so its character
`(spechtModule μ).character` takes values in `ℚ`. Those values are in fact **integers**: a
character value at an element of finite order is an algebraic integer, and a rational algebraic
integer is an integer. That refinement is what this file records, as
`TauCeti.spechtChar μ : Equiv.Perm (Fin n) → ℤ`, together with the cast
`TauCeti.spechtChar_cast` back to the rational character; integrality is a theorem, not part of
the definition.

A character is a class function, and the conjugacy classes of `Sₙ` are the partitions of `n`
(`TauCeti.partitionEquivConjClasses`), so `spechtChar μ` descends to a function of a partition
`ν`, its **character value** `TauCeti.spechtCharValue μ ν`. Both indices being partitions of `n`,
these values assemble into a square integer matrix, the **character table of the symmetric group**
`TauCeti.symmetricCharacterTable n`. Its rows are indexed by the Specht modules, which are
precisely the irreducible rational representations of `Sₙ`
(`TauCeti.partitionEquivSimpleModuleClasses`), and its columns by the conjugacy classes; the
column of the identity holds the degrees.

The general half of the argument is stated for an arbitrary rational representation of a finite
group, as `TauCeti.FDRep.intCharacter`, and is what this file specializes. Nothing here computes
an entry of the table: the recursion that does is the Murnaghan--Nakayama rule, which needs rim
hooks and is not proved here. Neither is `symmetricCharacterTable n` compared with the library's
general `TauCeti.characterTable k G`, which lives over an algebraically closed field and enumerates
its rows by `Fin (Nat.card (ConjClasses G))`, nor is any of the table properties that one carries —
the orthogonality relations, the specification `TauCeti.IsCharacterTableSpec` — proved for it.

## Main definitions

* `TauCeti.spechtChar`: the `ℤ`-valued character `χ^μ` of the Specht module `S^μ`.
* `TauCeti.spechtCharConjClasses`: its descent to the conjugacy classes of `Sₙ`.
* `TauCeti.spechtCharValue`: its value on the class of cycle type `ν`.
* `TauCeti.symmetricCharacterTable`: the character table of `Sₙ`, a
  `Matrix (Nat.Partition n) (Nat.Partition n) ℤ`.

## Main results

* `TauCeti.spechtChar_cast`: the integer character casts to the rational character of `S^μ`.
* `TauCeti.spechtChar_eq_of_partition_eq`: it depends only on the cycle type.
* `TauCeti.spechtChar_one`: the value at the identity is the degree `dim_ℚ S^μ`.
* `TauCeti.spechtChar_one_pos`: that degree is positive.
* `TauCeti.spechtChar_eq_value`: the character is read off the character table.
* `TauCeti.intCast_symmetricCharacterTable_apply`: conversely the table recovers the rational
  character, so no information is lost in passing to `ℤ`.
* `TauCeti.symmetricCharacterTable_one`: the column of the identity class holds the degrees.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 6.
* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Section 4.10.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 6, "The Specht character".
-/

public section

namespace TauCeti

open Module

variable {n : ℕ}

/-! ## The integer character -/

/-- **The integer character `χ^μ` of the Specht module** `S^μ`. The character of `S^μ` takes
rational values, and those values are integers (`TauCeti.FDRep.intCharacter`); this is the
integer-valued refinement, related to the rational character by `TauCeti.spechtChar_cast`. -/
noncomputable def spechtChar (μ : n.Partition) : Equiv.Perm (Fin n) → ℤ :=
  FDRep.intCharacter (spechtModule μ)

theorem spechtChar_def (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    spechtChar μ σ = FDRep.intCharacter (spechtModule μ) σ := (rfl)

/-- **The integer character of `S^μ` casts to its rational character.** This is the whole content
of `TauCeti.spechtChar`: the character of a Specht module is integer-valued. -/
@[simp]
theorem spechtChar_cast (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    (spechtChar μ σ : ℚ) = (spechtModule μ).character σ := by
  rw [spechtChar_def, FDRep.intCharacter_cast]

/-- **The integer character is a class function.** -/
@[simp]
theorem spechtChar_conj (μ : n.Partition) (σ τ : Equiv.Perm (Fin n)) :
    spechtChar μ (τ * σ * τ⁻¹) = spechtChar μ σ :=
  FDRep.intCharacter_conj (spechtModule μ) σ τ

/-- Conjugate permutations have the same integer character. -/
theorem spechtChar_eq_of_isConj (μ : n.Partition) {σ τ : Equiv.Perm (Fin n)} (h : IsConj σ τ) :
    spechtChar μ σ = spechtChar μ τ :=
  FDRep.intCharacter_eq_of_isConj (spechtModule μ) h

/-- **The integer character depends only on the cycle type**, two permutations of `Fin n` being
conjugate exactly when they have the same partition. -/
theorem spechtChar_eq_of_partition_eq (μ : n.Partition) {σ τ : Equiv.Perm (Fin n)}
    (h : σ.partition = τ.partition) : spechtChar μ σ = spechtChar μ τ :=
  spechtChar_eq_of_isConj μ (Equiv.Perm.partition_eq_of_isConj.mpr h)

/-- **The value at the identity is the degree** `dim_ℚ S^μ`. -/
@[simp]
theorem spechtChar_one (μ : n.Partition) : spechtChar μ 1 = finrank ℚ (spechtModule μ) :=
  FDRep.intCharacter_one (spechtModule μ)

/-- **The value at the identity is positive**, the Specht module `S^μ` being nonzero. -/
theorem spechtChar_one_pos (μ : n.Partition) : 0 < spechtChar μ 1 := by
  rw [spechtChar_one]
  exact_mod_cast finrank_spechtModule_pos μ

/-! ## Descent to the conjugacy classes -/

/-- **The integer character as a function of the conjugacy class**, the descent
(`TauCeti.ClassFunction.toConjClasses`) of the class function `TauCeti.FDRep.intClassFunction` of
`S^μ`. -/
noncomputable def spechtCharConjClasses (μ : n.Partition) : ConjClasses (Equiv.Perm (Fin n)) → ℤ :=
  ClassFunction.toConjClasses (FDRep.intClassFunction (spechtModule μ))

theorem spechtCharConjClasses_def (μ : n.Partition) :
    spechtCharConjClasses μ =
      ClassFunction.toConjClasses (FDRep.intClassFunction (spechtModule μ)) := (rfl)

@[simp]
theorem spechtCharConjClasses_mk (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    spechtCharConjClasses μ (ConjClasses.mk σ) = spechtChar μ σ := by
  rw [spechtCharConjClasses_def, ClassFunction.toConjClasses_mk, FDRep.intClassFunction_apply,
    spechtChar_def]

/-- **The character value of `S^μ` on the class of cycle type `ν`**, the entry `χ^μ(ν)` of the
character table. -/
noncomputable def spechtCharValue (μ ν : n.Partition) : ℤ :=
  spechtCharConjClasses μ (partitionEquivConjClasses n ν)

theorem spechtCharValue_def (μ ν : n.Partition) :
    spechtCharValue μ ν = spechtCharConjClasses μ (partitionEquivConjClasses n ν) := (rfl)

/-- The character value is computed at any permutation representing the class of `ν`. -/
theorem spechtCharValue_eq_spechtChar (μ ν : n.Partition) {σ : Equiv.Perm (Fin n)}
    (hσ : ConjClasses.mk σ = partitionEquivConjClasses n ν) :
    spechtCharValue μ ν = spechtChar μ σ := by
  rw [spechtCharValue_def, ← hσ, spechtCharConjClasses_mk]

/-- **The integer character is read off the character table**, at the partition indexing the class
of the permutation. -/
theorem spechtChar_eq_value (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    spechtChar μ σ =
      spechtCharValue μ ((partitionEquivConjClasses n).symm (ConjClasses.mk σ)) := by
  rw [spechtCharValue_def, Equiv.apply_symm_apply, spechtCharConjClasses_mk]

/-! ## The character table -/

/-- **The character table of the symmetric group `Sₙ`**: the integer matrix whose `(μ, ν)` entry is
the value `χ^μ(ν)` of the character of the Specht module `S^μ` on the conjugacy class of cycle
type `ν`. Both indices are partitions of `n`, which index the irreducible rational representations
(`TauCeti.partitionEquivSimpleModuleClasses`) and the conjugacy classes
(`TauCeti.partitionEquivConjClasses`) respectively.

Implementation note: this is not the library's general `TauCeti.characterTable k G`, which is
defined over an algebraically closed field, takes values there, and enumerates its rows by
`Fin (Nat.card (ConjClasses G))` through an arbitrary choice of ordering of the irreducible
characters. This matrix is the `ℤ`-valued table of `Sₙ` re-indexed on both sides by the partitions
of `n`. No comparison with `TauCeti.characterTable ℂ (Equiv.Perm (Fin n))` is proved here, and
neither are any of the table properties — the orthogonality relations, or the character-table
specification `TauCeti.IsCharacterTableSpec` — which the general table carries. -/
noncomputable def symmetricCharacterTable (n : ℕ) : Matrix n.Partition n.Partition ℤ :=
  Matrix.of fun μ ν => spechtCharValue μ ν

@[simp]
theorem symmetricCharacterTable_apply (μ ν : n.Partition) :
    symmetricCharacterTable n μ ν = spechtCharValue μ ν := (rfl)

/-- **The character table recovers the rational characters of the Specht modules**, so passing from
`ℚ` to `ℤ` and from permutations to cycle types loses nothing. -/
theorem intCast_symmetricCharacterTable_apply (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    ((symmetricCharacterTable n μ
        ((partitionEquivConjClasses n).symm (ConjClasses.mk σ)) : ℤ) : ℚ) =
      (spechtModule μ).character σ := by
  rw [symmetricCharacterTable_apply, ← spechtChar_eq_value, spechtChar_cast]

/-- **The column of the identity holds the degrees** `dim_ℚ S^μ`. -/
theorem symmetricCharacterTable_one (μ : n.Partition) :
    symmetricCharacterTable n μ ((partitionEquivConjClasses n).symm (ConjClasses.mk 1)) =
      finrank ℚ (spechtModule μ) := by
  rw [symmetricCharacterTable_apply, ← spechtChar_eq_value, spechtChar_one]

end TauCeti
