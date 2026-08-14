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
hooks and is not proved here.

## Main definitions

* `TauCeti.spechtChar`: the `ℤ`-valued character `χ^μ` of the Specht module `S^μ`.
* `TauCeti.spechtCharClass`: its descent to the conjugacy classes of `Sₙ`.
* `TauCeti.spechtCharValue`: its value on the class of cycle type `ν`.
* `TauCeti.symmetricCharacterTable`: the character table of `Sₙ`, a
  `Matrix (Nat.Partition n) (Nat.Partition n) ℤ`.

## Main results

* `TauCeti.spechtChar_cast`: the integer character casts to the rational character of `S^μ`.
* `TauCeti.spechtChar_eq_of_partition_eq`: it depends only on the cycle type.
* `TauCeti.spechtChar_eq_value`: it is read off the character table.
* `TauCeti.character_spechtModule_eq_intCast`: conversely the table recovers the rational
  character, so no information is lost in passing to `ℤ`.
* `TauCeti.spechtChar_one`: the value at the identity is the degree `dim_ℚ S^μ`, which is positive.

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

/-- The integer character carries exactly the information of the rational one: two permutations
share an integer character value precisely when they share the rational one. -/
theorem spechtChar_eq_iff (μ : n.Partition) (σ τ : Equiv.Perm (Fin n)) :
    spechtChar μ σ = spechtChar μ τ ↔
      (spechtModule μ).character σ = (spechtModule μ).character τ := by
  rw [← spechtChar_cast, ← spechtChar_cast]
  exact ⟨fun h => by rw [h], fun h => Int.cast_injective h⟩

/-- **The integer character is a class function.** -/
theorem spechtChar_conj (μ : n.Partition) (σ τ : Equiv.Perm (Fin n)) :
    spechtChar μ (τ * σ * τ⁻¹) = spechtChar μ σ :=
  FDRep.intCharacter_conj (spechtModule μ) σ τ

/-- Conjugate permutations have the same integer character. -/
theorem spechtChar_eq_of_isConj (μ : n.Partition) {σ τ : Equiv.Perm (Fin n)} (h : IsConj σ τ) :
    spechtChar μ σ = spechtChar μ τ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  exact (spechtChar_conj μ σ c).symm

/-- **The integer character depends only on the cycle type**, two permutations of `Fin n` being
conjugate exactly when they have the same partition. -/
theorem spechtChar_eq_of_partition_eq (μ : n.Partition) {σ τ : Equiv.Perm (Fin n)}
    (h : σ.partition = τ.partition) : spechtChar μ σ = spechtChar μ τ :=
  spechtChar_eq_of_isConj μ (Equiv.Perm.partition_eq_of_isConj.mpr h)

/-- **The value at the identity is the degree** `dim_ℚ S^μ`. -/
@[simp]
theorem spechtChar_one (μ : n.Partition) : spechtChar μ 1 = finrank ℚ (spechtModule μ) :=
  FDRep.intCharacter_one (spechtModule μ)

/-- The degree of `S^μ` is positive, so the identity column of the character table has positive
entries. -/
theorem spechtChar_one_pos (μ : n.Partition) : 0 < spechtChar μ 1 := by
  rw [spechtChar_one]
  exact_mod_cast finrank_spechtModule_pos μ

/-! ## Descent to the conjugacy classes -/

/-- **The integer character as a function of the conjugacy class.** -/
noncomputable def spechtCharClass (μ : n.Partition) : ConjClasses (Equiv.Perm (Fin n)) → ℤ :=
  Quotient.lift (spechtChar μ) fun _ _ h => spechtChar_eq_of_isConj μ h

@[simp]
theorem spechtCharClass_mk (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    spechtCharClass μ (ConjClasses.mk σ) = spechtChar μ σ := (rfl)

/-- **The character value of `S^μ` on the class of cycle type `ν`**, the entry `χ^μ(ν)` of the
character table. -/
noncomputable def spechtCharValue (μ ν : n.Partition) : ℤ :=
  spechtCharClass μ (partitionEquivConjClasses n ν)

theorem spechtCharValue_def (μ ν : n.Partition) :
    spechtCharValue μ ν = spechtCharClass μ (partitionEquivConjClasses n ν) := (rfl)

/-- The character value is computed at any permutation representing the class of `ν`. -/
theorem spechtCharValue_eq_spechtChar (μ ν : n.Partition) {σ : Equiv.Perm (Fin n)}
    (hσ : ConjClasses.mk σ = partitionEquivConjClasses n ν) :
    spechtCharValue μ ν = spechtChar μ σ := by
  rw [spechtCharValue_def, ← hσ, spechtCharClass_mk]

/-- **The integer character is read off the character table**, at the partition indexing the class
of the permutation. -/
theorem spechtChar_eq_value (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    spechtChar μ σ =
      spechtCharValue μ ((partitionEquivConjClasses n).symm (ConjClasses.mk σ)) := by
  rw [spechtCharValue_def, Equiv.apply_symm_apply, spechtCharClass_mk]

/-! ## The character table -/

/-- **The character table of the symmetric group `Sₙ`**: the integer matrix whose `(μ, ν)` entry is
the value `χ^μ(ν)` of the character of the Specht module `S^μ` on the conjugacy class of cycle
type `ν`. Both indices are partitions of `n`, which index the irreducible rational representations
(`TauCeti.partitionEquivSimpleModuleClasses`) and the conjugacy classes
(`TauCeti.partitionEquivConjClasses`) respectively. -/
noncomputable def symmetricCharacterTable (n : ℕ) : Matrix n.Partition n.Partition ℤ :=
  Matrix.of fun μ ν => spechtCharValue μ ν

@[simp]
theorem symmetricCharacterTable_apply (μ ν : n.Partition) :
    symmetricCharacterTable n μ ν = spechtCharValue μ ν := (rfl)

/-- **The character table recovers the rational characters of the Specht modules**, so passing from
`ℚ` to `ℤ` and from permutations to cycle types loses nothing. -/
theorem character_spechtModule_eq_intCast (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    (spechtModule μ).character σ =
      ((symmetricCharacterTable n μ
        ((partitionEquivConjClasses n).symm (ConjClasses.mk σ)) : ℤ) : ℚ) := by
  rw [symmetricCharacterTable_apply, ← spechtChar_eq_value, spechtChar_cast]

/-- **The column of the identity holds the degrees** `dim_ℚ S^μ`. -/
theorem symmetricCharacterTable_apply_one_class (μ : n.Partition) :
    symmetricCharacterTable n μ ((partitionEquivConjClasses n).symm (ConjClasses.mk 1)) =
      finrank ℚ (spechtModule μ) := by
  rw [symmetricCharacterTable_apply, ← spechtChar_eq_value, spechtChar_one]

end TauCeti
