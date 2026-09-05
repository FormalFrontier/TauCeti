/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.Symmetric.Specht.AbsoluteIrreducibility
public import TauCeti.RepresentationTheory.Symmetric.Specht.Character
public import TauCeti.RepresentationTheory.Symmetric.Specht.Completeness
public import Mathlib.RepresentationTheory.FinGroupCharZero
-- Non-public: `Complex.isAlgClosed` is what puts `ℂ` in the scope of the orthogonality relations,
-- and `FDRep.nonempty_iso_of_character_eq_of_simple` consumes it; both are used only inside the
-- proofs below, and no statement here mentions algebraic closedness.
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.RepresentationTheory.CharacterTable.Independence

/-!
# The complex Specht modules classify the irreducible complex representations of `Sₙ`

The Specht module `S^μ` is defined over `ℚ`, and this file extends its scalars to `ℂ`:
`TauCeti.spechtModuleℂ μ` is `ℂ ⊗_ℚ S^μ`, an object of `FDRep ℂ Sₙ`. The point of the file is that
nothing is lost and nothing is gained in the passage — the complex Specht modules are again
**simple**, again pairwise **non-isomorphic**, and again **all** of the simple objects — so the
partitions of `n` classify the irreducible complex representations of the symmetric group exactly as
they classify the rational ones (`TauCeti.partitionEquivSimpleFDRepClasses`).

Simplicity is where the rational theory could fail and does not, and the reason is **absolute
irreducibility**: irreducibility over `ℚ` alone says nothing about `ℂ ⊗_ℚ S^μ`, but
`TauCeti.spechtModuleIntertwiningEndAlgEquiv` says the intertwiner algebra of `S^μ` is `ℚ` itself,
one-dimensional, and the intertwiner space is the kernel of a linear map, so its dimension is
unchanged by the flat extension `ℚ → ℂ` (`Representation.finrank_intertwiningMap_baseChange`).
So the complex endomorphism algebra is one-dimensional too, which over `ℂ` is simplicity
(`FDRep.simple_iff_char_is_norm_one`). The same dimension count with two different partitions is
`0` on the rational side by Schur's lemma, hence `0` on the complex side, which is distinctness; and
the partitions of `n` are as many as the conjugacy classes of `Sₙ`, which bounds the number of
isomorphism classes of simple objects over any field, so distinctness already forces exhaustion.

Because the character of `S^μ` is integer-valued (`TauCeti.spechtChar`), the complex characters are
the same integers read in `ℂ`, and the integer-valued character table of `Sₙ`
(`TauCeti.symmetricCharacterTable`, a `Matrix (Nat.Partition n) (Nat.Partition n) ℤ`), whose casts
recover the rational character values, therefore records the complex ones just as well: the
irreducible complex characters of `Sₙ` are exactly the `χ^μ`.

## Main definitions

* `TauCeti.spechtModuleℂ`: the complex Specht module `ℂ ⊗_ℚ S^μ`.
* `TauCeti.spechtModuleℂFDRepClass`: its isomorphism class as a simple object of `FDRep ℂ Sₙ`.
* `TauCeti.partitionEquivSimpleFDRepClassesℂ`: **the classification**, `μ ↦ ℂ ⊗_ℚ S^μ` as a
  bijection from `Nat.Partition n` to the isomorphism classes of simple objects of `FDRep ℂ Sₙ`.

## Main results

* `TauCeti.character_spechtModuleℂ` and `TauCeti.character_spechtModuleℂ_intCast`: the complex
  character is the rational character, equivalently the integer character `χ^μ`, read in `ℂ`.
* `TauCeti.finrank_spechtModuleℂ`: extending the scalars does not change the dimension.
* `TauCeti.instSimpleSpechtModuleℂ`: **the complex Specht module is simple.**
* `TauCeti.spechtModuleℂ_iso_iff`: complex Specht modules of distinct shapes are non-isomorphic.
* `TauCeti.existsUnique_nonempty_iso_spechtModuleℂ`: every simple object of `FDRep ℂ Sₙ` is a
  complex Specht module for exactly one partition.
* `TauCeti.existsUnique_character_eq_spechtChar`: **the ℂ-corollary** — the irreducible complex
  characters of `Sₙ` are exactly the integer characters `χ^μ`, one for each partition of `n`.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 4.
* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Section 2.4.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "Absolute irreducibility" and "Distinctness and completeness".
-/

public section

namespace TauCeti

open CategoryTheory Module
open scoped MonoidAlgebra

variable {n : ℕ}

/-- The order of `Sₙ` is invertible in `ℂ`, which is what puts the complex Specht modules in the
scope of the character-orthogonality machinery. -/
private noncomputable instance : Invertible ((Nat.card (Equiv.Perm (Fin n)) : ℂ)) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ### The complex Specht module -/

/-- **The complex Specht module** `ℂ ⊗_ℚ S^μ`, the scalar extension of the rational Specht module
`TauCeti.spechtModule` to `ℂ`. It is simple (`TauCeti.instSimpleSpechtModuleℂ`), and as `μ` ranges
over the partitions of `n` these exhaust the simple objects of `FDRep ℂ Sₙ` without repetition
(`TauCeti.partitionEquivSimpleFDRepClassesℂ`). -/
noncomputable def spechtModuleℂ (μ : n.Partition) : FDRep ℂ (Equiv.Perm (Fin n)) :=
  FDRep.of (Representation.baseChange ℂ (spechtModule μ).ρ)

/-- The complex Specht module is the object of `FDRep ℂ Sₙ` carrying the base change of the
rational Specht representation. -/
theorem spechtModuleℂ_def (μ : n.Partition) :
    spechtModuleℂ μ = FDRep.of (Representation.baseChange ℂ (spechtModule μ).ρ) := (rfl)

/-- **The complex character is the rational character read in `ℂ`.** -/
theorem character_spechtModuleℂ (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    (spechtModuleℂ μ).character σ = algebraMap ℚ ℂ ((spechtModule μ).character σ) := by
  rw [spechtModuleℂ_def, FDRep.character, FDRep.of_ρ']
  exact Representation.character_baseChange _ σ

/-- **The complex character is the integer character `χ^μ` read in `ℂ`.** Combined with
`TauCeti.spechtChar_eq_value` this says that the integer-valued character table of `Sₙ`,
`TauCeti.symmetricCharacterTable`, whose casts recover the rational character values, records the
complex ones too. -/
@[simp]
theorem character_spechtModuleℂ_intCast (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    (spechtModuleℂ μ).character σ = (spechtChar μ σ : ℂ) := by
  rw [character_spechtModuleℂ, ← spechtChar_cast, eq_ratCast, Rat.cast_intCast]

/-- **Extending the scalars does not change the dimension.** -/
theorem finrank_spechtModuleℂ (μ : n.Partition) :
    finrank ℂ (spechtModuleℂ μ) = finrank ℚ (spechtModule μ) := by
  rw [spechtModuleℂ_def]
  exact Module.finrank_baseChange

/-- **The dimension of an intertwiner space is unchanged by complexification.** This is the whole
mechanism of the file: the rational intertwiner dimensions, `1` on the diagonal and `0` off it,
are inherited verbatim by the complex Specht modules. -/
private theorem finrank_intertwiningMap_spechtModuleℂ (μ ν : n.Partition) :
    finrank ℂ (Representation.IntertwiningMap (spechtModuleℂ μ).ρ (spechtModuleℂ ν).ρ)
      = finrank ℚ (Representation.IntertwiningMap (spechtModule μ).ρ (spechtModule ν).ρ) := by
  rw [spechtModuleℂ_def, spechtModuleℂ_def, FDRep.of_ρ', FDRep.of_ρ']
  exact Representation.finrank_intertwiningMap_baseChange _ _

/-! ### Simplicity and distinctness -/

/-- Specht modules of distinct shapes are inequivalent as rational representations. This is
`TauCeti.spechtModule_iso_iff` read at the level of `Representation.Equiv`. -/
private theorem isEmpty_equiv_spechtModule {μ ν : n.Partition} (h : μ ≠ ν) :
    IsEmpty (Representation.Equiv (spechtModule μ).ρ (spechtModule ν).ρ) := by
  rw [← not_nonempty_iff]
  intro hne
  exact h ((spechtModule_iso_iff μ ν).mp (nonempty_fdRepIso_iff.mpr hne))

/-- Schur's lemma over `ℚ`: there are no nonzero intertwiners between Specht modules of distinct
shapes. -/
private theorem finrank_intertwiningMap_spechtModule_eq_zero {μ ν : n.Partition} (h : μ ≠ ν) :
    finrank ℚ (Representation.IntertwiningMap (spechtModule μ).ρ (spechtModule ν).ρ) = 0 := by
  have _ : Representation.IsIrreducible (spechtModule μ).ρ := isIrreducible_spechtModule μ
  have _ : Representation.IsIrreducible (spechtModule ν).ρ := isIrreducible_spechtModule ν
  have _ := isEmpty_equiv_spechtModule h
  have : Subsingleton (Representation.IntertwiningMap (spechtModule μ).ρ (spechtModule ν).ρ) :=
    inferInstance
  exact Module.finrank_zero_of_subsingleton

/-- **The character inner product of two complex Specht modules is the rational intertwiner
dimension times `|Sₙ|`.** Unnormalized, because this is the shape both
`FDRep.simple_iff_char_is_norm_one` and `FDRep.char_orthonormal` consume. -/
private theorem sum_character_spechtModuleℂ_mul_character_spechtModuleℂ_inv_eq_finrank_mul_card
    (μ ν : n.Partition) :
    ∑ σ : Equiv.Perm (Fin n),
        (spechtModuleℂ μ).character σ * (spechtModuleℂ ν).character σ⁻¹
      = (finrank ℚ (Representation.IntertwiningMap (spechtModule ν).ρ (spechtModule μ).ρ) : ℂ) *
        (Nat.card (Equiv.Perm (Fin n)) : ℂ) := by
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank
    (spechtModuleℂ ν).ρ (spechtModuleℂ μ).ρ
  rw [finrank_intertwiningMap_spechtModuleℂ] at h
  have hN : ((Nat.card (Equiv.Perm (Fin n)) : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp at h
  rw [mul_comm]
  exact h

/-- **The complex Specht module is simple.** Its endomorphism algebra is one-dimensional, because
that of the rational Specht module is (`TauCeti.spechtModuleIntertwiningEndAlgEquiv`) and the
dimension survives complexification; over `ℂ` a one-dimensional endomorphism algebra is
simplicity. -/
instance instSimpleSpechtModuleℂ (μ : n.Partition) : Simple (spechtModuleℂ μ) := by
  have hend : finrank ℚ
      (Representation.IntertwiningMap (spechtModule μ).ρ (spechtModule μ).ρ) = 1 := by
    rw [(spechtModuleIntertwiningEndAlgEquiv μ).toLinearEquiv.finrank_eq]
    exact Module.finrank_self ℚ
  rw [FDRep.simple_iff_char_is_norm_one,
    sum_character_spechtModuleℂ_mul_character_spechtModuleℂ_inv_eq_finrank_mul_card, hend]
  simp

/-- **Complex Specht modules of distinct shapes are non-isomorphic.** -/
@[simp]
theorem spechtModuleℂ_iso_iff (μ ν : n.Partition) :
    Nonempty (spechtModuleℂ μ ≅ spechtModuleℂ ν) ↔ μ = ν := by
  refine ⟨fun hiso => ?_, by rintro rfl; exact ⟨Iso.refl _⟩⟩
  by_contra hne
  have h := FDRep.char_orthonormal (spechtModuleℂ μ) (spechtModuleℂ ν)
  rw [sum_character_spechtModuleℂ_mul_character_spechtModuleℂ_inv_eq_finrank_mul_card,
    finrank_intertwiningMap_spechtModule_eq_zero (Ne.symm hne)] at h
  simp [hiso] at h

/-- **A complex Specht module is determined by its character.** A simple object of `FDRep ℂ Sₙ` is
determined by its character (`FDRep.nonempty_iso_of_character_eq_of_simple`), and complex Specht
modules of distinct shapes are non-isomorphic. -/
theorem spechtModuleℂ_character_injective :
    Function.Injective fun μ : n.Partition => (spechtModuleℂ μ).character := fun _ _ h =>
  (spechtModuleℂ_iso_iff _ _).mp (FDRep.nonempty_iso_of_character_eq_of_simple _ _ h)

/-! ### The classification -/

/-- **The isomorphism class of the complex Specht module `ℂ ⊗_ℚ S^μ`** as a simple object of
`FDRep ℂ Sₙ`. The complex counterpart of `TauCeti.spechtModuleFDRepClass`. -/
noncomputable def spechtModuleℂFDRepClass (μ : n.Partition) :
    SimpleFDRepClasses ℂ (Equiv.Perm (Fin n)) :=
  SimpleFDRepClasses.mk (spechtModuleℂ μ)

@[simp]
theorem spechtModuleℂFDRepClass_def (μ : n.Partition) :
    spechtModuleℂFDRepClass μ = SimpleFDRepClasses.mk (spechtModuleℂ μ) :=
  (rfl)

/-- **The complex Specht modules exhaust the simple objects of `FDRep ℂ Sₙ`.** They are pairwise
non-isomorphic and as many as the conjugacy classes of `Sₙ`, and no field admits more isomorphism
classes of simple objects than the group has conjugacy classes. -/
theorem spechtModuleℂFDRepClass_bijective :
    Function.Bijective (spechtModuleℂFDRepClass (n := n)) := by
  refine SimpleFDRepClasses.bijective_of_injective_of_card_conjClasses_le ?_
    (Nat.card_congr (partitionEquivConjClasses n).symm).le
  intro μ ν h
  rw [spechtModuleℂFDRepClass_def, spechtModuleℂFDRepClass_def,
    SimpleFDRepClasses.mk_eq_mk_iff] at h
  exact (spechtModuleℂ_iso_iff μ ν).mp h

/-- **The classification of the irreducible complex representations of the symmetric group**:
`μ ↦ ℂ ⊗_ℚ S^μ` is a bijection from the partitions of `n` to the isomorphism classes of simple
objects of `FDRep ℂ Sₙ`. It is the complex counterpart of
`TauCeti.partitionEquivSimpleFDRepClasses`, indexed by the same partitions. -/
noncomputable def partitionEquivSimpleFDRepClassesℂ (n : ℕ) :
    n.Partition ≃ SimpleFDRepClasses ℂ (Equiv.Perm (Fin n)) :=
  Equiv.ofBijective _ spechtModuleℂFDRepClass_bijective

@[simp]
theorem partitionEquivSimpleFDRepClassesℂ_apply (μ : n.Partition) :
    partitionEquivSimpleFDRepClassesℂ n μ = spechtModuleℂFDRepClass μ :=
  (rfl)

/-- The partition a complex Specht module's class names is the partition it was built from: the
`symm` companion of `TauCeti.partitionEquivSimpleFDRepClassesℂ_apply`. -/
@[simp]
theorem partitionEquivSimpleFDRepClassesℂ_symm_mk_spechtModuleℂ (μ : n.Partition) :
    (partitionEquivSimpleFDRepClassesℂ n).symm
      (SimpleFDRepClasses.mk (spechtModuleℂ μ)) = μ := by
  rw [← spechtModuleℂFDRepClass_def, ← partitionEquivSimpleFDRepClassesℂ_apply,
    Equiv.symm_apply_apply]

/-- **Every simple object of `FDRep ℂ Sₙ` is a complex Specht module for exactly one
partition.** -/
theorem existsUnique_nonempty_iso_spechtModuleℂ (X : FDRep ℂ (Equiv.Perm (Fin n))) [Simple X] :
    ∃! μ : n.Partition, Nonempty (X ≅ spechtModuleℂ μ) := by
  obtain ⟨μ, hμ⟩ := spechtModuleℂFDRepClass_bijective.surjective (SimpleFDRepClasses.mk X)
  rw [spechtModuleℂFDRepClass_def, SimpleFDRepClasses.mk_eq_mk_iff] at hμ
  refine ⟨μ, ⟨hμ.some.symm⟩, fun ν hν => ?_⟩
  exact (spechtModuleℂ_iso_iff ν μ).mp ⟨hν.some.symm.trans hμ.some.symm⟩

/-- **The `ℂ`-corollary: the irreducible complex characters of `Sₙ` are exactly the `χ^μ`.** Every
simple object of `FDRep ℂ Sₙ` has, for exactly one partition `μ` of `n`, the integer character
`TauCeti.spechtChar` of the Specht module `S^μ` read in `ℂ`. With
`TauCeti.spechtChar_eq_value` this identifies the integer-valued
`TauCeti.symmetricCharacterTable n`, whose casts recover the rational character values, as
recording the complex character table of `Sₙ` as well. -/
theorem existsUnique_character_eq_spechtChar (X : FDRep ℂ (Equiv.Perm (Fin n))) [Simple X] :
    ∃! μ : n.Partition, X.character = fun σ => (spechtChar μ σ : ℂ) := by
  obtain ⟨μ, ⟨e⟩, -⟩ := existsUnique_nonempty_iso_spechtModuleℂ X
  have hμ : X.character = fun σ => (spechtChar μ σ : ℂ) := by
    rw [FDRep.char_iso e]
    exact funext (character_spechtModuleℂ_intCast μ)
  refine ⟨μ, hμ, fun ν hν => ?_⟩
  have hchar : (spechtModuleℂ ν).character = (spechtModuleℂ μ).character := by
    funext σ
    rw [character_spechtModuleℂ_intCast, character_spechtModuleℂ_intCast]
    exact congrFun (hν.symm.trans hμ) σ
  exact spechtModuleℂ_character_injective hchar

end TauCeti
