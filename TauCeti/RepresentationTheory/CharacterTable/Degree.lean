/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.CentralCharacter
public import TauCeti.RepresentationTheory.CharacterTable.Values
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-!
# The degree of an irreducible character divides the group order

For an irreducible representation `ρ` of a finite group `G` over an algebraically closed field of
characteristic zero, the degree `χ(1) = dim V` divides `|G|`.

The proof is the classical one. First orthogonality gives `∑_g χ(g) χ(g⁻¹) = |G|`. Collecting that
sum one conjugacy class at a time and substituting the class-sum identity
`ωᵪ(K_C) · χ(1) = |C| · χ(g_C)` for the central character turns it into

`χ(1) · ∑_C ωᵪ(K_C) χ(g_C⁻¹) = |G|`.

Every factor of the remaining sum is an algebraic integer -- the values of a central character on
the class sums because the class sums are integral over `ℤ`, the character values because they are
sums of roots of unity -- so `|G| / χ(1)` is an algebraic integer. It is also rational, and a
rational algebraic integer is an integer, so `χ(1)` divides `|G|`.

## Main statements

* `TauCeti.Representation.finrank_mul_sum_centralCharacter_eq_card`: the division-free identity
  `χ(1) · ∑_C ωᵪ(K_C) χ(g_C⁻¹) = |G|`.
* `TauCeti.Representation.finrank_dvd_card` and `TauCeti.FDRep.finrank_dvd_card`: the degree of an
  irreducible representation divides the order of the group.

## Implementation notes

The character value at the inverse, `g ↦ χ(g⁻¹)`, is the character of the dual representation
(`Representation.char_dual`), so the sum over conjugacy classes is indexed through
`TauCeti.ClassFunction.toConjClasses` of that character rather than through a choice of class
representatives. The corresponding representative form is
`TauCeti.Representation.centralCharacter_classSumCenter_mul_character_one`.

## References

This proves the "degree divides the order" item of Layer 4 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).
See I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 3.11, or J.-P. Serre, *Linear
Representations of Finite Groups*, Section 6.5.
-/

public section

namespace TauCeti

open Module (finrank)
open scoped MonoidAlgebra

/-- A rational algebraic integer is an integer, in the form used below: if `n · z = m` for natural
numbers `m` and `n` with `n ≠ 0`, and `z` is integral over `ℤ` in a field of characteristic zero,
then `n` divides `m`. -/
private theorem dvd_of_isIntegral_of_natCast_mul_eq {k : Type*} [Field k] [CharZero k] {m n : ℕ}
    {z : k} (hz : IsIntegral ℤ z) (h : (n : k) * z = m) (hn : n ≠ 0) : n ∣ m := by
  have hnk : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hz' : algebraMap ℚ k ((m : ℚ) / (n : ℚ)) = z := by
    rw [map_div₀, map_natCast, map_natCast, eq_comm, eq_div_iff hnk, mul_comm]
    exact h
  have hq : IsIntegral ℤ ((m : ℚ) / (n : ℚ)) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ k).injective).mp (hz' ▸ hz)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hq
  have hyq : (y : ℚ) * (n : ℚ) = (m : ℚ) := by
    rw [← eq_intCast (algebraMap ℤ ℚ) y, hy, div_mul_cancel₀]
    exact Nat.cast_ne_zero.mpr hn
  refine Int.natCast_dvd_natCast.mp ⟨y, ?_⟩
  exact_mod_cast (by linarith : (m : ℚ) = (n : ℚ) * (y : ℚ))

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

section Divisibility

/-- The pointwise product `g ↦ χ(g) χ(g⁻¹)` is a class function: conjugation acts on `g` and on
`g⁻¹` simultaneously. -/
private theorem character_mul_character_inv_mem_classFunction (ρ : Representation k G V) :
    (fun g : G => ρ.character g * ρ.character g⁻¹) ∈ ClassFunction k G := by
  refine ClassFunction.mem_iff.mpr fun g h => ?_
  have hinv : (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ := by group
  rw [hinv, ρ.char_conj, ρ.char_conj]

variable [Fintype G] [DecidableEq G] [IsAlgClosed k] [FiniteDimensional k V]
  (ρ : Representation k G V) [ρ.IsIrreducible]

/-- **The degree times an algebraic integer is the group order.**

Collecting first orthogonality one conjugacy class at a time and substituting
`ωᵪ(K_C) · χ(1) = |C| · χ(g_C)` gives `χ(1) · ∑_C ωᵪ(K_C) χ(g_C⁻¹) = |G|`, where `g_C` is any
element of the class `C` and the value `χ(g_C⁻¹)` is read off the character of the dual
representation. Both factors of each summand are algebraic integers, which is what makes this the
divisibility statement `TauCeti.Representation.finrank_dvd_card`. -/
theorem finrank_mul_sum_centralCharacter_eq_card [Invertible (Nat.card G : k)] :
    (finrank k V : k) * ∑ C : ConjClasses G, centralCharacter ρ (classSumCenter C) *
        ClassFunction.toConjClasses (ClassFunction.ofCharacter ρ.dual) C = Nat.card G := by
  classical
  -- First orthogonality for `ρ` against itself, with the normalising factor `|G|⁻¹` cleared.
  have hself : Nonempty (_root_.Representation.Equiv ρ ρ) := ⟨.refl ρ⟩
  have horth : ∑ g : G, ρ.character g * ρ.character g⁻¹ = Nat.card G := by
    have h := _root_.Representation.char_orthonormal ρ ρ
    rw [ite_eq_left hself,
      inv_mul_eq_iff_eq_mul₀ (Invertible.ne_zero (a := (Nat.card G : k)))] at h
    simpa using h
  rw [Finset.mul_sum, ← horth,
    ClassFunction.sum_eq_sum_conjClasses
      (⟨_, character_mul_character_inv_mem_classFunction ρ⟩ : ClassFunction k G)]
  refine Finset.sum_congr rfl fun C _ => ?_
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  have hω := centralCharacter_classSumCenter_mul_character_one ρ (rfl : ConjClasses.mk g = _)
  rw [ρ.char_one] at hω
  have hdual : ClassFunction.toConjClasses (ClassFunction.ofCharacter ρ.dual)
      (ConjClasses.mk g) = ρ.character g⁻¹ := by
    rw [ClassFunction.toConjClasses_mk, ClassFunction.ofCharacter_apply, ρ.char_dual]
  rw [hdual, ClassFunction.toConjClasses_mk, ← mul_assoc, mul_comm (finrank k V : k), hω,
    mul_assoc]

end Divisibility

section Dvd

variable [Finite G] [IsAlgClosed k] [CharZero k] [FiniteDimensional k V]
  (ρ : Representation k G V) [ρ.IsIrreducible]

include ρ in
/-- **The degree of an irreducible character divides the order of the group.**

Over an algebraically closed field of characteristic zero, the dimension of an irreducible
representation of a finite group `G` divides `|G|`. -/
theorem finrank_dvd_card : finrank k V ∣ Nat.card G := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hcard : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have : Invertible (Nat.card G : k) := invertibleOfNonzero hcard
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial k[G] ρ.asModule
  have : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  refine dvd_of_isIntegral_of_natCast_mul_eq (k := k) ?_
    (finrank_mul_sum_centralCharacter_eq_card ρ) Module.finrank_pos.ne'
  refine IsIntegral.sum _ fun C _ => IsIntegral.mul
    (isIntegral_centralCharacter_classSumCenter ρ C) ?_
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  rw [ClassFunction.toConjClasses_mk, ClassFunction.ofCharacter_apply]
  exact isIntegral_char ρ.dual (isOfFinOrder_of_finite g).orderOf_pos.ne' (pow_orderOf_eq_one g)

end Dvd

end Representation

namespace FDRep

variable {k G : Type*} [Field k] [IsAlgClosed k] [CharZero k] [Group G] [Finite G]

/-- **The degree of an irreducible character divides the order of the group**, for a bundled
finite-dimensional representation. -/
theorem finrank_dvd_card (X : FDRep k G) [_root_.Representation.IsIrreducible X.ρ] :
    finrank k X ∣ Nat.card G :=
  Representation.finrank_dvd_card X.ρ

end FDRep

end TauCeti
