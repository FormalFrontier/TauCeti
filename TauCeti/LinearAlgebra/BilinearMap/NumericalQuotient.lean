/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Numerical quotients of a bilinear map

For a possibly nonsymmetric bilinear map `b : L →ₗ[R] M →ₗ[R] P`, its left radical and
right radical need not agree—indeed, its two arguments need not even have the same type. This file
defines the two radicals separately, quotients each argument by the appropriate radical, and
descends `b` to a nondegenerate pairing between the resulting quotients. An ordinary biadditive
pairing of additive groups is reinterpreted over `ℤ` by `TauCeti.biadditiveToIntBilinear`.

The intermediate pairings use Mathlib's `Submodule.liftQ`. Quotienting the left argument makes the
pairing left-separating, while quotienting the right argument makes it right-separating; no
assertion is made about the other side until both quotients are taken.

## Main definitions

* `TauCeti.biadditiveToIntBilinear`: a biadditive pairing viewed as a `ℤ`-bilinear map.
* `TauCeti.leftRadical` and `TauCeti.rightRadical`: the two radicals of a bilinear map.
* `TauCeti.LeftNumericalQuotient` and `TauCeti.RightNumericalQuotient`: the corresponding
  quotient modules.
* `TauCeti.numericalPairing`: the pairing between both numerical quotients.

## Main results

* `TauCeti.leftNumericalPairing_separatingLeft` and
  `TauCeti.rightNumericalPairing_separatingRight`: the precise one-sided nondegeneracy results.
* `TauCeti.numericalPairing_nondegenerate`: the pairing between both quotients has zero left and
  right radicals.

The quotient construction uses Mathlib's asymmetric `LinearMap.liftQ₂`.  The terminology and the
warning that the two radicals remain distinct follow Dancso–Licata, *Koszul algebras and flow
lattices*, Section 3.1, and the Grothendieck-groups, Cartan-maps, and Euler-forms roadmap, Layer 7.
-/

public section

namespace TauCeti

universe u₁ u₂ u₃

variable {R : Type*} [CommRing R]
variable {L : Type u₁} {M : Type u₂} {P : Type u₃}
variable [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
variable [AddCommGroup P] [Module R P]

section Biadditive

variable {A B D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]

/-- A biadditive pairing of additive groups, reinterpreted as a bilinear map over `ℤ`.

This is the bridge from pairings such as an Euler pairing, naturally constructed as
`A →+ B →+ D`, to the bilinear numerical-quotient API in this file. -/
def biadditiveToIntBilinear (b : A →+ B →+ D) : A →ₗ[ℤ] B →ₗ[ℤ] D :=
  (addMonoidHomLequivInt ℤ).toLinearMap ∘ₗ b.toIntLinearMap

/-- Reinterpreting a biadditive pairing over `ℤ` does not change its values. -/
@[simp]
theorem biadditiveToIntBilinear_apply (b : A →+ B →+ D) (a : A) (x : B) :
    biadditiveToIntBilinear b a x = b a x :=
  by simp [biadditiveToIntBilinear]

end Biadditive

section Radicals

variable (b : L →ₗ[R] M →ₗ[R] P)

/-- The **left radical** of a bilinear map: the elements in the first argument which pair to zero
with every element of the second argument. -/
abbrev leftRadical : Submodule R L :=
  b.ker

/-- The **right radical** of a bilinear map: the elements in the second argument which pair to zero
with every element of the first argument. -/
abbrev rightRadical : Submodule R M :=
  b.flip.ker

/-- Membership in the left radical means pairing to zero against every second argument. -/
@[simp]
theorem mem_leftRadical_iff (x : L) : x ∈ leftRadical b ↔ ∀ y : M, b x y = 0 := by
  simp [leftRadical, LinearMap.ext_iff]

/-- Membership in the right radical means pairing to zero against every first argument. -/
@[simp]
theorem mem_rightRadical_iff (y : M) : y ∈ rightRadical b ↔ ∀ x : L, b x y = 0 := by
  simp [rightRadical, LinearMap.ext_iff]

end Radicals

section Quotients

variable (b : L →ₗ[R] M →ₗ[R] P)

/-- The quotient of the first argument by the left radical. -/
abbrev LeftNumericalQuotient := L ⧸ leftRadical b

/-- The quotient of the second argument by the right radical. -/
abbrev RightNumericalQuotient := M ⧸ rightRadical b

/-- Quotienting only the first argument by the left radical gives a pairing on the left numerical
quotient and the original second argument, and makes it left-separating. -/
theorem leftNumericalPairing_separatingLeft :
    ((leftRadical b).liftQ b le_rfl).SeparatingLeft := by
  intro q hq
  obtain ⟨x, rfl⟩ := (leftRadical b).mkQ_surjective q
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (mem_leftRadical_iff b x).mpr fun y ↦ by
    simpa only [Submodule.mkQ_apply, Submodule.liftQ_apply] using hq y

/-- Quotienting only the second argument by the right radical gives a pairing on the original first
argument and the right numerical quotient, and makes it right-separating. -/
theorem rightNumericalPairing_separatingRight :
    (((rightRadical b).liftQ b.flip le_rfl).flip).SeparatingRight := by
  intro q hq
  obtain ⟨y, rfl⟩ := (rightRadical b).mkQ_surjective q
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (mem_rightRadical_iff b y).mpr fun x ↦ by
    simpa only [LinearMap.flip_apply, Submodule.mkQ_apply, Submodule.liftQ_apply] using hq x

/-- The pairing descended through both the left and right radicals. -/
def numericalPairing :
    LeftNumericalQuotient b →ₗ[R] RightNumericalQuotient b →ₗ[R] P :=
  b.liftQ₂ (leftRadical b) (rightRadical b) le_rfl le_rfl

/-- The numerical pairing is represented by the original pairing. -/
@[simp]
theorem numericalPairing_mk (x : L) (y : M) :
    numericalPairing b ((leftRadical b).mkQ x) ((rightRadical b).mkQ y) =
      b x y := by
  rw [numericalPairing, Submodule.mkQ_apply]
  exact LinearMap.liftQ₂_mk le_rfl le_rfl x y

/-- The numerical pairing is the unique bilinear map between the two quotients which agrees with
the original pairing on representatives. -/
theorem numericalPairing_unique
    (c : LeftNumericalQuotient b →ₗ[R] RightNumericalQuotient b →ₗ[R] P)
    (hc : ∀ x y, c ((leftRadical b).mkQ x) ((rightRadical b).mkQ y) = b x y) :
    c = numericalPairing b := by
  apply LinearMap.ext₂
  intro q r
  obtain ⟨x, rfl⟩ := (leftRadical b).mkQ_surjective q
  obtain ⟨y, rfl⟩ := (rightRadical b).mkQ_surjective r
  rw [hc, numericalPairing_mk]

/-- The numerical pairing has trivial left radical. -/
theorem numericalPairing_separatingLeft : (numericalPairing b).SeparatingLeft := by
  intro q hq
  obtain ⟨x, rfl⟩ := (leftRadical b).mkQ_surjective q
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine (mem_leftRadical_iff b x).mpr fun y ↦ ?_
  rw [← numericalPairing_mk b x y]
  exact hq ((rightRadical b).mkQ y)

/-- The numerical pairing has trivial right radical. -/
theorem numericalPairing_separatingRight : (numericalPairing b).SeparatingRight := by
  intro q hq
  obtain ⟨y, rfl⟩ := (rightRadical b).mkQ_surjective q
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine (mem_rightRadical_iff b y).mpr fun x ↦ ?_
  rw [← numericalPairing_mk b x y]
  exact hq ((leftRadical b).mkQ x)

/-- Quotienting both arguments by their respective radicals produces a nondegenerate pairing. -/
theorem numericalPairing_nondegenerate : (numericalPairing b).Nondegenerate :=
  ⟨numericalPairing_separatingLeft b, numericalPairing_separatingRight b⟩

end Quotients

end TauCeti
