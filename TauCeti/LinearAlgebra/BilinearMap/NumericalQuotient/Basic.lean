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

The intermediate pairings with only one argument quotiented are also provided.  Quotienting the
left argument makes the pairing left-separating, while quotienting the right argument makes it
right-separating; no assertion is made about the other side until both quotients are taken.

## Main definitions

* `TauCeti.biadditiveToIntBilinear`: a biadditive pairing viewed as a `ℤ`-bilinear map.
* `TauCeti.leftRadical` and `TauCeti.rightRadical`: the two radicals of a bilinear map.
* `TauCeti.LeftNumericalQuotient` and `TauCeti.RightNumericalQuotient`: the corresponding
  quotient modules.
* `TauCeti.leftNumericalPairing` and `TauCeti.rightNumericalPairing`: the one-sided quotient
  pairings.
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
def biadditiveToIntBilinear (b : A →+ B →+ D) : A →ₗ[ℤ] B →ₗ[ℤ] D where
  toFun a := (addMonoidHomLequivInt ℤ) (b a)
  map_add' a a' := by
    ext x
    simp
  map_smul' n a := by
    ext x
    simp

/-- Reinterpreting a biadditive pairing over `ℤ` does not change its values. -/
@[simp]
theorem biadditiveToIntBilinear_apply (b : A →+ B →+ D) (a : A) (x : B) :
    biadditiveToIntBilinear b a x = b a x :=
  (rfl)

end Biadditive

section Radicals

variable (b : L →ₗ[R] M →ₗ[R] P)

/-- The **left radical** of a bilinear map: the elements in the first argument which pair to zero
with every element of the second argument. -/
def leftRadical : Submodule R L :=
  b.ker

/-- The **right radical** of a bilinear map: the elements in the second argument which pair to zero
with every element of the first argument. -/
def rightRadical : Submodule R M :=
  b.flip.ker

/-- Membership in the left radical means pairing to zero against every second argument. -/
@[simp]
theorem mem_leftRadical_iff (x : L) : x ∈ leftRadical b ↔ ∀ y : M, b x y = 0 := by
  rw [leftRadical, LinearMap.mem_ker]
  constructor
  · intro h y
    rw [h, LinearMap.zero_apply]
  · intro h
    ext y
    exact (h y).trans (LinearMap.zero_apply y).symm

/-- Membership in the right radical means pairing to zero against every first argument. -/
@[simp]
theorem mem_rightRadical_iff (y : M) : y ∈ rightRadical b ↔ ∀ x : L, b x y = 0 := by
  rw [rightRadical, LinearMap.mem_ker]
  constructor
  · intro h x
    rw [← b.flip_apply x y, h, LinearMap.zero_apply]
  · intro h
    ext x
    simpa only [LinearMap.flip_apply, LinearMap.zero_apply] using h x

/-- A bilinear map is left-separating exactly when its left radical is trivial. -/
theorem separatingLeft_iff_leftRadical_eq_bot :
    b.SeparatingLeft ↔ leftRadical b = ⊥ := by
  rw [leftRadical, LinearMap.separatingLeft_iff_ker_eq_bot]

/-- A bilinear map is right-separating exactly when its right radical is trivial. -/
theorem separatingRight_iff_rightRadical_eq_bot :
    b.SeparatingRight ↔ rightRadical b = ⊥ := by
  rw [rightRadical, LinearMap.separatingRight_iff_flip_ker_eq_bot]

end Radicals

section Quotients

variable (b : L →ₗ[R] M →ₗ[R] P)

/-- The quotient of the first argument by the left radical. -/
abbrev LeftNumericalQuotient := L ⧸ leftRadical b

/-- The quotient of the second argument by the right radical. -/
abbrev RightNumericalQuotient := M ⧸ rightRadical b

/-- The quotient map from the first argument to its left numerical quotient. -/
def leftNumericalQuotientMk : L →ₗ[R] LeftNumericalQuotient b :=
  (leftRadical b).mkQ

/-- The quotient map from the second argument to its right numerical quotient. -/
def rightNumericalQuotientMk : M →ₗ[R] RightNumericalQuotient b :=
  (rightRadical b).mkQ

/-- The left numerical quotient map sends an element to its quotient class. -/
theorem leftNumericalQuotientMk_apply (x : L) :
    leftNumericalQuotientMk b x = Submodule.Quotient.mk x :=
  Submodule.mkQ_apply (leftRadical b) x

/-- The right numerical quotient map sends an element to its quotient class. -/
theorem rightNumericalQuotientMk_apply (y : M) :
    rightNumericalQuotientMk b y = Submodule.Quotient.mk y :=
  Submodule.mkQ_apply (rightRadical b) y

/-- The kernel of the left numerical quotient map is the left radical. -/
@[simp]
theorem ker_leftNumericalQuotientMk : (leftNumericalQuotientMk b).ker = leftRadical b :=
  (leftRadical b).ker_mkQ

/-- The kernel of the right numerical quotient map is the right radical. -/
@[simp]
theorem ker_rightNumericalQuotientMk : (rightNumericalQuotientMk b).ker = rightRadical b :=
  (rightRadical b).ker_mkQ

/-- The left numerical quotient map is surjective. -/
theorem leftNumericalQuotientMk_surjective :
    Function.Surjective (leftNumericalQuotientMk b) :=
  (leftRadical b).mkQ_surjective

/-- The right numerical quotient map is surjective. -/
theorem rightNumericalQuotientMk_surjective :
    Function.Surjective (rightNumericalQuotientMk b) :=
  (rightRadical b).mkQ_surjective

/-- A class in the left numerical quotient vanishes exactly when its representative lies in the
left radical. -/
@[simp]
theorem leftNumericalQuotientMk_eq_zero_iff (x : L) :
    leftNumericalQuotientMk b x = 0 ↔ x ∈ leftRadical b := by
  rw [← LinearMap.mem_ker, ker_leftNumericalQuotientMk]

/-- A class in the right numerical quotient vanishes exactly when its representative lies in the
right radical. -/
@[simp]
theorem rightNumericalQuotientMk_eq_zero_iff (y : M) :
    rightNumericalQuotientMk b y = 0 ↔ y ∈ rightRadical b := by
  rw [← LinearMap.mem_ker, ker_rightNumericalQuotientMk]

/-- Two elements have the same left numerical class exactly when their difference lies in the
left radical. -/
@[simp]
theorem leftNumericalQuotientMk_eq_iff (x x' : L) :
    leftNumericalQuotientMk b x = leftNumericalQuotientMk b x' ↔
      x - x' ∈ leftRadical b := by
  rw [← sub_eq_zero, ← map_sub, leftNumericalQuotientMk_eq_zero_iff]

/-- Two elements have the same right numerical class exactly when their difference lies in the
right radical. -/
@[simp]
theorem rightNumericalQuotientMk_eq_iff (y y' : M) :
    rightNumericalQuotientMk b y = rightNumericalQuotientMk b y' ↔
      y - y' ∈ rightRadical b := by
  rw [← sub_eq_zero, ← map_sub, rightNumericalQuotientMk_eq_zero_iff]

/-- Quotienting only the first argument by the left radical gives a pairing on the left numerical
quotient and the original second argument. -/
def leftNumericalPairing : LeftNumericalQuotient b →ₗ[R] M →ₗ[R] P :=
  (leftRadical b).liftQ b le_rfl

/-- Quotienting only the second argument by the right radical gives a pairing on the original
first argument and the right numerical quotient. -/
def rightNumericalPairing : L →ₗ[R] RightNumericalQuotient b →ₗ[R] P :=
  ((rightRadical b).liftQ b.flip le_rfl).flip

/-- The left quotient pairing is represented by the original pairing. -/
@[simp]
theorem leftNumericalPairing_mk (x : L) (y : M) :
    leftNumericalPairing b (leftNumericalQuotientMk b x) y = b x y := by
  rw [leftNumericalPairing, leftNumericalQuotientMk, Submodule.mkQ_apply]
  exact DFunLike.congr_fun (Submodule.liftQ_apply (leftRadical b) b x) y

/-- The right quotient pairing is represented by the original pairing. -/
@[simp]
theorem rightNumericalPairing_mk (x : L) (y : M) :
    rightNumericalPairing b x (rightNumericalQuotientMk b y) = b x y := by
  rw [rightNumericalPairing, rightNumericalQuotientMk, Submodule.mkQ_apply]
  simpa only [LinearMap.flip_apply] using
    DFunLike.congr_fun (Submodule.liftQ_apply (rightRadical b) b.flip y) x

/-- Quotienting the first argument by the left radical makes the pairing left-separating. -/
theorem leftNumericalPairing_separatingLeft : (leftNumericalPairing b).SeparatingLeft := by
  intro q hq
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b q
  rw [leftNumericalQuotientMk_eq_zero_iff]
  exact (mem_leftRadical_iff b x).mpr fun y ↦ leftNumericalPairing_mk b x y ▸ hq y

/-- Quotienting the second argument by the right radical makes the pairing right-separating. -/
theorem rightNumericalPairing_separatingRight : (rightNumericalPairing b).SeparatingRight := by
  intro q hq
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b q
  rw [rightNumericalQuotientMk_eq_zero_iff]
  exact (mem_rightRadical_iff b y).mpr fun x ↦ rightNumericalPairing_mk b x y ▸ hq x

/-- The pairing descended through both the left and right radicals. -/
def numericalPairing :
    LeftNumericalQuotient b →ₗ[R] RightNumericalQuotient b →ₗ[R] P :=
  b.liftQ₂ (leftRadical b) (rightRadical b) le_rfl le_rfl

/-- The numerical pairing is represented by the original pairing. -/
@[simp]
theorem numericalPairing_mk (x : L) (y : M) :
    numericalPairing b (leftNumericalQuotientMk b x) (rightNumericalQuotientMk b y) =
      b x y := by
  rw [numericalPairing, leftNumericalQuotientMk, rightNumericalQuotientMk,
    Submodule.mkQ_apply]
  exact LinearMap.liftQ₂_mk le_rfl le_rfl x y

/-- The numerical pairing is the unique bilinear map between the two quotients which agrees with
the original pairing on representatives. -/
theorem numericalPairing_unique
    (c : LeftNumericalQuotient b →ₗ[R] RightNumericalQuotient b →ₗ[R] P)
    (hc : ∀ x y, c (leftNumericalQuotientMk b x) (rightNumericalQuotientMk b y) = b x y) :
    c = numericalPairing b := by
  apply LinearMap.ext₂
  intro q r
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b q
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b r
  rw [hc, numericalPairing_mk]

/-- The numerical pairing has trivial left radical. -/
theorem numericalPairing_separatingLeft : (numericalPairing b).SeparatingLeft := by
  intro q hq
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b q
  rw [leftNumericalQuotientMk_eq_zero_iff]
  refine (mem_leftRadical_iff b x).mpr fun y ↦ ?_
  rw [← numericalPairing_mk b x y]
  exact hq (rightNumericalQuotientMk b y)

/-- The numerical pairing has trivial right radical. -/
theorem numericalPairing_separatingRight : (numericalPairing b).SeparatingRight := by
  intro q hq
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b q
  rw [rightNumericalQuotientMk_eq_zero_iff]
  refine (mem_rightRadical_iff b y).mpr fun x ↦ ?_
  rw [← numericalPairing_mk b x y]
  exact hq (leftNumericalQuotientMk b x)

/-- Quotienting both arguments by their respective radicals produces a nondegenerate pairing. -/
theorem numericalPairing_nondegenerate : (numericalPairing b).Nondegenerate :=
  ⟨numericalPairing_separatingLeft b, numericalPairing_separatingRight b⟩

/-- The left radical of the numerical pairing is trivial. -/
@[simp]
theorem leftRadical_numericalPairing : leftRadical (numericalPairing b) = ⊥ :=
  (separatingLeft_iff_leftRadical_eq_bot (numericalPairing b)).mp
    (numericalPairing_separatingLeft b)

/-- The right radical of the numerical pairing is trivial. -/
@[simp]
theorem rightRadical_numericalPairing : rightRadical (numericalPairing b) = ⊥ :=
  (separatingRight_iff_rightRadical_eq_bot (numericalPairing b)).mp
    (numericalPairing_separatingRight b)

end Quotients

end TauCeti
