/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearMap.NumericalQuotient.Basic

/-!
# Functoriality of numerical quotients

A linear map between the left arguments of two bilinear maps descends to their left numerical
quotients precisely after one proves that it sends the first left radical into the second.  The
right-hand construction is independent and has the dual condition.  This file supplies those two
maps, their identity and composition laws, and compatibility with the descended numerical
pairings.

For a pair of maps preserving the original pairings, surjectivity of the map in the opposite
argument supplies the required radical inclusion.  In particular, a pair of linear equivalences
preserving a pairing induces linear equivalences of both numerical quotients, and those
equivalences preserve the numerical pairing.

This is the functoriality target in Layer 7 of the Grothendieck-groups, Cartan-maps, and Euler-forms
roadmap.  The separate left and right hypotheses are essential for nonsymmetric pairings: neither
radical condition follows from the other.

## Main definitions

* `TauCeti.leftNumericalMap` and `TauCeti.rightNumericalMap`: maps induced on the two numerical
  quotients by a proved radical inclusion.
* `TauCeti.leftNumericalEquiv` and `TauCeti.rightNumericalEquiv`: the equivalences induced by a
  pairing-preserving pair of linear equivalences.

## Main results

* `TauCeti.numericalPairing_map_map`: compatible quotient maps preserve the numerical pairing.
* `TauCeti.numericalPairing_equiv_equiv`: the equivalences induced by a pairing equivalence
  preserve the numerical pairing.
-/

public section

namespace TauCeti

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇

variable {R : Type*} [CommRing R]
variable {L : Type u₁} {M : Type u₂} {P : Type u₃}
variable {L' : Type u₄} {M' : Type u₅} {L'' : Type u₆} {M'' : Type u₇}
variable [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
variable [AddCommGroup L'] [Module R L'] [AddCommGroup M'] [Module R M']
variable [AddCommGroup L''] [Module R L''] [AddCommGroup M''] [Module R M'']
variable [AddCommGroup P] [Module R P]

section Maps

variable (b : L →ₗ[R] M →ₗ[R] P) (c : L' →ₗ[R] M' →ₗ[R] P)

/-- A linear map of left arguments descends to the left numerical quotients when it sends the
source left radical into the target left radical. -/
def leftNumericalMap (f : L →ₗ[R] L')
    (hf : leftRadical b ≤ (leftRadical c).comap f) :
    LeftNumericalQuotient b →ₗ[R] LeftNumericalQuotient c :=
  (leftRadical b).mapQ (leftRadical c) f hf

/-- A linear map of right arguments descends to the right numerical quotients when it sends the
source right radical into the target right radical. -/
def rightNumericalMap (g : M →ₗ[R] M')
    (hg : rightRadical b ≤ (rightRadical c).comap g) :
    RightNumericalQuotient b →ₗ[R] RightNumericalQuotient c :=
  (rightRadical b).mapQ (rightRadical c) g hg

/-- The map on left numerical quotients sends the class of a representative to the class of its
image. -/
@[simp]
theorem leftNumericalMap_mk (f : L →ₗ[R] L')
    (hf : leftRadical b ≤ (leftRadical c).comap f) (x : L) :
    leftNumericalMap b c f hf (leftNumericalQuotientMk b x) =
      leftNumericalQuotientMk c (f x) := by
  simp only [leftNumericalMap, leftNumericalQuotientMk_apply, Submodule.mapQ_apply]

/-- The map on right numerical quotients sends the class of a representative to the class of its
image. -/
@[simp]
theorem rightNumericalMap_mk (g : M →ₗ[R] M')
    (hg : rightRadical b ≤ (rightRadical c).comap g) (y : M) :
    rightNumericalMap b c g hg (rightNumericalQuotientMk b y) =
      rightNumericalQuotientMk c (g y) := by
  simp only [rightNumericalMap, rightNumericalQuotientMk_apply, Submodule.mapQ_apply]

/-- The identity of the left argument induces the identity on the left numerical quotient. -/
@[simp]
theorem leftNumericalMap_id :
    leftNumericalMap b b LinearMap.id (by rw [Submodule.comap_id]) = LinearMap.id :=
  Submodule.mapQ_id (leftRadical b)

/-- The identity of the right argument induces the identity on the right numerical quotient. -/
@[simp]
theorem rightNumericalMap_id :
    rightNumericalMap b b LinearMap.id (by rw [Submodule.comap_id]) = LinearMap.id :=
  Submodule.mapQ_id (rightRadical b)

variable (d : L'' →ₗ[R] M'' →ₗ[R] P)

/-- Composition of left-argument maps induces composition of the maps on left numerical
quotients. -/
theorem leftNumericalMap_comp (f : L →ₗ[R] L') (g : L' →ₗ[R] L'')
    (hf : leftRadical b ≤ (leftRadical c).comap f)
    (hg : leftRadical c ≤ (leftRadical d).comap g) :
    leftNumericalMap b d (g.comp f) (hf.trans (Submodule.comap_mono hg)) =
      (leftNumericalMap c d g hg).comp (leftNumericalMap b c f hf) :=
  Submodule.mapQ_comp (leftRadical b) (leftRadical c) (leftRadical d) f g hf hg

/-- Composition of right-argument maps induces composition of the maps on right numerical
quotients. -/
theorem rightNumericalMap_comp (f : M →ₗ[R] M') (g : M' →ₗ[R] M'')
    (hf : rightRadical b ≤ (rightRadical c).comap f)
    (hg : rightRadical c ≤ (rightRadical d).comap g) :
    rightNumericalMap b d (g.comp f) (hf.trans (Submodule.comap_mono hg)) =
      (rightNumericalMap c d g hg).comp (rightNumericalMap b c f hf) :=
  Submodule.mapQ_comp (rightRadical b) (rightRadical c) (rightRadical d) f g hf hg

end Maps

section PairingMaps

variable (b : L →ₗ[R] M →ₗ[R] P) (c : L' →ₗ[R] M' →ₗ[R] P)
variable (f : L →ₗ[R] L') (g : M →ₗ[R] M')

/-- If a pair of maps preserves a pairing and the right map is surjective, then the left map sends
the left radical into the target left radical. -/
theorem leftRadical_le_comap_of_surjective_of_pairing (hg : Function.Surjective g)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    leftRadical b ≤ (leftRadical c).comap f := by
  intro x hx
  rw [Submodule.mem_comap, mem_leftRadical_iff]
  intro y'
  obtain ⟨y, rfl⟩ := hg y'
  rw [hpair]
  exact (mem_leftRadical_iff b x).mp hx y

/-- If a pair of maps preserves a pairing and the left map is surjective, then the right map sends
the right radical into the target right radical. -/
theorem rightRadical_le_comap_of_surjective_of_pairing (hf : Function.Surjective f)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    rightRadical b ≤ (rightRadical c).comap g := by
  intro y hy
  rw [Submodule.mem_comap, mem_rightRadical_iff]
  intro x'
  obtain ⟨x, rfl⟩ := hf x'
  rw [hpair]
  exact (mem_rightRadical_iff b y).mp hy x

/-- A pair of compatible maps on left and right numerical quotients preserves the descended
numerical pairing. -/
theorem numericalPairing_map_map
    (hf : leftRadical b ≤ (leftRadical c).comap f)
    (hg : rightRadical b ≤ (rightRadical c).comap g)
    (hpair : ∀ x y, c (f x) (g y) = b x y)
    (x : LeftNumericalQuotient b) (y : RightNumericalQuotient b) :
    numericalPairing c (leftNumericalMap b c f hf x) (rightNumericalMap b c g hg y) =
      numericalPairing b x y := by
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b x
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b y
  simp only [leftNumericalMap_mk, rightNumericalMap_mk, numericalPairing_mk, hpair]

end PairingMaps

section Equivalences

variable (b : L →ₗ[R] M →ₗ[R] P) (c : L' →ₗ[R] M' →ₗ[R] P)
variable (f : L ≃ₗ[R] L') (g : M ≃ₗ[R] M')

/-- A pairing-preserving pair of linear equivalences identifies the two left radicals. -/
theorem map_leftRadical_eq (hpair : ∀ x y, c (f x) (g y) = b x y) :
    (leftRadical b).map (f : L →ₗ[R] L') = leftRadical c := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact leftRadical_le_comap_of_surjective_of_pairing b c f g g.surjective hpair
  · intro x' hx'
    obtain ⟨x, rfl⟩ := f.surjective x'
    refine ⟨x, ?_, rfl⟩
    exact (mem_leftRadical_iff b x).mpr fun y ↦ by
      rw [← hpair]
      exact (mem_leftRadical_iff c (f x)).mp hx' (g y)

/-- A pairing-preserving pair of linear equivalences identifies the two right radicals. -/
theorem map_rightRadical_eq (hpair : ∀ x y, c (f x) (g y) = b x y) :
    (rightRadical b).map (g : M →ₗ[R] M') = rightRadical c := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact rightRadical_le_comap_of_surjective_of_pairing b c f g f.surjective hpair
  · intro y' hy'
    obtain ⟨y, rfl⟩ := g.surjective y'
    refine ⟨y, ?_, rfl⟩
    exact (mem_rightRadical_iff b y).mpr fun x ↦ by
      rw [← hpair]
      exact (mem_rightRadical_iff c (g y)).mp hy' (f x)

/-- A pairing-preserving pair of linear equivalences induces an equivalence of left numerical
quotients. -/
def leftNumericalEquiv (hpair : ∀ x y, c (f x) (g y) = b x y) :
    LeftNumericalQuotient b ≃ₗ[R] LeftNumericalQuotient c :=
  Submodule.Quotient.equiv (leftRadical b) (leftRadical c) f
    (map_leftRadical_eq b c f g hpair)

/-- A pairing-preserving pair of linear equivalences induces an equivalence of right numerical
quotients. -/
def rightNumericalEquiv (hpair : ∀ x y, c (f x) (g y) = b x y) :
    RightNumericalQuotient b ≃ₗ[R] RightNumericalQuotient c :=
  Submodule.Quotient.equiv (rightRadical b) (rightRadical c) g
    (map_rightRadical_eq b c f g hpair)

/-- The induced equivalence of left numerical quotients sends a representative to the class of
its image. -/
@[simp]
theorem leftNumericalEquiv_mk (hpair : ∀ x y, c (f x) (g y) = b x y) (x : L) :
    leftNumericalEquiv b c f g hpair (leftNumericalQuotientMk b x) =
      leftNumericalQuotientMk c (f x) := by
  simp only [leftNumericalEquiv, Submodule.Quotient.equiv_apply,
    leftNumericalQuotientMk_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe]

/-- The induced equivalence of right numerical quotients sends a representative to the class of
its image. -/
@[simp]
theorem rightNumericalEquiv_mk (hpair : ∀ x y, c (f x) (g y) = b x y) (y : M) :
    rightNumericalEquiv b c f g hpair (rightNumericalQuotientMk b y) =
      rightNumericalQuotientMk c (g y) := by
  simp only [rightNumericalEquiv, Submodule.Quotient.equiv_apply,
    rightNumericalQuotientMk_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe]

/-- The inverse induced equivalence of left numerical quotients sends a representative to the
class of its inverse image. -/
@[simp]
theorem leftNumericalEquiv_symm_mk (hpair : ∀ x y, c (f x) (g y) = b x y) (x : L') :
    (leftNumericalEquiv b c f g hpair).symm (leftNumericalQuotientMk c x) =
      leftNumericalQuotientMk b (f.symm x) := by
  rw [LinearEquiv.symm_apply_eq, leftNumericalEquiv_mk, LinearEquiv.apply_symm_apply]

/-- The inverse induced equivalence of right numerical quotients sends a representative to the
class of its inverse image. -/
@[simp]
theorem rightNumericalEquiv_symm_mk (hpair : ∀ x y, c (f x) (g y) = b x y) (y : M') :
    (rightNumericalEquiv b c f g hpair).symm (rightNumericalQuotientMk c y) =
      rightNumericalQuotientMk b (g.symm y) := by
  rw [LinearEquiv.symm_apply_eq, rightNumericalEquiv_mk, LinearEquiv.apply_symm_apply]

/-- The equivalences induced on the two numerical quotients preserve the numerical pairing. -/
theorem numericalPairing_equiv_equiv
    (hpair : ∀ x y, c (f x) (g y) = b x y)
    (x : LeftNumericalQuotient b) (y : RightNumericalQuotient b) :
    numericalPairing c (leftNumericalEquiv b c f g hpair x)
        (rightNumericalEquiv b c f g hpair y) = numericalPairing b x y := by
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b x
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b y
  simp only [leftNumericalEquiv_mk, rightNumericalEquiv_mk, numericalPairing_mk, hpair]

end Equivalences

end TauCeti
