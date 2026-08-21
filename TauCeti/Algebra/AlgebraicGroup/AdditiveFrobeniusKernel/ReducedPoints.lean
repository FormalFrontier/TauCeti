/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.PUnit
public import TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.Basic

/-!
# Points of `αₚ` over reduced algebras

The Frobenius kernel `αₚ` has nontrivial points only on algebras with nilpotents.  More
precisely, its points on a commutative algebra `A` are the elements whose `p`-th power
vanishes.  If `A` is reduced, such an element is zero, so the `p`-nilpotent subgroup is
trivial and the convolution group `αₚ(A)` has one element.

This is an important qualification to the non-reduced worked example: although the group
scheme `αₚ` itself is nontrivial, it is invisible on every reduced test algebra.  In
particular its field-valued points are trivial.  Non-reduced test algebras, such as dual
numbers, are required to detect it.

The proofs use the description of the functor of points in
`TauCeti.Algebra.AlgebraicGroup.AdditiveFrobeniusKernel.Basic` and Mathlib's
`eq_zero_of_pow_eq_zero` for reduced rings.

This develops the worked example `αₚ` in the Tau Ceti reductive-groups roadmap
(`ReductiveGroups/README.md` in TauCetiRoadmap), whose standing hypotheses require the
theory to retain non-smooth and non-reduced group schemes such as `αₚ`.

## Main declarations

* `TauCeti.AlphaP.pNilpotent_eq_bot_of_isReduced`: the subgroup of `p`-nilpotent
  elements of a reduced algebra is trivial.
* `TauCeti.AlphaP.points_eq_one_of_isReduced`: every `αₚ`-point over a reduced algebra
  is the identity point.
* `TauCeti.AlphaP.instUniquePointsOfIsReduced`: the convolution group of points has a
  unique element over a reduced algebra.
* `TauCeti.AlphaP.reducedPointsMulEquivPUnit`: the resulting canonical equivalence with
  the trivial group.
-/

public section

open WithConv

namespace TauCeti.AlphaP

universe u v

variable {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
variable {A : Type v} [CommRing A] [Algebra R A]

/-- An element of the `p`-nilpotent subgroup of a reduced algebra is the identity of the
ambient additive group. -/
private theorem coe_eq_one_of_isReduced [IsReduced A]
    (a : pNilpotent (R := R) p (A := A)) : (a : Multiplicative A) = 1 := by
  apply Multiplicative.toAdd.injective
  simpa using eq_zero_of_pow_eq_zero
    (x := Multiplicative.toAdd (a : Multiplicative A))
    ((mem_pNilpotent_iff p (a : Multiplicative A)).mp a.property)

/-- Over a reduced algebra, the subgroup of `p`-nilpotent elements is the trivial subgroup. -/
theorem pNilpotent_eq_bot_of_isReduced [IsReduced A] :
    pNilpotent (R := R) p (A := A) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro a ha
  exact coe_eq_one_of_isReduced p ⟨a, ha⟩

/-- Every point of `αₚ` over a reduced algebra maps to the identity element of the additive
group under the canonical inclusion. -/
@[simp]
theorem pointsHom_eq_one_of_isReduced [IsReduced A]
    (F : WithConv (CoordinateRing (R := R) p →ₐ[R] A)) : pointsHom p F = 1 := by
  have hmem : pointsHom p F ∈ pNilpotent (R := R) p (A := A) :=
    ⟨F, rfl⟩
  exact coe_eq_one_of_isReduced p ⟨pointsHom p F, hmem⟩

/-- Every point of `αₚ` over a reduced algebra is the identity for convolution. -/
theorem points_eq_one_of_isReduced [IsReduced A]
    (F : WithConv (CoordinateRing (R := R) p →ₐ[R] A)) : F = 1 := by
  apply pointsHom_injective (R := R) p (A := A)
  rw [pointsHom_eq_one_of_isReduced, map_one]

/-- The convolution group of `αₚ`-points over a reduced algebra has a unique element. -/
noncomputable instance instUniquePointsOfIsReduced [IsReduced A] :
    Unique (WithConv (CoordinateRing (R := R) p →ₐ[R] A)) :=
  @Unique.mk' _ ⟨1⟩ ⟨fun F G ↦ (points_eq_one_of_isReduced p F).trans
    (points_eq_one_of_isReduced p G).symm⟩

/-- Over a reduced algebra, the functor of points of `αₚ` is canonically isomorphic to the
trivial group. -/
noncomputable def reducedPointsMulEquivPUnit [IsReduced A] :
    WithConv (CoordinateRing (R := R) p →ₐ[R] A) ≃* PUnit :=
  MulEquiv.ofUnique

@[simp]
theorem reducedPointsMulEquivPUnit_apply [IsReduced A]
    (F : WithConv (CoordinateRing (R := R) p →ₐ[R] A)) :
    reducedPointsMulEquivPUnit p F = PUnit.unit :=
  rfl

@[simp]
theorem reducedPointsMulEquivPUnit_symm_apply [IsReduced A] (x : PUnit) :
    (reducedPointsMulEquivPUnit (R := R) (A := A) p).symm x = 1 := by
  exact points_eq_one_of_isReduced (R := R) (A := A) p _

end TauCeti.AlphaP
