/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.InnerConjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# Conjugating closed subgroups of affine groups

A Hopf ideal `I` in a commutative Hopf algebra `H` cuts out a closed subgroup of the affine
group represented by `H`. Pulling `I` back along the coordinate automorphism attached to a
rational point `g` cuts out the conjugate subgroup `g G_I g⁻¹`.

The characteristic point theorem keeps the contravariance visible: a point `x` belongs to the
subgroup cut out by `I` exactly when its conjugate by `g` belongs to the subgroup cut out by
`I.conjugate g`.

## Main declarations

* `TauCeti.HopfIdeal.conjugate`: the defining Hopf ideal of a conjugate closed subgroup.
* `TauCeti.HopfIdeal.mem_quotientPointsSubgroup_conjugate_iff`: conjugation identifies the
  corresponding algebra-valued point subgroups.
* `TauCeti.HopfIdeal.conjugateOrderIso`: conjugation as an order automorphism of Hopf ideals.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§3.5 and 10.20.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §8.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u v

namespace HopfIdeal

variable {R : Type u} [CommRing R]
variable {H : _root_.CommHopfAlgCat.{u} R}

/-- The defining ideal of the conjugate by `g` of the closed subgroup cut out by `I`.

The inverse image is taken along the coordinate pullback for `x ↦ g x g⁻¹`. Since coordinate
rings are contravariant, this ideal cuts out the direct image of the subgroup under that
automorphism. -/
noncomputable def conjugate (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) : HopfIdeal R H :=
  I.comapOfSurjective (CommHopfAlgCat.innerConjugationIso H g).hom.hom
    (ConcreteCategory.bijective_of_isIso
      (CommHopfAlgCat.innerConjugationIso H g).hom).2

/-- Membership in the conjugate defining ideal is membership after applying the coordinate
inner automorphism. -/
@[simp]
theorem mem_conjugate_iff (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (x : H) :
    x ∈ I.conjugate g ↔ (CommHopfAlgCat.innerConjugationIso H g).hom.hom x ∈ I := by
  rw [conjugate, mem_comapOfSurjective]

/-- A point belongs to the closed subgroup cut out by `I` exactly when its conjugate by `g`
belongs to the conjugate closed subgroup.

Thus conjugation gives a bijection from the original subgroup's `A`-points to the conjugate
subgroup's `A`-points, uniformly in the commutative value algebra `A`. -/
theorem mem_quotientPointsSubgroup_conjugate_iff (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    CommHopfAlgCat.extendPoint H A g * x * (CommHopfAlgCat.extendPoint H A g)⁻¹ ∈
        CommHopfAlgCat.quotientPointsSubgroup H (I.conjugate g) A ↔
      x ∈ CommHopfAlgCat.quotientPointsSubgroup H I A := by
  let f := (CommHopfAlgCat.innerConjugationIso H g).hom.hom
  have hf : Function.Bijective f :=
    ConcreteCategory.bijective_of_isIso (CommHopfAlgCat.innerConjugationIso H g).hom
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  constructor
  · intro hx y hy
    obtain ⟨z, rfl⟩ := hf.2 y
    have hz : z ∈ I.conjugate g := (mem_conjugate_iff I g z).2 hy
    have haction := congrArg (fun p : HopfAlgebra.points (R := R) (H := H) A ↦ p.ofConv z)
      (CommHopfAlgCat.mapPointsFunctor_innerConjugationIso_hom_app_apply H g A x)
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply_apply] at haction
    exact haction.trans (hx z hz)
  · intro hx y hy
    have haction := congrArg (fun p : HopfAlgebra.points (R := R) (H := H) A ↦ p.ofConv y)
      (CommHopfAlgCat.mapPointsFunctor_innerConjugationIso_hom_app_apply H g A x)
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply_apply] at haction
    exact haction.symm.trans (hx (f y) ((mem_conjugate_iff I g y).1 hy))

/-- Conjugating a closed subgroup by the identity point does not change it. -/
@[simp]
theorem conjugate_one (I : HopfIdeal R H) :
    I.conjugate
        (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) = I := by
  ext x
  rw [mem_conjugate_iff, CommHopfAlgCat.innerConjugationIso_one]
  rfl

/-- Successive conjugation first by `g` and then by `h` is conjugation by `h * g`. The reversed
order comes from the contravariance of defining ideals. -/
@[simp]
theorem conjugate_conjugate (I : HopfIdeal R H)
    (g h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (I.conjugate g).conjugate h = I.conjugate (h * g) := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff,
    CommHopfAlgCat.innerConjugationIso_mul]
  rfl

/-- Conjugating by `g⁻¹` undoes conjugation by `g`. -/
theorem conjugate_inv_conjugate (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (I.conjugate g).conjugate g⁻¹ = I := by
  rw [conjugate_conjugate, inv_mul_cancel g, conjugate_one]

/-- Conjugating by `g` undoes conjugation by `g⁻¹`. -/
theorem conjugate_conjugate_inv (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (I.conjugate g⁻¹).conjugate g = I := by
  rw [conjugate_conjugate, mul_inv_cancel g, conjugate_one]

/-- Conjugation by a rational point as an order automorphism of defining Hopf ideals. -/
noncomputable def conjugateOrderIso
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    HopfIdeal R H ≃o HopfIdeal R H where
  toFun I := I.conjugate g
  invFun I := I.conjugate g⁻¹
  left_inv I := conjugate_inv_conjugate I g
  right_inv I := conjugate_conjugate_inv I g
  map_rel_iff' := comapOfSurjective_le_comapOfSurjective_iff
    (CommHopfAlgCat.innerConjugationIso H g).hom.hom
      (ConcreteCategory.bijective_of_isIso
        (CommHopfAlgCat.innerConjugationIso H g).hom).2

/-- Applying the conjugation order isomorphism conjugates the defining Hopf ideal. -/
@[simp]
theorem conjugateOrderIso_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (I : HopfIdeal R H) :
    conjugateOrderIso g I = I.conjugate g := by
  rfl

/-- Applying the inverse conjugation order isomorphism conjugates by the inverse point. -/
@[simp]
theorem conjugateOrderIso_symm_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (I : HopfIdeal R H) :
    (conjugateOrderIso g).symm I = I.conjugate g⁻¹ := by
  rfl

end HopfIdeal

end TauCeti
