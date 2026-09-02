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

This supplies the closed-subgroup conjugation operation required before the Layer 7 conjugacy
theorems for maximal tori and Borel subgroups in the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

universe u

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

/-- The conjugate ideal is the inverse image along the coordinate inner automorphism. -/
theorem conjugate_eq_comapOfSurjective (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    I.conjugate g =
      I.comapOfSurjective (CommHopfAlgCat.innerConjugationIso H g).hom.hom
        (ConcreteCategory.bijective_of_isIso
          (CommHopfAlgCat.innerConjugationIso H g).hom).2 := by
  rfl

/-- Membership in the conjugate defining ideal is membership after applying the coordinate
inner automorphism. -/
@[simp]
theorem mem_conjugate_iff (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (x : H) :
    x ∈ I.conjugate g ↔ (CommHopfAlgCat.innerConjugationIso H g).hom.hom x ∈ I := by
  rw [conjugate_eq_comapOfSurjective, mem_comapOfSurjective]

private theorem mapDomainMulEquiv_innerConjugation_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (hf : Function.Bijective (CommHopfAlgCat.innerConjugationIso H g).hom.hom)
    (A : CommAlgCat.{u} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    AlgHom.mapDomainMulEquiv (A := A)
        (BialgEquiv.ofBijective (CommHopfAlgCat.innerConjugationIso H g).hom.hom hf) x =
      CommHopfAlgCat.extendPoint H A g * x * (CommHopfAlgCat.extendPoint H A g)⁻¹ := by
  have h := CommHopfAlgCat.mapPointsFunctor_innerConjugationIso_hom_app_apply H g A x
  apply WithConv.ofConv_injective
  exact congrArg WithConv.ofConv h

/-- A point belongs to the closed subgroup cut out by `I` exactly when its conjugate by `g`
belongs to the conjugate closed subgroup.

Thus conjugation gives a bijection from the original subgroup's `A`-points to the conjugate
subgroup's `A`-points, uniformly in the commutative value algebra `A`. -/
theorem mem_quotientPointsSubgroup_conjugate_iff (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{u} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    CommHopfAlgCat.extendPoint H A g * x * (CommHopfAlgCat.extendPoint H A g)⁻¹ ∈
        CommHopfAlgCat.quotientPointsSubgroup H (I.conjugate g) A ↔
      x ∈ CommHopfAlgCat.quotientPointsSubgroup H I A := by
  let f := (CommHopfAlgCat.innerConjugationIso H g).hom.hom
  let hf : Function.Bijective f :=
    ConcreteCategory.bijective_of_isIso (CommHopfAlgCat.innerConjugationIso H g).hom
  have h := CommHopfAlgCat.mapDomainMulEquiv_mem_quotientPointsSubgroup_comapOfSurjective_iff
    f hf.1 hf.2 I A x
  rw [mapDomainMulEquiv_innerConjugation_apply g hf] at h
  change _ ∈ CommHopfAlgCat.quotientPointsSubgroup H (I.conjugate g) A ↔ _ at h
  exact h

/-- Conjugation preserves containment of closed subgroups, expressed in the reversed order on
their defining Hopf ideals. -/
theorem conjugate_mono
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    Monotone (fun I : HopfIdeal R H ↦ I.conjugate g) := by
  intro I J hIJ
  exact comapOfSurjective_mono _ _ hIJ

/-- Conjugating a closed subgroup by the identity point does not change it. -/
@[simp]
theorem conjugate_one (I : HopfIdeal R H) :
    I.conjugate
        (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) = I := by
  ext x
  rw [mem_conjugate_iff, CommHopfAlgCat.innerConjugationIso_one]
  rfl

/-- Conjugating by `g⁻¹` undoes conjugation by `g`. -/
@[simp]
theorem conjugate_inv_conjugate (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (I.conjugate g).conjugate g⁻¹ = I := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, CommHopfAlgCat.innerConjugationIso_inv]
  simp

/-- Conjugating by `g` undoes conjugation by `g⁻¹`. -/
@[simp]
theorem conjugate_conjugate_inv (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (I.conjugate g⁻¹).conjugate g = I := by
  simpa only [inv_inv] using conjugate_inv_conjugate I g⁻¹

/-- Conjugation by a rational point as an order automorphism of defining Hopf ideals. -/
noncomputable def conjugateOrderIso
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    HopfIdeal R H ≃o HopfIdeal R H where
  toFun I := I.conjugate g
  invFun I := I.conjugate g⁻¹
  left_inv I := conjugate_inv_conjugate I g
  right_inv I := conjugate_conjugate_inv I g
  map_rel_iff' := by
    intro I J
    change I.conjugate g ≤ J.conjugate g ↔ I ≤ J
    constructor
    · intro h
      have := conjugate_mono g⁻¹ h
      change (I.conjugate g).conjugate g⁻¹ ≤ (J.conjugate g).conjugate g⁻¹ at this
      rw [conjugate_inv_conjugate, conjugate_inv_conjugate] at this
      exact this
    · intro h
      exact conjugate_mono g h

end HopfIdeal

end TauCeti
