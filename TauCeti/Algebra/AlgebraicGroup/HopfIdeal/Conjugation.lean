/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.InnerConjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Basic

/-!
# Conjugating closed subgroups of affine groups

A Hopf ideal `I` in a commutative Hopf algebra `H` cuts out a closed subgroup of the affine
group represented by `H`. Pulling `I` back along the coordinate automorphism attached to a
rational point `g` cuts out the conjugate subgroup `g G_I g⁻¹`.

The characteristic point theorem states that a point `x` belongs to the subgroup cut out by `I`
exactly when its conjugate by `g` belongs to the subgroup cut out by `I.conjugate g`.

## Main declarations

* `TauCeti.HopfIdeal.conjugate`: the defining Hopf ideal of a conjugate closed subgroup.
* `TauCeti.HopfIdeal.conj_mem_quotientPointsSubgroup_conjugate_iff`: conjugation identifies the
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
@[simp]
theorem conj_mem_quotientPointsSubgroup_conjugate_iff (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    HopfAlgebra.extendPoint H A g * x * (HopfAlgebra.extendPoint H A g)⁻¹ ∈
        CommHopfAlgCat.quotientPointsSubgroup H (I.conjugate g) A ↔
      x ∈ CommHopfAlgCat.quotientPointsSubgroup H I A := by
  let f := (CommHopfAlgCat.innerConjugationIso H g).hom.hom
  have hf : Function.Bijective f :=
    ConcreteCategory.bijective_of_isIso (CommHopfAlgCat.innerConjugationIso H g).hom
  have hmap :
      (CommHopfAlgCat.mapPointsFunctor
        (CommHopfAlgCat.innerConjugationIso H g).hom).app A x = AlgHom.mapDomain f x := by
    rw [CommHopfAlgCat.mapPointsFunctor_app_apply, AlgHom.mapDomain_apply]
  rw [← CommHopfAlgCat.mapPointsFunctor_innerConjugationIso_hom_app_apply H g A x, hmap]
  have he : (BialgEquiv.ofBijective f hf).toBialgHom = f := by
    ext y
    exact congrFun (BialgEquiv.coe_ofBijective f hf) y
  rw [← he]
  rw [BialgEquiv.toBialgHom_eq_coe]
  rw [← AlgHom.mapDomainMulEquiv_apply (BialgEquiv.ofBijective f hf)]
  -- The generic transport theorem reconstructs the categorical object from its carrier; this
  -- `change` is only the residual `CommHopfAlgCat.of R ↑H` eta identification.
  change AlgHom.mapDomainMulEquiv (A := A) (BialgEquiv.ofBijective f hf) x ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R ↑H)
        (I.comapOfSurjective f hf.2) A ↔
    x ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R ↑H) I A
  exact CommHopfAlgCat.mapDomainMulEquiv_mem_quotientPointsSubgroup_comapOfSurjective_iff
    f hf.1 hf.2 I A x

/-- Conjugating a closed subgroup by the identity point does not change it. -/
@[simp]
theorem conjugate_one (I : HopfIdeal R H) :
    I.conjugate
        (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) = I := by
  ext x
  rw [mem_conjugate_iff, CommHopfAlgCat.innerConjugationIso_one]
  simp

/-- Successive conjugation first by `g` and then by `h` is conjugation by `h * g`, in the usual
order for the action by inner automorphisms. -/
@[simp]
theorem conjugate_conjugate (I : HopfIdeal R H)
    (g h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (I.conjugate g).conjugate h = I.conjugate (h * g) := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff, mem_conjugate_iff,
    CommHopfAlgCat.innerConjugationIso_mul]
  simp only [Iso.trans_hom, CategoryTheory.ConcreteCategory.comp_apply]

/-- Conjugating by `g⁻¹` undoes conjugation by `g`. -/
theorem conjugate_conjugate_inv (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (I.conjugate g).conjugate g⁻¹ = I := by
  rw [conjugate_conjugate, inv_mul_cancel g, conjugate_one]

/-- Conjugating by `g` undoes conjugation by `g⁻¹`. -/
theorem conjugate_inv_conjugate (I : HopfIdeal R H)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (I.conjugate g⁻¹).conjugate g = I := by
  rw [conjugate_conjugate, mul_inv_cancel g, conjugate_one]

/-- Conjugation by a rational point as an order automorphism of defining Hopf ideals. -/
noncomputable def conjugateOrderIso
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    HopfIdeal R H ≃o HopfIdeal R H :=
  comapOrderIso (BialgEquiv.ofBijective
    (CommHopfAlgCat.innerConjugationIso H g).hom.hom
    (ConcreteCategory.bijective_of_isIso
      (CommHopfAlgCat.innerConjugationIso H g).hom))

/-- Applying the conjugation order isomorphism conjugates the defining Hopf ideal. -/
@[simp]
theorem conjugateOrderIso_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (I : HopfIdeal R H) :
    conjugateOrderIso g I = I.conjugate g := by
  rw [conjugateOrderIso, comapOrderIso_apply]
  unfold conjugate
  rfl

/-- Applying the inverse conjugation order isomorphism conjugates by the inverse point. -/
@[simp]
theorem conjugateOrderIso_symm_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (I : HopfIdeal R H) :
    (conjugateOrderIso g).symm I = I.conjugate g⁻¹ := by
  apply (conjugateOrderIso g).injective
  rw [OrderIso.apply_symm_apply, conjugateOrderIso_apply, conjugate_inv_conjugate]

end HopfIdeal

end TauCeti
