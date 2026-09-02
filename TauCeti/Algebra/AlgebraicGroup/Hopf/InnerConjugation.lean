/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Conjugation

/-!
# Inner conjugation in Hopf coordinates

A rational point `g` of an affine group acts on all algebra-valued points by inner
conjugation. This action is natural in the value algebra and is a group automorphism. Full
faithfulness of the functor of points therefore recovers a coordinate Hopf-algebra
automorphism.

The coordinate morphism is characterized both on arbitrary algebra-valued points and as an
algebra map. The latter is evaluation of the universal conjugation morphism at `g` in its first
factor:

```text
H --conj#--> H ⊗ H --(g ⊗ id)--> H.
```

## Main declarations

* `TauCeti.CommHopfAlgCat.innerConjugationPointIso`: inner conjugation on the functor of points.
* `TauCeti.CommHopfAlgCat.innerConjugationIso`: the corresponding coordinate Hopf-algebra
  automorphism.
* `TauCeti.CommHopfAlgCat.innerConjugationIso_hom_toAlgHom`: its explicit coordinate formula.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§3.5 and 10.20.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §8.

This is the conjugation operation needed by Layer 7, "Borel subgroups, maximal tori, and their
conjugacy", of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R]
variable (H : _root_.CommHopfAlgCat.{u} R)

/-- Extension of an `R`-valued point to an `A`-valued point along the structure map of `A`. -/
noncomputable def extendPoint (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    HopfAlgebra.points (R := R) (H := H) A :=
  AlgHom.mapValue (Algebra.ofId R A) g

/-- Extending a point to its original value algebra does not change it. -/
@[simp]
theorem extendPoint_self
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    extendPoint H (CommAlgCat.of R R) g = g := by
  apply WithConv.ofConv_injective
  ext x
  simp [extendPoint]

/-- The identity rational point extends to the identity point. -/
@[simp]
theorem extendPoint_one (A : CommAlgCat.{u} R) :
    extendPoint H A (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) = 1 := by
  exact (AlgHom.mapValue (H := H) (Algebra.ofId R A)).map_one

/-- Extension of rational points preserves multiplication. -/
@[simp]
theorem extendPoint_mul (A : CommAlgCat.{u} R)
    (g h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    extendPoint H A (g * h) = extendPoint H A g * extendPoint H A h := by
  exact (AlgHom.mapValue (H := H) (Algebra.ofId R A)).map_mul g h

/-- Extension of rational points preserves inverses. -/
@[simp]
theorem extendPoint_inv (A : CommAlgCat.{u} R)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    extendPoint H A g⁻¹ = (extendPoint H A g)⁻¹ := by
  exact (AlgHom.mapValue (H := H) (Algebra.ofId R A)).map_inv g

/-- Extension of a ground-ring-valued point is natural in the value algebra. -/
theorem mapPoints_extendPoint {A B : CommAlgCat.{u} R} (f : A ⟶ B)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    HopfAlgebra.mapPoints (H := H) f (extendPoint H A g) = extendPoint H B g := by
  apply WithConv.ofConv_injective
  ext x
  change f.hom (algebraMap R A (g.ofConv x)) = algebraMap R B (g.ofConv x)
  exact f.hom.commutes (g.ofConv x)

/-- Conjugation by the extension of a rational point, as an automorphism of `A`-valued points. -/
noncomputable def innerConjugationPointIso
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{u} R) :
    (HopfAlgebra.pointsFunctor (R := R) (H := H)).obj A ≅
      (HopfAlgebra.pointsFunctor (R := R) (H := H)).obj A :=
  MulEquiv.toGrpIso (MulAut.conj (extendPoint H A g))

/-- Inner conjugation acts by `x ↦ g * x * g⁻¹` after extending `g` to the value algebra. -/
@[simp]
theorem innerConjugationPointIso_hom_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{u} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (innerConjugationPointIso H g A).hom x =
      extendPoint H A g * x * (extendPoint H A g)⁻¹ := by
  rfl

/-- The inverse inner-conjugation map is conjugation by the inverse point. -/
@[simp]
theorem innerConjugationPointIso_inv_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{u} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (innerConjugationPointIso H g A).inv x =
      extendPoint H A g⁻¹ * x * extendPoint H A g := by
  rfl

/-- Conjugation by a rational point, naturally on the full functor of points. -/
noncomputable def innerConjugationPointsIso
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    HopfAlgebra.pointsFunctor (R := R) (H := H) ≅
      HopfAlgebra.pointsFunctor (R := R) (H := H) :=
  NatIso.ofComponents (innerConjugationPointIso H g) fun {A B} f ↦ by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    let x' : HopfAlgebra.points (R := R) (H := H) A := x
    change (innerConjugationPointIso H g B).hom (HopfAlgebra.mapPoints (H := H) f x') =
      HopfAlgebra.mapPoints (H := H) f ((innerConjugationPointIso H g A).hom x')
    rw [innerConjugationPointIso_hom_apply, innerConjugationPointIso_hom_apply,
      HopfAlgebra.mapPoints_mul, HopfAlgebra.mapPoints_mul, HopfAlgebra.mapPoints_inv,
      mapPoints_extendPoint]

/-- Conjugation by the identity point is the identity automorphism of the functor of points. -/
@[simp]
theorem innerConjugationPointsIso_one :
    innerConjugationPointsIso H
        (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) =
      Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  let x' : HopfAlgebra.points (R := R) (H := H) A := x
  change extendPoint H A 1 * x' * (extendPoint H A 1)⁻¹ = x'
  simp

/-- Conjugation by an inverse point is inverse to conjugation by the original point. -/
@[simp]
theorem innerConjugationPointsIso_inv
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationPointsIso H g⁻¹ = (innerConjugationPointsIso H g).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  let x' : HopfAlgebra.points (R := R) (H := H) A := x
  change extendPoint H A g⁻¹ * x' * (extendPoint H A g⁻¹)⁻¹ =
    (innerConjugationPointIso H g A).inv x'
  rw [innerConjugationPointIso_inv_apply]
  have h : (extendPoint H A g⁻¹)⁻¹ = extendPoint H A g := by
    calc
      (extendPoint H A g⁻¹)⁻¹ = extendPoint H A (g⁻¹)⁻¹ := (extendPoint_inv H A g⁻¹).symm
      _ = extendPoint H A g := by rw [inv_inv]
  rw [h]

/-- The coordinate Hopf-algebra automorphism representing conjugation by a rational point.

Contravariance means that its underlying coordinate map is the pullback of the pointwise inner
automorphism. -/
noncomputable def innerConjugationIso
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) : H ≅ H where
  hom := homOfPointsMap (innerConjugationPointsIso H g).hom
  inv := homOfPointsMap (innerConjugationPointsIso H g).inv
  hom_inv_id := by
    rw [← homOfPointsMap_comp, Iso.inv_hom_id, homOfPointsMap_id]
  inv_hom_id := by
    rw [← homOfPointsMap_comp, Iso.hom_inv_id, homOfPointsMap_id]

/-- Conjugation by the identity point is the identity coordinate Hopf-algebra automorphism. -/
@[simp]
theorem innerConjugationIso_one :
    innerConjugationIso H
        (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) =
      Iso.refl H := by
  apply Iso.ext
  change homOfPointsMap (innerConjugationPointsIso H 1).hom = 𝟙 H
  rw [innerConjugationPointsIso_one]
  exact homOfPointsMap_id H

/-- The coordinate automorphism for conjugation by an inverse point is the inverse coordinate
automorphism. -/
@[simp]
theorem innerConjugationIso_inv
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationIso H g⁻¹ = (innerConjugationIso H g).symm := by
  apply Iso.ext
  change homOfPointsMap (innerConjugationPointsIso H g⁻¹).hom =
    homOfPointsMap (innerConjugationPointsIso H g).inv
  rw [innerConjugationPointsIso_inv]
  rfl

/-- Precomposition by the coordinate inner automorphism is pointwise conjugation. -/
@[simp]
theorem mapPointsFunctor_innerConjugationIso_hom
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    mapPointsFunctor (innerConjugationIso H g).hom =
      (innerConjugationPointsIso H g).hom := by
  exact mapPointsFunctor_homOfPointsMap _

/-- On points, the coordinate inner automorphism acts by conjugation by the extended rational
point. -/
@[simp]
theorem mapPointsFunctor_innerConjugationIso_hom_app_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{u} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (mapPointsFunctor (innerConjugationIso H g).hom).app A x =
      extendPoint H A g * x * (extendPoint H A g)⁻¹ := by
  rw [mapPointsFunctor_innerConjugationIso_hom]
  exact innerConjugationPointIso_hom_apply H g A x

/-- The coordinate algebra map of inner conjugation is obtained from the universal conjugation
map by evaluating its conjugating variable at the given rational point. -/
theorem innerConjugationIso_hom_toAlgHom
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (innerConjugationIso H g).hom.hom.toAlgHom =
      (Algebra.TensorProduct.productMap
        ((Algebra.ofId R H).comp g.ofConv) (AlgHom.id R H)).comp
          (HopfAlgebra.conjugationAlgHom (R := R) (H := H)) := by
  apply AlgHom.ext
  intro x
  have hpoint := mapPointsFunctor_innerConjugationIso_hom_app_apply H g
    (CommAlgCat.of R H) (toConv (AlgHom.id R H))
  have hx := congrArg (fun p : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R H) ↦
    p.ofConv x) hpoint
  rw [mapPointsFunctor_app_apply] at hx
  calc
    (innerConjugationIso H g).hom.hom.toAlgHom x =
        (extendPoint H (CommAlgCat.of R H) g * toConv (AlgHom.id R H) *
          (extendPoint H (CommAlgCat.of R H) g)⁻¹).ofConv x := by
      simpa only [AlgHom.comp_apply, AlgHom.id_apply, WithConv.toConv_ofConv] using hx
    _ = (Algebra.TensorProduct.productMap
          ((Algebra.ofId R H).comp g.ofConv) (AlgHom.id R H)).comp
            (HopfAlgebra.conjugationAlgHom (R := R) (H := H)) x := by
      simpa only [extendPoint, AlgHom.mapValue_apply, WithConv.ofConv_toConv] using
        DFunLike.congr_fun
          (HopfAlgebra.productMap_comp_conjugationAlgHom (R := R) (H := H)
            (toConv ((Algebra.ofId R H).comp g.ofConv)) (toConv (AlgHom.id R H))).symm x

end TauCeti.CommHopfAlgCat
