/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda

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
-/

public section

open CategoryTheory WithConv

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} [CommRing R]
variable (H : _root_.CommHopfAlgCat.{u} R)

/-- Extension of an `R`-valued point to an `A`-valued point along the structure map of `A`. -/
noncomputable def extendPoint (A : CommAlgCat.{v} R)
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
theorem extendPoint_one (A : CommAlgCat.{v} R) :
    extendPoint H A (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) = 1 := by
  exact (AlgHom.mapValue (H := H) (Algebra.ofId R A)).map_one

/-- Extension of rational points preserves multiplication. -/
@[simp]
theorem extendPoint_mul (A : CommAlgCat.{v} R)
    (g h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    extendPoint H A (g * h) = extendPoint H A g * extendPoint H A h := by
  exact (AlgHom.mapValue (H := H) (Algebra.ofId R A)).map_mul g h

/-- Extension of rational points preserves inverses. -/
@[simp]
theorem extendPoint_inv (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    extendPoint H A g⁻¹ = (extendPoint H A g)⁻¹ := by
  exact (AlgHom.mapValue (H := H) (Algebra.ofId R A)).map_inv g

/-- Extension of a ground-ring-valued point is natural in the value algebra. -/
theorem mapPoints_extendPoint {A : CommAlgCat.{v} R} {B : CommAlgCat.{w} R}
    (f : A →ₐ[R] B)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    AlgHom.mapValue (H := H) f (extendPoint H A g) = extendPoint H B g := by
  apply WithConv.ofConv_injective
  ext x
  simp only [extendPoint, AlgHom.mapValue_apply,
    WithConv.ofConv_toConv, AlgHom.comp_apply]
  exact f.commutes (g.ofConv x)

/-- Mapping a conjugate by an extended rational point commutes with extension to the target value
algebra. This isolates the group-homomorphism normalization used in the naturality proof below. -/
private theorem mapPoints_conjugate_extendPoint {A B : CommAlgCat.{v} R} (f : A ⟶ B)
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (x : HopfAlgebra.points (R := R) (H := H) A) :
    HopfAlgebra.mapPoints (H := H) f
        (extendPoint H A g * x * (extendPoint H A g)⁻¹) =
      extendPoint H B g * HopfAlgebra.mapPoints (H := H) f x * (extendPoint H B g)⁻¹ := by
  rw [HopfAlgebra.mapPoints_mul, HopfAlgebra.mapPoints_mul, HopfAlgebra.mapPoints_inv]
  rw [show HopfAlgebra.mapPoints (H := H) f (extendPoint H A g) = extendPoint H B g from
    mapPoints_extendPoint H f.hom g]

/-- Conjugation by the extension of a rational point, as an automorphism of `A`-valued points. -/
noncomputable def innerConjugationPointIso
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) :
    (HopfAlgebra.pointsFunctor (R := R) (H := H)).obj A ≅
      (HopfAlgebra.pointsFunctor (R := R) (H := H)).obj A :=
  MulEquiv.toGrpIso (MulAut.conj (extendPoint H A g))

/-- Inner conjugation acts by `x ↦ g * x * g⁻¹` after extending `g` to the value algebra. -/
@[simp]
theorem innerConjugationPointIso_hom_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (innerConjugationPointIso H g A).hom x =
      extendPoint H A g * x * (extendPoint H A g)⁻¹ := by
  rfl

/-- The inverse inner-conjugation map is conjugation by the inverse point. -/
@[simp]
theorem innerConjugationPointIso_inv_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (innerConjugationPointIso H g A).inv x =
      extendPoint H A g⁻¹ * x * extendPoint H A g := by
  rfl

/-- Conjugation by a rational point, naturally on the full functor of points. -/
noncomputable def innerConjugationPointsIso
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    HopfAlgebra.pointsFunctor.{u, u, v} (R := R) (H := H) ≅
      HopfAlgebra.pointsFunctor.{u, u, v} (R := R) (H := H) :=
  NatIso.ofComponents (innerConjugationPointIso H g) fun {A B} f ↦ by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    let x' : HopfAlgebra.points (R := R) (H := H) A := x
    -- `NatIso.ofComponents` stores this naturality square through the categorical wrappers for
    -- `GrpCat`; expose its pointwise form so the named point-map laws apply.
    change (innerConjugationPointIso H g B).hom (HopfAlgebra.mapPoints (H := H) f x') =
      HopfAlgebra.mapPoints (H := H) f ((innerConjugationPointIso H g A).hom x')
    rw [innerConjugationPointIso_hom_apply, innerConjugationPointIso_hom_apply]
    exact (mapPoints_conjugate_extendPoint H f g x').symm

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
  -- The components of `innerConjugationPointsIso` are stored as `GrpCat` morphisms; expose the
  -- underlying conjugation formula before applying its computation lemma.
  change extendPoint H A 1 * x' * (extendPoint H A 1)⁻¹ = x'
  simp only [extendPoint_one, inv_one, one_mul, mul_one]

/-- Conjugation by a product is successive conjugation, first by the second point and then by the
first. -/
@[simp]
theorem innerConjugationPointsIso_mul
    (g h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationPointsIso H (g * h) =
      (innerConjugationPointsIso H h).trans (innerConjugationPointsIso H g) := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  let x' : HopfAlgebra.points (R := R) (H := H) A := x
  -- As above, remove only the `NatIso.ofComponents`/`GrpCat` wrappers to compare the two
  -- conjugation automorphisms on an arbitrary point.
  change (MulAut.conj (extendPoint H A (g * h))) x' =
    (MulAut.conj (extendPoint H A g)) ((MulAut.conj (extendPoint H A h)) x')
  rw [extendPoint_mul]
  exact congrArg (fun f : MulAut _ ↦ f x') ((MulAut.conj : _ →* MulAut _).map_mul
    (extendPoint H A g) (extendPoint H A h))

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
  -- The two sides are hidden behind the component projections of the natural isomorphisms;
  -- expose the pointwise formulas so the named hom/inverse computation lemmas apply.
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
  -- `innerConjugationIso` is assembled fieldwise from the recovered coordinate maps, so expose
  -- its `hom` field before applying their identity law.
  change homOfPointsMap (innerConjugationPointsIso H 1).hom = 𝟙 H
  rw [innerConjugationPointsIso_one]
  exact homOfPointsMap_id H

/-- Coordinate pullback reverses the pointwise composition order: the coordinate automorphism for
conjugation by `g * h` is the composite for `g` followed by the one for `h`. -/
@[simp]
theorem innerConjugationIso_mul
    (g h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationIso H (g * h) =
      (innerConjugationIso H g).trans (innerConjugationIso H h) := by
  apply Iso.ext
  -- Expose the `homOfPointsMap` fields so its explicit contravariant composition law applies.
  change homOfPointsMap (innerConjugationPointsIso H (g * h)).hom =
    homOfPointsMap (innerConjugationPointsIso H g).hom ≫
      homOfPointsMap (innerConjugationPointsIso H h).hom
  have hmul := congrArg Iso.hom (innerConjugationPointsIso_mul H g h)
  simp only [Iso.trans_hom] at hmul
  rw [hmul, homOfPointsMap_comp]

/-- The coordinate automorphism for conjugation by an inverse point is the inverse coordinate
automorphism. -/
@[simp]
theorem innerConjugationIso_inv
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationIso H g⁻¹ = (innerConjugationIso H g).symm := by
  apply Iso.ext
  -- As in the identity and multiplication laws, expose the fieldwise construction before using
  -- the corresponding functor-of-points equality.
  change homOfPointsMap (innerConjugationPointsIso H g⁻¹).hom =
    homOfPointsMap (innerConjugationPointsIso H g).inv
  rw [innerConjugationPointsIso_inv]
  rfl

/-- Precomposition by the coordinate inner automorphism is pointwise conjugation. -/
@[simp]
theorem mapPointsFunctor_innerConjugationIso_hom
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (mapPointsFunctor (innerConjugationIso H g).hom :
      HopfAlgebra.pointsFunctor.{u, u, u} (R := R) (H := H) ⟶
        HopfAlgebra.pointsFunctor.{u, u, u} (R := R) (H := H)) =
      (innerConjugationPointsIso.{u, u} H g).hom := by
  exact mapPointsFunctor_homOfPointsMap _

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
  have hpoint :
      (mapPointsFunctor (innerConjugationIso H g).hom).app (CommAlgCat.of R H)
          (toConv (AlgHom.id R H)) =
        extendPoint H (CommAlgCat.of R H) g * toConv (AlgHom.id R H) *
          (extendPoint H (CommAlgCat.of R H) g)⁻¹ := by
    rw [mapPointsFunctor_innerConjugationIso_hom]
    exact innerConjugationPointIso_hom_apply H g _ _
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

/-- On points over any commutative value algebra, the coordinate inner automorphism acts by
conjugation by the extended rational point. -/
-- Not `@[simp]`: `mapPointsFunctor_innerConjugationIso_hom` is the preferred same-universe rule.
theorem mapPointsFunctor_innerConjugationIso_hom_app_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (mapPointsFunctor (innerConjugationIso H g).hom).app A x =
      extendPoint H A g * x * (extendPoint H A g)⁻¹ := by
  apply WithConv.ofConv_injective
  rw [mapPointsFunctor_app_apply]
  rw [innerConjugationIso_hom_toAlgHom]
  rw [← AlgHom.comp_assoc]
  have hprod :
      x.ofConv.comp (Algebra.TensorProduct.productMap
          ((Algebra.ofId R H).comp g.ofConv) (AlgHom.id R H)) =
        Algebra.TensorProduct.productMap (extendPoint H A g).ofConv x.ofConv := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply,
      AlgHom.id_apply, extendPoint, AlgHom.mapValue_apply, WithConv.ofConv_toConv,
      Algebra.ofId_apply, map_mul]
    exact congrArg (fun c : A ↦ c * x.ofConv b) (x.ofConv.commutes (g.ofConv a))
  rw [hprod]
  exact (HopfAlgebra.productMap_comp_conjugationAlgHom (R := R) (H := H)
    (extendPoint H A g) x)

end TauCeti.CommHopfAlgCat
