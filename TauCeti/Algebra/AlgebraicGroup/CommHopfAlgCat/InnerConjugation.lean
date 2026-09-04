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

* `TauCeti.CommHopfAlgCat.innerConjugationPointIso`: inner conjugation on `A`-valued points.
* `TauCeti.CommHopfAlgCat.innerConjugationPointNatIso`: inner conjugation naturally on the
  functor of points.
* `TauCeti.CommHopfAlgCat.innerConjugationIso`: the corresponding coordinate Hopf-algebra
  automorphism.
* `TauCeti.CommHopfAlgCat.innerConjugationIso_hom_toAlgHom`: its explicit coordinate formula.
* `TauCeti.CommHopfAlgCat.mapPointsFunctor_innerConjugationIso_hom_app_apply`: its action on
  arbitrary algebra-valued points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§3.5 and 10.20.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §8.
-/

public section

open CategoryTheory TauCeti.HopfAlgebra WithConv

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} [CommRing R]
variable (H : _root_.CommHopfAlgCat.{u} R)

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

/-- The inverse inner-conjugation map is conjugation by the inverse of the extended point. -/
@[simp]
theorem innerConjugationPointIso_inv_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (innerConjugationPointIso H g A).inv x =
      (extendPoint H A g)⁻¹ * x * extendPoint H A g := by
  rfl

/-- Conjugation by a rational point, naturally on the full functor of points. -/
noncomputable def innerConjugationPointNatIso
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
    rw [HopfAlgebra.mapPoints_mul, HopfAlgebra.mapPoints_mul, HopfAlgebra.mapPoints_inv,
      HopfAlgebra.mapPoints_extendPoint]

/-- The forward component of the natural inner-conjugation isomorphism acts by conjugation. -/
@[simp]
theorem innerConjugationPointNatIso_hom_app_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (innerConjugationPointNatIso H g).hom.app A x =
      extendPoint H A g * x * (extendPoint H A g)⁻¹ :=
  innerConjugationPointIso_hom_apply H g A x

/-- The inverse component of the natural inner-conjugation isomorphism acts by conjugation by
the inverse extended point. -/
@[simp]
theorem innerConjugationPointNatIso_inv_app_apply
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R))
    (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A) :
    (innerConjugationPointNatIso H g).inv.app A x =
      (extendPoint H A g)⁻¹ * x * extendPoint H A g :=
  innerConjugationPointIso_inv_apply H g A x

private theorem pointNatIso_ext
    {e₁ e₂ : HopfAlgebra.pointsFunctor.{u, u, v} (R := R) (H := H) ≅
      HopfAlgebra.pointsFunctor.{u, u, v} (R := R) (H := H)}
    (h : ∀ (A : CommAlgCat.{v} R) (x : HopfAlgebra.points (R := R) (H := H) A),
      e₁.hom.app A x = e₂.hom.app A x) : e₁ = e₂ := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  exact h A

/-- Conjugation by the identity point is the identity automorphism of the functor of points. -/
@[simp]
theorem innerConjugationPointNatIso_one :
    innerConjugationPointNatIso H
        (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) =
      Iso.refl _ := by
  apply pointNatIso_ext
  intro A x
  rw [innerConjugationPointNatIso_hom_app_apply]
  simp only [map_one, inv_one, one_mul, mul_one]
  exact Eq.refl _

/-- Conjugation by a product is successive conjugation, first by the second point and then by the
first. -/
@[simp]
theorem innerConjugationPointNatIso_mul
    (g h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationPointNatIso H (g * h) =
      (innerConjugationPointNatIso H h).trans (innerConjugationPointNatIso H g) := by
  apply pointNatIso_ext
  intro A x
  rw [innerConjugationPointNatIso_hom_app_apply]
  -- After extensionality, this is the residual application rule for the composite `GrpCat`
  -- morphism stored by `Iso.trans`; the following rewrites use the public component equations.
  change extendPoint H A (g * h) * x * (extendPoint H A (g * h))⁻¹ =
    (innerConjugationPointNatIso H g).hom.app A
      ((innerConjugationPointNatIso H h).hom.app A x)
  rw [innerConjugationPointNatIso_hom_app_apply,
    innerConjugationPointNatIso_hom_app_apply]
  simp only [map_mul, mul_inv_rev, mul_assoc]

/-- Conjugation by an inverse point is inverse to conjugation by the original point. -/
@[simp]
theorem innerConjugationPointNatIso_inv_point
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationPointNatIso H g⁻¹ = (innerConjugationPointNatIso H g).symm := by
  apply pointNatIso_ext
  intro A x
  rw [innerConjugationPointNatIso_hom_app_apply, Iso.symm_hom,
    innerConjugationPointNatIso_inv_app_apply, map_inv, inv_inv]

/-- The coordinate Hopf-algebra automorphism representing conjugation by a rational point.

Contravariance means that its underlying coordinate map is the pullback of the pointwise inner
automorphism. -/
noncomputable def innerConjugationIso
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) : H ≅ H where
  hom := homOfPointsMap (innerConjugationPointNatIso H g).hom
  inv := homOfPointsMap (innerConjugationPointNatIso H g).inv
  hom_inv_id := by
    rw [← homOfPointsMap_comp, Iso.inv_hom_id, homOfPointsMap_id]
  inv_hom_id := by
    rw [← homOfPointsMap_comp, Iso.hom_inv_id, homOfPointsMap_id]

private theorem innerConjugationIso_hom_def
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (innerConjugationIso H g).hom = homOfPointsMap (innerConjugationPointNatIso H g).hom :=
  (rfl)

private theorem innerConjugationIso_inv_def
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    (innerConjugationIso H g).inv = homOfPointsMap (innerConjugationPointNatIso H g).inv :=
  (rfl)

/-- Conjugation by the identity point is the identity coordinate Hopf-algebra automorphism. -/
@[simp]
theorem innerConjugationIso_one :
    innerConjugationIso H
        (1 : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) =
      Iso.refl H := by
  apply Iso.ext
  rw [innerConjugationIso_hom_def]
  rw [innerConjugationPointNatIso_one]
  exact homOfPointsMap_id H

/-- Coordinate pullback reverses the pointwise composition order: the coordinate automorphism for
conjugation by `g * h` is the composite for `g` followed by the one for `h`. -/
@[simp]
theorem innerConjugationIso_mul
    (g h : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationIso H (g * h) =
      (innerConjugationIso H g).trans (innerConjugationIso H h) := by
  apply Iso.ext
  rw [innerConjugationIso_hom_def, Iso.trans_hom, innerConjugationIso_hom_def,
    innerConjugationIso_hom_def]
  have hmul := congrArg Iso.hom (innerConjugationPointNatIso_mul H g h)
  simp only [Iso.trans_hom] at hmul
  rw [hmul, homOfPointsMap_comp]

/-- The coordinate automorphism for conjugation by an inverse point is the inverse coordinate
automorphism. -/
@[simp]
theorem innerConjugationIso_inv_point
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) :
    innerConjugationIso H g⁻¹ = (innerConjugationIso H g).symm := by
  apply Iso.ext
  rw [innerConjugationIso_hom_def, Iso.symm_hom, innerConjugationIso_inv_def,
    innerConjugationPointNatIso_inv_point, Iso.symm_hom]

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
    rw [innerConjugationIso_hom_def, mapPointsFunctor_homOfPointsMap]
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
      have hext : extendPoint H (CommAlgCat.of R H) g =
          toConv ((Algebra.ofId R H).comp g.ofConv) := by
        apply WithConv.ofConv_injective
        ext y
        exact HopfAlgebra.extendPoint_ofConv H (CommAlgCat.of R H) g y
      rw [hext]
      exact
        DFunLike.congr_fun
          (HopfAlgebra.productMap_comp_conjugationAlgHom (R := R) (H := H)
            (toConv ((Algebra.ofId R H).comp g.ofConv)) (toConv (AlgHom.id R H))).symm x

/-- On points over any commutative value algebra, the coordinate inner automorphism acts by
conjugation by the extended rational point. -/
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
      AlgHom.id_apply,
      Algebra.ofId_apply, map_mul]
    rw [HopfAlgebra.extendPoint_ofConv]
    exact congrArg (fun c : A ↦ c * x.ofConv b) (x.ofConv.commutes (g.ofConv a))
  rw [hprod]
  exact (HopfAlgebra.productMap_comp_conjugationAlgHom (R := R) (H := H)
    (extendPoint H A g) x)

end TauCeti.CommHopfAlgCat
