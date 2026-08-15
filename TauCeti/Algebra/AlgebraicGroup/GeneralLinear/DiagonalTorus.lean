/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.RootSubgroup
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Scheme

/-!
# The diagonal torus of the general linear group scheme

The rank-`N` split torus has `A`-points `Fin N → Aˣ`, while the general linear group has
`A`-points `GL (Fin N) A`.  The diagonal embedding

```text
(t₀, …, tₙ₋₁) ↦ diag(t₀, …, tₙ₋₁)
```

is natural in the commutative `R`-algebra `A`.  This file uses full faithfulness of the functor of
points to recover its coordinate Hopf-algebra morphism, then applies relative spectrum to obtain
the group-scheme morphism `TauCeti.GeneralLinear.diagonalTorus`.

The diagonal torus acts on the root subgroup for `εᵢ - εⱼ` with that character.  On
algebra-valued points the pinning equation is

```text
t xᵢⱼ(c) t⁻¹ = xᵢⱼ(tᵢ c tⱼ⁻¹).
```

Thus the split maximal torus and the root subgroups of the worked `GLₙ` construction are linked
by the same equation required of a pinned Chevalley--Demazure group scheme.

## Main declarations

* `TauCeti.GeneralLinear.diagonalTorusPoints`: the diagonal embedding on algebra-valued points.
* `TauCeti.GeneralLinear.diagonalTorusCoordinateMap`: its coordinate Hopf-algebra morphism.
* `TauCeti.GeneralLinear.diagonalTorus`: the corresponding group-scheme morphism.
* `TauCeti.GeneralLinear.diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv`: the root-character
  conjugation equation.
* `TauCeti.GeneralLinear.schemePointsMulEquiv_diagonalTorus`: on scheme-valued points, composing
  with the diagonal torus morphism is the diagonal matrix of the coordinates.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
* The points-map, natural-transformation, coordinate-morphism, and relative-spectrum
  constructions are adapted from the formal template in
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.RootSubgroup`.

This is the split-torus and root-subgroup pinning equation in Layer 9 of
`TauCetiRoadmap/ReductiveGroups/README.md`, a prerequisite for milestone L0 of the
`CFSGStatement` roadmap.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.GeneralLinear

universe u w

variable {R : Type u} [CommRing R] {N : ℕ}

/-- Restrict a same-universe coordinate family on `ULift (Fin N)` to the canonical copy of
`Fin N`.  The universe lift is required only by the current same-universe group-scheme API. -/
def diagonalTorusCoordinates {A : Type w} [Monoid A] :
    (ULift.{u} (Fin N) → Aˣ) →* (Fin N → Aˣ) where
  toFun t i := t (ULift.up i)
  map_one' := rfl
  map_mul' _ _ := rfl

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- The diagonal-torus homomorphism on `A`-points.  Under the split-torus and general-linear
points equivalences it is the diagonal embedding `diagGL : (Fin N → Aˣ) →* GL (Fin N) A`. -/
noncomputable def diagonalTorusPoints :
    WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)) →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R N →ₐ[R] A) :=
  (pointsMulEquiv (R := R) (A := A) N).symm.toMonoidHom.comp
    ((diagGL (k := A) (n := N)).comp
      ((diagonalTorusCoordinates (N := N) (A := A)).comp
        (SplitTorus.pointsMulEquiv (R := R) (A := A)).toMonoidHom))

/-- Reading the image of a split-torus point as an invertible matrix gives the diagonal matrix
whose diagonal entries are the coordinates of that point. -/
-- Not `@[simp]`: `pointsMulEquiv_apply` already simplifies the left-hand side, so `simpNF`
-- rejects this higher-level equation as not being in normal form.
theorem pointsMulEquiv_diagonalTorusPoints
    (f : WithConv
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)) →ₐ[R] A)) :
    pointsMulEquiv N (diagonalTorusPoints f) =
      diagGL (diagonalTorusCoordinates (SplitTorus.pointsMulEquiv f)) := by
  simp [diagonalTorusPoints]

/-- The diagonal-torus homomorphism on points is injective. -/
theorem diagonalTorusPoints_injective :
    Function.Injective (diagonalTorusPoints (R := R) (N := N) (A := A)) := by
  intro f g h
  have hdiag :
      diagGL (diagonalTorusCoordinates (SplitTorus.pointsMulEquiv f)) =
        diagGL (diagonalTorusCoordinates (SplitTorus.pointsMulEquiv g)) := by
    rw [← pointsMulEquiv_diagonalTorusPoints, ← pointsMulEquiv_diagonalTorusPoints, h]
  have hcoordinates := diagGL_injective hdiag
  apply (SplitTorus.pointsMulEquiv (R := R) (A := A)).injective
  funext i
  simpa only [diagonalTorusCoordinates, MonoidHom.coe_mk, OneHom.coe_mk, ULift.up_down] using
    congrFun hcoordinates i.down

variable {B : Type w} [CommRing B] [Algebra R B]

/-- The diagonal embedding is natural in the value algebra. -/
-- Not `@[simp]`: `AlgHom.mapValue_apply` already simplifies the left-hand side, so `simpNF`
-- rejects this higher-level equation as not being in normal form.
theorem mapValue_diagonalTorusPoints (phi : A →ₐ[R] B)
    (f : WithConv
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)) →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R N) phi (diagonalTorusPoints f) =
      diagonalTorusPoints
        (AlgHom.mapValue
          (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) phi f) := by
  apply (pointsMulEquiv (R := R) (A := B) N).injective
  rw [pointsMulEquiv_mapValue N phi (diagonalTorusPoints f),
    pointsMulEquiv_diagonalTorusPoints, pointsMulEquiv_diagonalTorusPoints]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.GeneralLinearGroup.map_apply, diagGL_apply, ite_eq_left]
    exact (congrArg Units.val
      (SplitTorus.pointsMulEquiv_mapValue phi f (ULift.up i))).symm
  · simp [Matrix.GeneralLinearGroup.map_apply, diagGL_apply, hij]

/-- Conjugation by a diagonal-torus point acts on the root subgroup for `εᵢ - εⱼ` by
the corresponding character `t ↦ tᵢ tⱼ⁻¹`. -/
theorem diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv {i j : Fin N} (hij : i ≠ j)
    (t : WithConv
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)) →ₐ[R] A))
    (c : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    diagonalTorusPoints t * rootSubgroupPoints hij c * (diagonalTorusPoints t)⁻¹ =
      rootSubgroupPoints hij
        ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm <|
          Multiplicative.ofAdd
            ((SplitTorus.pointsMulEquiv (R := R) (A := A) t (ULift.up i) : A) *
              Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv c) *
              (((SplitTorus.pointsMulEquiv (R := R) (A := A) t
                (ULift.up j))⁻¹ : Aˣ) : A))) := by
  apply (pointsMulEquiv (R := R) (A := A) N).injective
  rw [map_mul, map_mul, map_inv, pointsMulEquiv_diagonalTorusPoints,
    pointsMulEquiv_rootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints]
  rw [MulEquiv.apply_symm_apply]
  simpa only [diagonalTorusCoordinates, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] using
    diagGL_mul_transvectionUnit_mul_inv hij
      (diagonalTorusCoordinates (SplitTorus.pointsMulEquiv t))
      (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv c))

end Points

section Functor

/-- The natural transformation of group-valued functors whose component sends a coordinate
family of units to the corresponding diagonal invertible matrix. -/
noncomputable def diagonalTorusPointsMap :
    HopfAlgebra.pointsFunctor
        (R := R)
        (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R N) where
  app A := GrpCat.ofHom (diagonalTorusPoints (A := A))
  naturality _ _ phi := by
    ext f
    exact (mapValue_diagonalTorusPoints phi.hom f).symm

/-- The component of the natural diagonal-torus map at a value algebra is
`diagonalTorusPoints`. -/
@[simp]
theorem diagonalTorusPointsMap_app (A : CommAlgCat.{w} R) :
    (diagonalTorusPointsMap (R := R) (N := N)).app A =
      GrpCat.ofHom diagonalTorusPoints :=
  (rfl)

end Functor

section Scheme

/-- The coordinate morphism of the diagonal torus, recovered from its natural action on points.
Its direction is opposite to the represented group-scheme morphism. -/
noncomputable def diagonalTorusCoordinateMap :
    coordinateHopfAlgebra R N ⟶
      _root_.CommHopfAlgCat.of R
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) :=
  ((CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).preimage
    (X := Opposite.op (_root_.CommHopfAlgCat.of R
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)))))
    (Y := Opposite.op (coordinateHopfAlgebra R N))
    (diagonalTorusPointsMap.{u, u} (R := R) (N := N) :
      HopfAlgebra.pointsFunctor
          (R := R)
          (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R N))).unop

/-- Precomposition by the diagonal-torus coordinate morphism is the previously constructed
natural map on convolution points. -/
theorem mapPointsFunctor_diagonalTorusCoordinateMap :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (diagonalTorusCoordinateMap (R := R) (N := N)) :
      HopfAlgebra.pointsFunctor
          (R := R)
          (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R N)) =
      (diagonalTorusPointsMap.{u, u} (R := R) (N := N) :
        HopfAlgebra.pointsFunctor
            (R := R)
            (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) ⟶
          HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R N)) := by
  unfold diagonalTorusCoordinateMap
  rw [← CommHopfAlgCat.pointsFunctor_map]
  exact Functor.map_preimage
    (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}) _

/-- On every same-universe value algebra, the map induced by the diagonal-torus coordinate
morphism is `diagonalTorusPoints`. -/
@[simp]
theorem mapPointsFunctor_diagonalTorusCoordinateMap_app
    (A : CommAlgCat.{u} R)
    (f : HopfAlgebra.points
      (R := R)
      (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) A) :
    (CommHopfAlgCat.mapPointsFunctor
      (diagonalTorusCoordinateMap (R := R) (N := N))).app A f =
      diagonalTorusPoints f := by
  rw [mapPointsFunctor_diagonalTorusCoordinateMap, diagonalTorusPointsMap_app]
  rfl

/-- The diagonal torus of `GLₙ`, as a morphism from the rank-`N` split torus group scheme. -/
noncomputable def diagonalTorus :
    SplitTorus.groupScheme R (ULift.{u} (Fin N)) ⟶ groupScheme R N :=
  eqToHom
      (DiagonalizableGroup.groupScheme_def R
        (SplitTorus.characterGroup (ULift.{u} (Fin N)))) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (diagonalTorusCoordinateMap (R := R) (N := N)).op ≫
    eqToHom (groupScheme_def R N).symm

/-- The diagonal-torus morphism is relative spectrum applied contravariantly to its coordinate
Hopf-algebra morphism, transported across the named source and target presentations. -/
theorem diagonalTorus_def :
    diagonalTorus (R := R) (N := N) =
      eqToHom
          (DiagonalizableGroup.groupScheme_def R
            (SplitTorus.characterGroup (ULift.{u} (Fin N)))) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (diagonalTorusCoordinateMap (R := R) (N := N)).op ≫
        eqToHom (groupScheme_def R N).symm := by
  unfold diagonalTorus
  rfl

section SchemePoints

variable (A : Type u) [CommRing A] [Algebra R A]

/-- **The diagonal torus on scheme-valued points**: composing an `A`-point of the split torus
with the diagonal torus morphism gives the diagonal invertible matrix whose diagonal entries are
the coordinates of that point. -/
@[simp]
theorem schemePointsMulEquiv_diagonalTorus
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      (SplitTorus.groupScheme R (ULift.{u} (Fin N))).X) :
    schemePointsMulEquiv N A (p ≫ (diagonalTorus (R := R) (N := N)).hom.hom) =
      diagGL (diagonalTorusCoordinates (SplitTorus.schemePointsMulEquiv (R := R) (A := A) p)) := by
  let q := DiagonalizableGroup.groupSchemePointsMulEquiv (R := R) (A := A)
    (SplitTorus.characterGroup (ULift.{u} (Fin N))) p
  have hcomp_point : p ≫ (diagonalTorus (R := R) (N := N)).hom.hom =
      groupSchemePointMulEquiv N A (diagonalTorusPoints q) := by
    have hmap := CommHopfAlgCat.mapMulEquiv_mapDomain (CommAlgCat.of R A)
      (diagonalTorusCoordinateMap (R := R) (N := N)) q
    rw [mapPointsFunctor_diagonalTorusCoordinateMap_app] at hmap
    have eqToHom_left {G G' : Grp (Over (Spec (CommRingCat.of R)))} (h : G = G') :
        (eqToHom h).hom.hom.left =
          eqToHom (congrArg (fun K : Grp (Over (Spec (CommRingCat.of R))) ↦ K.X.left) h) := by
      subst h
      rfl
    apply Over.OverMorphism.ext
    rw [groupSchemePointMulEquiv_apply_left, Over.comp_left]
    rw [diagonalTorus_def]
    rw [show ((eqToHom (DiagonalizableGroup.groupScheme_def R
        (SplitTorus.characterGroup (ULift.{u} (Fin N)))) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (diagonalTorusCoordinateMap (R := R) (N := N)).op ≫
        eqToHom (groupScheme_def R N).symm)).hom.hom.left =
      (eqToHom (DiagonalizableGroup.groupScheme_def R
        (SplitTorus.characterGroup (ULift.{u} (Fin N))))).hom.hom.left ≫
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (diagonalTorusCoordinateMap (R := R) (N := N)).op).hom.hom.left ≫
        (eqToHom (groupScheme_def R N).symm).hom.hom.left from rfl]
    rw [eqToHom_left, eqToHom_left]
    change p.left ≫ eqToHom (DiagonalizableGroup.groupScheme_X_left R
        (SplitTorus.characterGroup (ULift.{u} (Fin N)))) ≫
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (diagonalTorusCoordinateMap (R := R) (N := N)).op).hom.hom.left ≫
        eqToHom (groupScheme_X_left R N).symm =
      (AlgebraicGeometry.Spec.mapMulEquiv (diagonalTorusPoints q)).left ≫
        eqToHom (groupScheme_X_left R N).symm
    rw [← Category.assoc p.left,
      DiagonalizableGroup.groupSchemePointsMulEquiv_apply_left_comp]
    change Spec.map (CommRingCat.ofHom q.ofConv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (diagonalTorusCoordinateMap (R := R) (N := N)).hom.toAlgHom.toRingHom) ≫
        eqToHom (groupScheme_X_left R N).symm =
      Spec.map (CommRingCat.ofHom (diagonalTorusPoints q).ofConv.toRingHom) ≫
        eqToHom (groupScheme_X_left R N).symm
    have hmapLeft :
        (AlgebraicGeometry.Spec.mapMulEquiv (diagonalTorusPoints q)).left =
          (AlgebraicGeometry.Spec.mapMulEquiv q).left ≫
            ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
              (diagonalTorusCoordinateMap (R := R) (N := N)).op).hom.hom.left :=
      congrArg Over.Hom.left hmap
    change Spec.map (CommRingCat.ofHom (diagonalTorusPoints q).ofConv.toRingHom) =
      Spec.map (CommRingCat.ofHom q.ofConv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (diagonalTorusCoordinateMap (R := R) (N := N)).hom.toAlgHom.toRingHom) at hmapLeft
    rw [← Category.assoc, ← hmapLeft]
  have hGL : schemePointsMulEquiv N A
      (groupSchemePointMulEquiv N A (diagonalTorusPoints q)) =
      pointsMulEquiv N (diagonalTorusPoints q) := by
    apply (schemePointsMulEquiv (R := R) N A).symm.injective
    rw [MulEquiv.symm_apply_apply, schemePointsMulEquiv_symm_apply,
      MulEquiv.symm_apply_apply]
  have hTorus : SplitTorus.schemePointsMulEquiv (R := R) (A := A) p =
      SplitTorus.pointsMulEquiv q := by
    ext i
    exact (SplitTorus.schemePointsMulEquiv_apply_coe p i).trans
      (SplitTorus.pointsMulEquiv_apply_coe q i).symm
  rw [hcomp_point, hGL, hTorus, pointsMulEquiv_diagonalTorusPoints]

end SchemePoints

end Scheme

end TauCeti.GeneralLinear
