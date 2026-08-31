/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal

/-!
# The diagonal torus of the symplectic group scheme

This file promotes the diagonal symplectic matrices

```text
diag(t₀, …, tₘ₋₁, t₀⁻¹, …, tₘ₋₁⁻¹)
```

to a morphism from the rank-`m` split torus to `Sp₂ₘ` over an arbitrary commutative base
ring. The construction is made simultaneously in the functor-of-points, coordinate-Hopf-algebra,
and affine-group-scheme models. On algebra-valued points it is injective, natural in the value
algebra, and conjugates each symplectic root subgroup through its standard root character.

This is the torus and pinning-equation part of the standard type-`C` pinning. It does not yet claim
that the morphism is a closed immersion or that its image is maximal; those statements require the
coordinate-surjectivity and root-datum work that remain in Layer 9.

## Main definitions

* `TauCeti.Symplectic.diagonalTorusPoints`: the diagonal-torus homomorphism on algebra-valued
  points.
* `TauCeti.Symplectic.diagonalTorusCoordinateMap`: the corresponding coordinate Hopf-algebra map.
* `TauCeti.Symplectic.diagonalTorus`: the group-scheme morphism from the split torus to `Sp₂ₘ`.

## Main results

* `TauCeti.Symplectic.pointsMulEquiv_diagonalTorusPoints`: the point map is the standard diagonal
  symplectic matrix.
* `TauCeti.Symplectic.diagonalTorusPoints_injective` and
  `TauCeti.Symplectic.mapValue_diagonalTorusPoints`: injectivity and naturality.
* `TauCeti.Symplectic.diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv`: the pinning equation on
  every root subgroup.

## References

* J. S. Milne, *Algebraic Groups* (2017), §23 and §24.6.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.

This advances the pinnings and root-subgroup-map targets of Layer 9 in
`TauCetiRoadmap/ReductiveGroups/README.md`. The resulting type-`C` pinning is consumed by milestone
L0, "pinned ambient groups", of `TauCetiRoadmap/CFSGStatement/README.md` for the `Cₙ(q)` family.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.Symplectic

universe u v w

variable {R : Type u} [CommRing R] {m : ℕ}

section Points

variable {A : Type w} [CommRing A] [Algebra R A]

/-- **The diagonal torus of `Sp₂ₘ` on algebra-valued points.** Under the split-torus and
symplectic points equivalences it is the standard diagonal matrix with paired inverse entries. -/
noncomputable def diagonalTorusPoints :
    WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R m →ₐ[R] A) :=
  (pointsMulEquiv (R := R) (A := A) m).symm.toMonoidHom.comp
    (GLSymplecticFin.diagonal.comp
      ((GeneralLinear.diagonalTorusCoordinates (N := m) (A := A)).comp
        (SplitTorus.pointsMulEquiv (R := R) (A := A)).toMonoidHom))

/-- Reading a diagonal-torus point as a symplectic matrix gives the standard diagonal matrix. -/
theorem pointsMulEquiv_diagonalTorusPoints
    (t : WithConv (MonoidAlgebra R
      (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) m (diagonalTorusPoints t) =
      GLSymplecticFin.diagonal
        (GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv t)) := by
  simp [diagonalTorusPoints]

/-- The diagonal-torus homomorphism into symplectic points is injective. -/
theorem diagonalTorusPoints_injective :
    Function.Injective (diagonalTorusPoints (R := R) (m := m) (A := A)) := by
  intro s t h
  apply (SplitTorus.pointsMulEquiv (R := R) (A := A)).injective
  have hc :
      GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv s) =
        GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv t) := by
    apply GLSymplecticFin.diagonal_injective
    rw [← pointsMulEquiv_diagonalTorusPoints, ← pointsMulEquiv_diagonalTorusPoints, h]
  funext i
  simpa only [GeneralLinear.diagonalTorusCoordinates_apply, ULift.up_down] using
    congrFun hc i.down

variable {B : Type v} [CommRing B] [Algebra R B]

/-- The symplectic diagonal-torus map is natural in the value algebra. -/
theorem mapValue_diagonalTorusPoints (f : A →ₐ[R] B)
    (t : WithConv (MonoidAlgebra R
      (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R m) f (diagonalTorusPoints t) =
      diagonalTorusPoints
        (AlgHom.mapValue
          (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) f t) := by
  apply (pointsMulEquiv (R := R) (A := B) m).injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_diagonalTorusPoints,
    pointsMulEquiv_diagonalTorusPoints, GLSymplecticFin.map_diagonal]
  congr 1
  funext i
  rw [GeneralLinear.diagonalTorusCoordinates_apply,
    GeneralLinear.diagonalTorusCoordinates_apply]
  change Units.map f.toRingHom (SplitTorus.pointsMulEquiv t (ULift.up i)) =
    SplitTorus.pointsMulEquiv (AlgHom.mapValue f t) (ULift.up i)
  exact (SplitTorus.pointsMulEquiv_mapValue f t (ULift.up i)).symm

/-- **The symplectic pinning equation on algebra-valued points.** Conjugation by a diagonal-torus
point scales the parameter of every standard root subgroup by its root character. -/
theorem diagonalTorusPoints_mul_rootSubgroupPoints_mul_inv
    (root : GLSymplecticFin.RootSubgroupIndex m)
    (t : WithConv (MonoidAlgebra R
      (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)) →ₐ[R] A))
    (c : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    diagonalTorusPoints t * rootSubgroupPoints root c * (diagonalTorusPoints t)⁻¹ =
      rootSubgroupPoints root
        ((AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).symm <|
          Multiplicative.ofAdd
            (((root.character
                (GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv t)) : Aˣ) : A) *
              Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv c))) := by
  apply (pointsMulEquiv (R := R) (A := A) m).injective
  rw [map_mul, map_mul, map_inv, pointsMulEquiv_diagonalTorusPoints,
    pointsMulEquiv_rootSubgroupPoints, pointsMulEquiv_rootSubgroupPoints,
    MulEquiv.apply_symm_apply]
  exact GLSymplecticFin.diagonal_mul_rootSubgroup_mul_inv root
    (GeneralLinear.diagonalTorusCoordinates (SplitTorus.pointsMulEquiv t))
    (AdditiveGroup.gaPointsMulEquiv c)

end Points

section Functor

/-- The natural transformation of group-valued points defined by the symplectic diagonal torus. -/
noncomputable def diagonalTorusPointsMap :
    HopfAlgebra.pointsFunctor
        (R := R)
        (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m) where
  app A := GrpCat.ofHom (diagonalTorusPoints (A := A))
  naturality _ _ f := by
    ext t
    exact (mapValue_diagonalTorusPoints f.hom t).symm

/-- The component of the natural diagonal-torus map is `diagonalTorusPoints`. -/
@[simp]
theorem diagonalTorusPointsMap_app (A : CommAlgCat.{w} R) :
    (diagonalTorusPointsMap (R := R) (m := m)).app A =
      GrpCat.ofHom diagonalTorusPoints :=
  (rfl)

end Functor

section Scheme

/-- The coordinate morphism of the symplectic diagonal torus, recovered from its natural action
on points. Its direction is opposite to the represented group-scheme morphism. -/
noncomputable def diagonalTorusCoordinateMap :
    coordinateHopfAlgebra R m ⟶
      _root_.CommHopfAlgCat.of R
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) :=
  ((CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).preimage
    (X := Opposite.op (_root_.CommHopfAlgCat.of R
      (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ)))))
    (Y := Opposite.op (coordinateHopfAlgebra R m))
    (diagonalTorusPointsMap.{u, u} (R := R) (m := m) :
      HopfAlgebra.pointsFunctor
          (R := R)
          (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m))).unop

/-- Precomposition by the coordinate morphism is the natural point map already constructed. -/
theorem mapPointsFunctor_diagonalTorusCoordinateMap :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (diagonalTorusCoordinateMap (R := R) (m := m)) :
      HopfAlgebra.pointsFunctor
          (R := R)
          (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m)) =
      (diagonalTorusPointsMap.{u, u} (R := R) (m := m) :
        HopfAlgebra.pointsFunctor
            (R := R)
            (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) ⟶
          HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m)) := by
  unfold diagonalTorusCoordinateMap
  rw [← CommHopfAlgCat.pointsFunctor_map]
  exact Functor.map_preimage
    (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}) _

/-- On every value algebra, the coordinate morphism induces `diagonalTorusPoints`. -/
@[simp]
theorem mapPointsFunctor_diagonalTorusCoordinateMap_app
    (A : CommAlgCat.{w} R)
    (t : HopfAlgebra.points
      (R := R)
      (H := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))) A) :
    (CommHopfAlgCat.mapPointsFunctor
      (diagonalTorusCoordinateMap (R := R) (m := m))).app A t =
      diagonalTorusPoints t := by
  let K := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin m) →₀ ℤ))
  let p : WithConv (K →ₐ[R] K) := toConv (AlgHom.id R K)
  have hp :
      (CommHopfAlgCat.mapPointsFunctor
        (diagonalTorusCoordinateMap (R := R) (m := m))).app (CommAlgCat.of R K) p =
        diagonalTorusPoints p := by
    rw [mapPointsFunctor_diagonalTorusCoordinateMap, diagonalTorusPointsMap_app]
    exact GrpCat.ofHom_apply diagonalTorusPoints p
  have htp : AlgHom.mapValue (H := K) t.ofConv p = t := by
    simp only [AlgHom.mapValue_apply, p, AlgHom.comp_id, WithConv.toConv_ofConv]
  have hnat :
      AlgHom.mapValue (H := coordinateHopfAlgebra R m) t.ofConv
          ((CommHopfAlgCat.mapPointsFunctor
            (diagonalTorusCoordinateMap (R := R) (m := m))).app (CommAlgCat.of R K) p) =
        (CommHopfAlgCat.mapPointsFunctor
          (diagonalTorusCoordinateMap (R := R) (m := m))).app A
            (AlgHom.mapValue (H := K) t.ofConv p) := by
    exact DFunLike.congr_fun
      (AlgHom.mapValue_mapDomain
        (diagonalTorusCoordinateMap (R := R) (m := m)).hom t.ofConv) p
  rw [← htp, ← hnat, hp, mapValue_diagonalTorusPoints]

/-- **The diagonal torus of `Sp₂ₘ` as a group-scheme morphism** from the rank-`m` split
torus. -/
noncomputable def diagonalTorus :
    SplitTorus.groupScheme R (ULift.{u} (Fin m)) ⟶ groupScheme R m :=
  eqToHom
      (DiagonalizableGroup.groupScheme_def R
        (SplitTorus.characterGroup (ULift.{u} (Fin m)))) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (diagonalTorusCoordinateMap (R := R) (m := m)).op ≫
    eqToHom (groupScheme_def R m).symm

/-- The diagonal torus is relative spectrum applied contravariantly to its coordinate morphism,
transported across the named presentations of the split torus and symplectic group. -/
theorem diagonalTorus_def :
    diagonalTorus (R := R) (m := m) =
      eqToHom
          (DiagonalizableGroup.groupScheme_def R
            (SplitTorus.characterGroup (ULift.{u} (Fin m)))) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (diagonalTorusCoordinateMap (R := R) (m := m)).op ≫
        eqToHom (groupScheme_def R m).symm :=
  (rfl)

end Scheme

end TauCeti.Symplectic
