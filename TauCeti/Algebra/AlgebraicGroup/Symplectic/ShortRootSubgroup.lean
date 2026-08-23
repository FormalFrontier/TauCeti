/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic

/-!
# Short-root subgroups of the symplectic group

For distinct `i j : Fin m`, the short roots of the split symplectic group `Sp₂ₘ` occur in three
families:

```text
 eᵢ - eⱼ,       eᵢ + eⱼ,       -eᵢ - eⱼ.
```

Their root elements are products of two commuting elementary matrices:

```text
x_{eᵢ-eⱼ}(c)  = (1 + c E_{i,j})(1 - c E_{m+j,m+i}),
x_{eᵢ+eⱼ}(c)  = (1 + c E_{i,m+j})(1 + c E_{j,m+i}),
x_{-eᵢ-eⱼ}(c) = (1 + c E_{m+i,j})(1 + c E_{m+j,i}).
```

The matrix-level construction in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic` proves directly that these products
preserve the standard alternating form and form one-parameter subgroups over every commutative
ring. This file assembles the three families uniformly, proves naturality in the value algebra,
recovers their coordinate Hopf-algebra morphisms by full faithfulness of the functor of points,
and applies relative spectrum to obtain affine group-scheme morphisms `𝔾ₐ → Sp₂ₘ`.

Together with `TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup`, this gives root-subgroup
maps for every root of the standard type-`Cₘ` realization: the earlier file supplies the long
roots `±2eᵢ`, while this file supplies all short roots.

## Main declarations

* `TauCeti.Symplectic.ShortRootFamily`: the three uniform families of type-`C` short roots.
* `TauCeti.Symplectic.shortRootSubgroupPoints`: the corresponding homomorphism on algebra-valued
  points.
* `TauCeti.Symplectic.shortRootSubgroupCoordinateMap`: its coordinate Hopf-algebra morphism.
* `TauCeti.Symplectic.shortRootSubgroup`: the affine group-scheme morphism `𝔾ₐ → Sp₂ₘ`.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.

This advances Layer 9, "Root subgroup maps", of the ReductiveGroups roadmap and supplies the
short-root half of the standard `Sp₂ₘ` worked example. In rank two it fixes the long/short
interface needed by the `B₂/C₂` special-isogeny target.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.Symplectic

universe u v w

variable {R : Type u} [CommRing R] {m : ℕ} {i j : Fin m}

/-- The three uniform families of short roots in the standard type-`Cₘ` realization.

The difference family is ordered: swapping `i` and `j` changes `eᵢ-eⱼ` to its negative. The two
sum families are symmetric in `i` and `j`. -/
inductive ShortRootFamily
  | difference
  | positiveSum
  | negativeSum
  deriving DecidableEq

namespace ShortRootFamily

/-- The matrix one-parameter subgroup belonging to a family of short roots. -/
def transvectionHom (family : ShortRootFamily) (hij : i ≠ j) :
    Multiplicative R →* GLSymplecticFin m R :=
  match family with
  | difference => GLSymplecticFin.differenceShortRootTransvectionHom hij
  | positiveSum => GLSymplecticFin.positiveSumShortRootTransvectionHom hij
  | negativeSum => GLSymplecticFin.negativeSumShortRootTransvectionHom hij

/-- Evaluating a short-root one-parameter subgroup commutes with change of coefficients. -/
@[simp]
theorem map_transvectionHom_apply {S : Type v} [CommRing S] (family : ShortRootFamily)
    (f : R →+* S) (hij : i ≠ j) (c : Multiplicative R) :
    GLSymplecticFin.map m R f (family.transvectionHom hij c) =
      family.transvectionHom hij (Multiplicative.ofAdd (f c.toAdd)) := by
  cases family
  · rw [transvectionHom, transvectionHom,
      GLSymplecticFin.differenceShortRootTransvectionHom_apply,
      GLSymplecticFin.differenceShortRootTransvectionHom_apply,
      GLSymplecticFin.map_differenceShortRootTransvectionUnit]
    simp
  · rw [transvectionHom, transvectionHom,
      GLSymplecticFin.positiveSumShortRootTransvectionHom_apply,
      GLSymplecticFin.positiveSumShortRootTransvectionHom_apply,
      GLSymplecticFin.map_positiveSumShortRootTransvectionUnit]
    simp
  · rw [transvectionHom, transvectionHom,
      GLSymplecticFin.negativeSumShortRootTransvectionHom_apply,
      GLSymplecticFin.negativeSumShortRootTransvectionHom_apply,
      GLSymplecticFin.map_negativeSumShortRootTransvectionUnit]
    simp

/-- Every short-root one-parameter subgroup is injective. -/
theorem transvectionHom_injective (family : ShortRootFamily) (hij : i ≠ j) :
    Function.Injective (family.transvectionHom (R := R) hij) := by
  intro c d h
  apply Multiplicative.toAdd.injective
  cases family
  · apply GLSymplecticFin.differenceShortRootTransvectionUnit_injective hij
    simpa only [transvectionHom, GLSymplecticFin.differenceShortRootTransvectionHom_apply] using h
  · apply GLSymplecticFin.positiveSumShortRootTransvectionUnit_injective hij
    simpa only [transvectionHom, GLSymplecticFin.positiveSumShortRootTransvectionHom_apply] using h
  · apply GLSymplecticFin.negativeSumShortRootTransvectionUnit_injective hij
    simpa only [transvectionHom, GLSymplecticFin.negativeSumShortRootTransvectionHom_apply] using h

end ShortRootFamily

section Points

variable {A : Type w} [CommRing A] [Algebra R A]
variable {B : Type v} [CommRing B] [Algebra R B]

/-- The short-root homomorphism on `A`-valued points of `𝔾ₐ` and `Sp₂ₘ`. -/
noncomputable def shortRootSubgroupPoints (family : ShortRootFamily) (hij : i ≠ j) :
    WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R m →ₐ[R] A) :=
  (pointsMulEquiv (R := R) (A := A) m).symm.toMonoidHom.comp
    ((family.transvectionHom hij).comp
      (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).toMonoidHom)

/-- Under the symplectic point equivalence, a short-root point is its paired-elementary-matrix
one-parameter subgroup. -/
theorem pointsMulEquiv_shortRootSubgroupPoints (family : ShortRootFamily) (hij : i ≠ j)
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) m (shortRootSubgroupPoints family hij q) =
      family.transvectionHom hij
        (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) q) := by
  rw [shortRootSubgroupPoints]
  simp

/-- A short-root subgroup is injective on points over every value algebra. -/
theorem shortRootSubgroupPoints_injective (family : ShortRootFamily) (hij : i ≠ j) :
    Function.Injective (shortRootSubgroupPoints (R := R) (A := A) family hij) :=
  (pointsMulEquiv (R := R) (A := A) m).symm.injective.comp <|
    (family.transvectionHom_injective hij).comp
      (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).injective

/-- Short-root point homomorphisms are natural in the value algebra. -/
theorem mapValue_shortRootSubgroupPoints (family : ShortRootFamily) (φ : A →ₐ[R] B)
    (hij : i ≠ j) (q : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R m) φ (shortRootSubgroupPoints family hij q) =
      shortRootSubgroupPoints family hij
        (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) φ q) := by
  apply (pointsMulEquiv (R := R) (A := B) m).injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_shortRootSubgroupPoints,
    pointsMulEquiv_shortRootSubgroupPoints, ShortRootFamily.map_transvectionHom_apply]
  apply congrArg (family.transvectionHom hij)
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd, AdditiveGroup.toAdd_gaPointsMulEquiv_mapValue]
  rfl

end Points

/-- The natural transformation of group-valued points attached to a short root. -/
noncomputable def shortRootSubgroupPointsMap (family : ShortRootFamily) (hij : i ≠ j) :
    HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m) where
  app A := GrpCat.ofHom (shortRootSubgroupPoints (A := A) family hij)
  naturality _ _ φ := by
    ext q
    exact (mapValue_shortRootSubgroupPoints family φ.hom hij q).symm

/-- A component of the natural short-root points map is the constructed point homomorphism. -/
@[simp]
theorem shortRootSubgroupPointsMap_app (family : ShortRootFamily) (hij : i ≠ j)
    (A : CommAlgCat.{w} R) :
    (shortRootSubgroupPointsMap (R := R) family hij).app A =
      GrpCat.ofHom (shortRootSubgroupPoints family hij) :=
  by rw [shortRootSubgroupPointsMap]

/-- The coordinate Hopf-algebra morphism of a short-root subgroup. -/
noncomputable def shortRootSubgroupCoordinateMap (family : ShortRootFamily) (hij : i ≠ j) :
    coordinateHopfAlgebra R m ⟶ AdditiveGroup.coordinateHopfAlgebra R :=
  ((CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}).preimage
    (shortRootSubgroupPointsMap.{u, u} (R := R) family hij)).unop

/-- Precomposition by the short-root coordinate morphism is its natural map on points. -/
theorem mapPointsFunctor_shortRootSubgroupCoordinateMap
    (family : ShortRootFamily) (hij : i ≠ j) :
    (CommHopfAlgCat.mapPointsFunctor.{u, u, u}
      (shortRootSubgroupCoordinateMap (R := R) family hij) :
      HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
        HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R m)) =
      shortRootSubgroupPointsMap.{u, u} family hij := by
  unfold shortRootSubgroupCoordinateMap
  rw [← CommHopfAlgCat.pointsFunctor_map]
  exact Functor.map_preimage
    (CommHopfAlgCat.pointsFunctor.{u, u, u} (R := R) :
      (_root_.CommHopfAlgCat.{u} R)ᵒᵖ ⥤ CommAlgCat.{u} R ⥤ GrpCat.{u}) _

/-- On a same-universe algebra, the coordinate morphism induces the constructed short-root point
homomorphism. -/
@[simp]
theorem mapPointsFunctor_shortRootSubgroupCoordinateMap_app
    (family : ShortRootFamily) (hij : i ≠ j) (A : CommAlgCat.{u} R)
    (q : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    (CommHopfAlgCat.mapPointsFunctor
      (shortRootSubgroupCoordinateMap (R := R) family hij)).app A q =
      shortRootSubgroupPoints family hij q := by
  rw [mapPointsFunctor_shortRootSubgroupCoordinateMap, shortRootSubgroupPointsMap_app]
  rfl

/-- The affine group-scheme morphism `𝔾ₐ → Sp₂ₘ` attached to a short root. -/
noncomputable def shortRootSubgroup (family : ShortRootFamily) (hij : i ≠ j) :
    AdditiveGroup.groupScheme R ⟶ groupScheme R m :=
  eqToHom (AdditiveGroup.groupScheme_def R) ≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
      (shortRootSubgroupCoordinateMap family hij).op ≫
    eqToHom (groupScheme_def R m).symm

/-- The short-root subgroup is relative spectrum applied to its coordinate morphism. -/
theorem shortRootSubgroup_def (family : ShortRootFamily) (hij : i ≠ j) :
    shortRootSubgroup (R := R) family hij =
      eqToHom (AdditiveGroup.groupScheme_def R) ≫
        (AlgebraicGeometry.hopfSpec (CommRingCat.of R)).map
          (shortRootSubgroupCoordinateMap family hij).op ≫
        eqToHom (groupScheme_def R m).symm := by
  unfold shortRootSubgroup
  rfl

end TauCeti.Symplectic
