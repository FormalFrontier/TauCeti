/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.GeneralLinear.pointsMulEquiv` is the body of the root subgroup homomorphism.
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
-- `TauCeti.AdditiveGroup.gaPointsMulEquiv` and the coordinate Hopf algebra of `𝔾ₐ` are its source.
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
-- `TauCeti.transvectionUnit` is the matrix the homomorphism is built from.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# The root subgroups of the general linear group

For a pair of distinct indices `i ≠ j`, the elementary matrices `xᵢⱼ(c) = 1 + c Eᵢⱼ` form a
one-parameter subgroup of `GLₙ`. This file promotes that family to a homomorphism of affine group
schemes

`xᵢⱼ : 𝔾ₐ → GLₙ`

over an arbitrary commutative base ring `R`, in the functor-of-points formulation: on the
`A`-points of `𝔾ₐ`, which are the additive group of `A`, it is the map `c ↦ xᵢⱼ(c)` into the
`A`-points of `GLₙ`, which are `GL n A`, and `TauCeti.GeneralLinear.rootSubgroup` packages the
family over all `A` as a morphism of the two representable group functors.

Reading the index pair `(i, j)` as the root `εᵢ - εⱼ` of the diagonal torus of `GLₙ`, this is the
**root subgroup** of that root. The relations it satisfies — additivity in the parameter, the
Chevalley commutator relations, and the rescaling of the parameter under conjugation by the torus
— all hold at the level of the matrices, and are proved in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/Transvection.lean`; the points equivalences
`TauCeti.GeneralLinear.pointsMulEquiv` and `TauCeti.AdditiveGroup.gaPointsMulEquiv` transport them
to any of the three views of the group. Nothing here needs `R` to be a field, and nothing needs the
base to be reduced or the rank to be positive: the construction is the one over `ℤ` that a
Chevalley–Demazure group of type `A` base changes from.

## Main definitions

* `TauCeti.GeneralLinear.rootSubgroupPoints`: the homomorphism on `A`-points, from the additive
  group of `A` to `GL n A`, read through the two points equivalences.
* `TauCeti.GeneralLinear.rootSubgroup`: the resulting morphism of representable group functors
  `𝔾ₐ → GLₙ`.

## Main results

* `TauCeti.GeneralLinear.pointsMulEquiv_rootSubgroupPoints`: the homomorphism on points is the
  elementary matrix of the parameter.
* `TauCeti.GeneralLinear.rootSubgroupPoints_injective`: the homomorphism on points is injective.
* `TauCeti.GeneralLinear.mapValue_rootSubgroupPoints`: it is natural in the value algebra, which
  is what makes `TauCeti.GeneralLinear.rootSubgroup` a morphism of group functors.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21, where the root subgroups of a split reductive group
  are characterised by exactly these equations.
* R. W. Carter, *Simple Groups of Lie Type* (1972), §11.3.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

namespace GeneralLinear

universe u w

variable {R : Type u} [CommRing R] {N : ℕ} {i j : Fin N}

section Points

variable {A : Type w} [CommRing A] [Algebra R A] {B : Type w} [CommRing B] [Algebra R B]

/-- The root subgroup homomorphism on `A`-points: it sends the `A`-point `c` of `𝔾ₐ` to the
elementary matrix `xᵢⱼ(c)`, an `A`-point of `GLₙ`. -/
noncomputable def rootSubgroupPoints (hij : i ≠ j) :
    WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R N →ₐ[R] A) :=
  ((pointsMulEquiv (R := R) (A := A) N).symm.toMonoidHom.comp
    ((transvectionHom hij).comp
      (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).toMonoidHom))

/-- On points, the root subgroup homomorphism is the elementary matrix of the parameter. This is
not a `simp` lemma, since `TauCeti.GeneralLinear.pointsMulEquiv_apply` rewrites its left-hand
side. -/
theorem pointsMulEquiv_rootSubgroupPoints (hij : i ≠ j)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    pointsMulEquiv N (rootSubgroupPoints hij f) =
      transvectionUnit hij
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) f)) := by
  rw [rootSubgroupPoints]
  simp

/-- The root subgroup homomorphism on points is injective. -/
theorem rootSubgroupPoints_injective (hij : i ≠ j) :
    Function.Injective (rootSubgroupPoints (R := R) (A := A) hij) := by
  intro f g h
  apply (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A)).injective
  have h' :
      transvectionUnit hij
          (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) f)) =
        transvectionUnit hij
          (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := R) (A := A) g)) := by
    rw [← pointsMulEquiv_rootSubgroupPoints, ← pointsMulEquiv_rootSubgroupPoints]
    exact congrArg (pointsMulEquiv (R := R) (A := A) N) h
  simpa only [ofAdd_toAdd] using
    congrArg Multiplicative.ofAdd (transvectionUnit_injective (A := A) hij h')

/-- The root subgroup homomorphism is natural in the value algebra: the elementary matrix of the
image parameter is the image of the elementary matrix. -/
theorem mapValue_rootSubgroupPoints (φ : A →ₐ[R] B) (hij : i ≠ j)
    (f : WithConv (AdditiveGroup.coordinateHopfAlgebra R →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R N) φ (rootSubgroupPoints hij f) =
      rootSubgroupPoints hij
        (AlgHom.mapValue (H := AdditiveGroup.coordinateHopfAlgebra R) φ f) := by
  apply (pointsMulEquiv (R := R) (A := B) N).injective
  rw [pointsMulEquiv_mapValue, pointsMulEquiv_rootSubgroupPoints,
    pointsMulEquiv_rootSubgroupPoints, map_transvectionUnit,
    AdditiveGroup.toAdd_gaPointsMulEquiv_mapValue]
  rfl

end Points

section Functor

/-- **The root subgroup of `GLₙ` attached to the root `εᵢ - εⱼ`**: the homomorphism of affine group
schemes `𝔾ₐ → GLₙ` whose value on an `A`-point `c` of `𝔾ₐ` is the elementary matrix `xᵢⱼ(c)`. It is
a morphism of the functors of points of the two coordinate Hopf algebras. -/
noncomputable def rootSubgroup (hij : i ≠ j) :
    HopfAlgebra.pointsFunctor (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := coordinateHopfAlgebra R N) where
  app A := GrpCat.ofHom (rootSubgroupPoints (A := A) hij)
  naturality _ _ φ := by
    ext f
    exact (mapValue_rootSubgroupPoints φ.hom hij f).symm

/-- The component of the root subgroup morphism at a value algebra is the homomorphism on
points. -/
@[simp]
theorem rootSubgroup_app (hij : i ≠ j) (A : CommAlgCat.{w} R) :
    (rootSubgroup (R := R) (N := N) hij).app A = GrpCat.ofHom (rootSubgroupPoints hij) :=
  (rfl)

/-- Every component of the root subgroup morphism is injective on points. -/
theorem rootSubgroup_app_injective (hij : i ≠ j) (A : CommAlgCat.{w} R) :
    Function.Injective ((rootSubgroup (R := R) (N := N) hij).app A) := by
  change Function.Injective (rootSubgroupPoints (R := R) (A := A) hij)
  exact rootSubgroupPoints_injective hij

/-- The root subgroup morphism sends an `A`-point of `𝔾ₐ` to the elementary matrix of its
parameter. -/
theorem pointsMulEquiv_rootSubgroup_app (hij : i ≠ j) (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := AdditiveGroup.coordinateHopfAlgebra R) A) :
    pointsMulEquiv N ((rootSubgroup hij).app A f) =
      transvectionUnit hij (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f)) :=
  pointsMulEquiv_rootSubgroupPoints hij f

end Functor

end GeneralLinear

end TauCeti
