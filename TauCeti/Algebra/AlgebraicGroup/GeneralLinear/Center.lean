/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic

/-!
# The center of the general linear group

For a field `k` and a positive integer `n`, this file identifies the center of the general
linear group scheme `GLₙ` with the multiplicative group `𝔾ₘ`. On points, a unit acts by its
scalar matrix. Mathlib's theorem `Matrix.GeneralLinearGroup.center_eq_range_scalar` supplies
the matrix-theoretic classification of the center; universal centrality then upgrades the
classification from each individual group of points to the represented center.

The natural pointwise equivalence and full faithfulness of the Hopf-algebra functor of points
give an isomorphism

```text
  k[GLₙ] / I(Z(GLₙ)) ≅ k[T, T⁻¹]
```

of commutative Hopf algebras. Thus the abstract center construction has the expected concrete
coordinate algebra in the basic reductive example.

## Main declarations

* `TauCeti.GeneralLinear.scalarTorusPoints`: the scalar-matrix map from `𝔾ₘ`-points to
  `GLₙ`-points.
* `TauCeti.GeneralLinear.scalarTorusCenterNatIso`: the natural isomorphism from `𝔾ₘ`-points
  to the represented center of `GLₙ`.
* `TauCeti.GeneralLinear.centerCoordinateLaurentIso`: the center coordinate Hopf algebra of
  `GLₙ` is the Laurent-polynomial Hopf algebra.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 2.4 and §21.
-/

public section

open CategoryTheory WithConv
open scoped LaurentPolynomial

namespace TauCeti

namespace GeneralLinear

universe u w w'

variable {R : Type u} [CommRing R]
variable (n : ℕ)

/-- Send a multiplicative-group point to the corresponding scalar general-linear point. -/
noncomputable def scalarTorusPoints {A : Type w} [CommRing A] [Algebra R A] :
    WithConv (R[T;T⁻¹] →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R n →ₐ[R] A) :=
  (pointsMulEquiv (R := R) (A := A) n).symm.toMonoidHom.comp
    ((Matrix.GeneralLinearGroup.scalar (Fin n)).comp
      (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).toMonoidHom)

/-- Under the standard point equivalences, `scalarTorusPoints` is the usual scalar-matrix
homomorphism. -/
@[simp]
theorem pointToGeneralLinear_scalarTorusPoints {A : Type w} [CommRing A] [Algebra R A]
    (f : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    pointToGeneralLinear n (scalarTorusPoints n f) =
      Matrix.GeneralLinearGroup.scalar (Fin n)
        (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A) f) := by
  simp [scalarTorusPoints]

/-- The scalar-matrix construction is natural in the value algebra. -/
theorem mapValue_scalarTorusPoints {A : Type w} {B : Type w'} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
    (f : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R n) φ (scalarTorusPoints n f) =
      scalarTorusPoints n (AlgHom.mapValue (H := R[T;T⁻¹]) φ f) := by
  apply (pointsMulEquiv (R := R) (A := B) n).injective
  calc
    pointsMulEquiv n (AlgHom.mapValue φ (scalarTorusPoints n f)) =
        Matrix.GeneralLinearGroup.map φ.toRingHom (pointsMulEquiv n (scalarTorusPoints n f)) :=
      pointsMulEquiv_mapValue n φ _
    _ = pointsMulEquiv n (scalarTorusPoints n (AlgHom.mapValue φ f)) := by
      simp only [pointsMulEquiv_apply, pointToGeneralLinear_scalarTorusPoints,
        MultiplicativeGroup.pointsMulEquiv_mapValue, Matrix.GeneralLinearGroup.map_scalar]
      exact congrArg (Matrix.GeneralLinearGroup.scalar (Fin n)) (Units.ext rfl)

/-- Scalar multiplication is injective in positive rank, stated on the represented point
groups. -/
theorem scalarTorusPoints_injective (hn : 0 < n) {A : Type w} [CommRing A] [Algebra R A] :
    Function.Injective (scalarTorusPoints (R := R) n (A := A)) := by
  intro f g hfg
  apply (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A)).injective
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hmat :
      Matrix.GeneralLinearGroup.scalar (Fin n)
          (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A) f) =
        Matrix.GeneralLinearGroup.scalar (Fin n)
          (MultiplicativeGroup.pointsMulEquiv (R := R) (A := A) g) := by
    simpa only [pointsMulEquiv_apply, pointToGeneralLinear_scalarTorusPoints] using
      congrArg (pointsMulEquiv (R := R) (A := A) n) hfg
  apply Units.ext
  apply (Matrix.scalar_inj (n := Fin n)).mp
  simpa only [Matrix.GeneralLinearGroup.coe_scalar] using congrArg Units.val hmat

/-- Scalar points are universally central over any commutative base ring. -/
theorem scalarTorusPoints_isCentralPoint {A : Type u} [CommRing A] [Algebra R A]
    (f : WithConv (R[T;T⁻¹] →ₐ[R] A)) :
    HopfAlgebra.IsCentralPoint (scalarTorusPoints n f) := by
  rw [HopfAlgebra.isCentralPoint_def]
  intro B _ _ φ g
  apply (pointsMulEquiv (R := R) (A := B) n).injective
  simpa only [map_mul, mapValue_scalarTorusPoints, pointsMulEquiv_apply,
    pointToGeneralLinear_scalarTorusPoints]
    using Matrix.GeneralLinearGroup.scalar_commute
      (MultiplicativeGroup.pointsMulEquiv (R := R) (A := B) (AlgHom.mapValue φ f))
      (pointsMulEquiv (R := R) (A := B) n g)

section Center

variable {k : Type u} [Field k]

/-- Every scalar point is a point of the represented center of `GLₙ`. -/
theorem scalarTorusPoints_mem_centerPointsSubgroup {A : Type u} [CommRing A] [Algebra k A]
    (f : WithConv (k[T;T⁻¹] →ₐ[k] A)) :
    scalarTorusPoints n f ∈ CommHopfAlgCat.centerPointsSubgroup
      (coordinateHopfAlgebra k n) (CommAlgCat.of k A) := by
  rw [CommHopfAlgCat.mem_centerPointsSubgroup_iff]
  exact scalarTorusPoints_isCentralPoint n f

/-- The scalar-matrix map with codomain restricted to the represented center. -/
noncomputable def scalarTorusCenterHom (A : CommAlgCat.{u} k) :
    HopfAlgebra.points (R := k) (H := k[T;T⁻¹]) A →*
      CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A :=
  (scalarTorusPoints (R := k) n (A := A)).codRestrict
    (CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A)
    (scalarTorusPoints_mem_centerPointsSubgroup n)

/-- The underlying value of `scalarTorusCenterHom` is the scalar-matrix point. -/
@[simp]
theorem coe_scalarTorusCenterHom_apply (A : CommAlgCat.{u} k)
    (f : HopfAlgebra.points (R := k) (H := k[T;T⁻¹]) A) :
    (scalarTorusCenterHom n A f :
      HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A) =
      scalarTorusPoints n f := by
  rfl

/-- In positive rank, scalar matrices give every universally central point of `GLₙ`. -/
theorem scalarTorusCenterHom_bijective (hn : 0 < n) (A : CommAlgCat.{u} k) :
    Function.Bijective (scalarTorusCenterHom n A) := by
  constructor
  · intro f g hfg
    apply scalarTorusPoints_injective (R := k) n hn
    exact congrArg Subtype.val hfg
  · intro g
    have hgcentral :
        pointsMulEquiv (R := k) (A := A) n g.1 ∈
          Subgroup.center (Matrix.GeneralLinearGroup (Fin n) A) := by
      have hgcenter :
          g.1 ∈ Subgroup.center
            (HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A) := by
        apply HopfAlgebra.center_le_center
        rw [← CommHopfAlgCat.centerPointsSubgroup_eq_center]
        exact g.2
      exact (Subgroup.centerCongr (pointsMulEquiv (R := k) (A := A) n)
        ⟨g.1, hgcenter⟩).2
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hgcentral
    obtain ⟨a, ha⟩ := hgcentral
    refine ⟨(MultiplicativeGroup.pointsMulEquiv (R := k) (A := A)).symm a, ?_⟩
    apply Subtype.ext
    rw [coe_scalarTorusCenterHom_apply]
    apply (pointsMulEquiv (R := k) (A := A) n).injective
    rw [pointsMulEquiv_apply, pointToGeneralLinear_scalarTorusPoints,
      MulEquiv.apply_symm_apply]
    exact ha

/-- A general-linear point is universally central exactly when it is a scalar point. -/
theorem mem_centerPointsSubgroup_iff_exists_scalarTorusPoints (hn : 0 < n)
    (A : CommAlgCat.{u} k)
    (g : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A) :
    g ∈ CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A ↔
      ∃ f : HopfAlgebra.points (R := k) (H := k[T;T⁻¹]) A,
        scalarTorusPoints n f = g := by
  constructor
  · intro hg
    obtain ⟨f, hf⟩ := (scalarTorusCenterHom_bijective n hn A).2 ⟨g, hg⟩
    refine ⟨f, ?_⟩
    calc
      scalarTorusPoints n f =
          (scalarTorusCenterHom n A f :
            HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k n) A) :=
        (coe_scalarTorusCenterHom_apply n A f).symm
      _ = g := congrArg Subtype.val hf
  · rintro ⟨f, rfl⟩
    exact scalarTorusPoints_mem_centerPointsSubgroup n f

/-- For every value algebra, scalar matrices identify the multiplicative group with the
represented center of `GLₙ`. -/
noncomputable def scalarTorusCenterIso (hn : 0 < n) (A : CommAlgCat.{u} k) :
    HopfAlgebra.points (R := k) (H := k[T;T⁻¹]) A ≅
      GrpCat.of (CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A) :=
  (MulEquiv.ofBijective (scalarTorusCenterHom n A)
    (scalarTorusCenterHom_bijective n hn A)).toGrpIso

/-- The forward component of `scalarTorusCenterIso` is the scalar-matrix homomorphism. -/
@[simp]
theorem scalarTorusCenterIso_hom_apply (hn : 0 < n) (A : CommAlgCat.{u} k)
    (f : HopfAlgebra.points (R := k) (H := k[T;T⁻¹]) A) :
    (scalarTorusCenterIso n hn A).hom f = scalarTorusCenterHom n A f := by
  rfl

private theorem scalarTorusCenterHom_natural {A B : CommAlgCat.{u} k} (φ : A ⟶ B)
    (f : HopfAlgebra.points (R := k) (H := k[T;T⁻¹]) A) :
    CommHopfAlgCat.mapQuotientPointsSubgroup
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)) φ
        (scalarTorusCenterHom n A f) =
      scalarTorusCenterHom n B (AlgHom.mapValue (H := k[T;T⁻¹]) φ.hom f) := by
  apply Subtype.ext
  rw [CommHopfAlgCat.coe_mapQuotientPointsSubgroup_apply,
    coe_scalarTorusCenterHom_apply, coe_scalarTorusCenterHom_apply]
  exact mapValue_scalarTorusPoints n φ.hom f

/-- Scalar matrices identify the multiplicative-group functor with the represented center
subfunctor of `GLₙ`. -/
noncomputable def scalarTorusCenterNatIso (hn : 0 < n) :
    HopfAlgebra.pointsFunctor (R := k) (H := k[T;T⁻¹]) ≅
      CommHopfAlgCat.quotientPointsSubgroupFunctor
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)) :=
  NatIso.ofComponents (scalarTorusCenterIso n hn) (by
    intro A B φ
    ext f
    exact (scalarTorusCenterHom_natural n φ f).symm)

/-- The natural isomorphism sends a multiplicative-group point to its scalar matrix. -/
@[simp]
theorem scalarTorusCenterNatIso_hom_app_apply (hn : 0 < n) (A : CommAlgCat.{u} k)
    (f : HopfAlgebra.points (R := k) (H := k[T;T⁻¹]) A) :
    CategoryTheory.ConcreteCategory.hom
        (X := (HopfAlgebra.pointsFunctor (R := k) (H := k[T;T⁻¹])).obj A)
        (Y := GrpCat.of (CommHopfAlgCat.centerPointsSubgroup
          (coordinateHopfAlgebra k n) A))
        ((scalarTorusCenterNatIso n hn).hom.app A) f =
      scalarTorusCenterHom n A f := by
  rfl

/-- The point functor of `𝔾ₘ` is naturally isomorphic to the point functor represented by the
center coordinate Hopf algebra of `GLₙ`. -/
noncomputable def scalarTorusCenterCoordinatePointsNatIso (hn : 0 < n) :
    (CommHopfAlgCat.pointsFunctor (R := k)).obj
        (Opposite.op (CommHopfAlgCat.of k k[T;T⁻¹])) ≅
      (CommHopfAlgCat.pointsFunctor (R := k)).obj
        (Opposite.op (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
          (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)))) :=
  scalarTorusCenterNatIso n hn ≪≫
    (CommHopfAlgCat.quotientPointsSubgroupNatIso
      (coordinateHopfAlgebra k n)
      (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))).symm

/-- The coordinate Hopf algebra of the center of positive-rank `GLₙ` is the Laurent-polynomial
Hopf algebra of `𝔾ₘ`. -/
noncomputable def centerCoordinateLaurentIso (hn : 0 < n) :
    CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)) ≅
      CommHopfAlgCat.of k k[T;T⁻¹] :=
  Iso.unop <| (Functor.FullyFaithful.ofFullyFaithful
    (CommHopfAlgCat.pointsFunctor (R := k))).preimageIso
      (scalarTorusCenterCoordinatePointsNatIso n hn)

/-- Applying the functor of points to `centerCoordinateLaurentIso` recovers the scalar-matrix
natural isomorphism used to construct it. -/
theorem pointsFunctor_mapIso_centerCoordinateLaurentIso (hn : 0 < n) :
    (CommHopfAlgCat.pointsFunctor (R := k)).mapIso (centerCoordinateLaurentIso n hn).op =
      scalarTorusCenterCoordinatePointsNatIso n hn := by
  unfold centerCoordinateLaurentIso
  rw [Iso.unop_op]
  apply Iso.ext
  exact (Functor.FullyFaithful.ofFullyFaithful
    (CommHopfAlgCat.pointsFunctor (R := k))).map_preimage _

end Center

end GeneralLinear

end TauCeti
