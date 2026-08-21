/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Yoneda
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# The center of the special linear group

For a field `k` and a positive integer `n`, this file identifies the center of the special
linear group scheme `SLₙ` with the roots-of-unity group scheme `μₙ`. A root of unity acts by
its scalar matrix. Mathlib's equivalence
`Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'` supplies the matrix-theoretic
classification of the center; universal centrality then upgrades it to the represented center.

The natural pointwise equivalence and full faithfulness of the Hopf-algebra functor of points
give an isomorphism

```text
  k[SLₙ] / I(Z(SLₙ)) ≅ k[Multiplicative (ZMod n)]
```

of commutative Hopf algebras. This is the center calculation used by the standard central
isogeny from `SLₙ` toward its adjoint form.

## Main declarations

* `TauCeti.SpecialLinear.rootsOfUnityScalarPoints`: the scalar-matrix map from `μₙ`-points to
  `SLₙ`-points.
* `TauCeti.SpecialLinear.rootsOfUnityScalarCenterNatIso`: the natural isomorphism from `μₙ`-points
  to the represented center of `SLₙ`.
* `TauCeti.SpecialLinear.centerCoordinateIsoGroupAlgebra`: the center coordinate Hopf algebra of
  `SLₙ` is the group algebra of `Multiplicative (ZMod n)`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Examples 2.4 and 5.49, and §18.a.

This advances Layer 6, "Reductive and semisimple groups", of the ReductiveGroups roadmap:
the center and central-isogeny input for the simply connected and adjoint forms.
-/

public section

open CategoryTheory WithConv

namespace TauCeti

namespace SpecialLinear

universe u v w

variable (n : ℕ)

/-- The scalar-matrix homomorphism from `n`th roots of unity to `SL(Fin n, A)`. -/
@[expose] noncomputable def rootsOfUnityScalarSL {A : Type v} [CommRing A] :
    rootsOfUnity n A →* Matrix.SpecialLinearGroup (Fin n) A where
  toFun ζ := (⟨Matrix.scalar (Fin n) ((ζ : Aˣ) : A), by
    rw [Matrix.scalar_apply, Matrix.det_diagonal]
    simpa using congrArg Units.val ζ.property⟩ :
      Matrix.SpecialLinearGroup (Fin n) A)
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [Matrix.scalar_apply]
  map_mul' ζ ξ := by
    apply Subtype.ext
    -- After subtype extensionality, expose the record's `toFun`; all matrix algebra is then
    -- discharged by the scalar-matrix simp lemmas.
    change Matrix.scalar (Fin n) ((((ζ * ξ : rootsOfUnity n A) : Aˣ) : A)) =
      Matrix.scalar (Fin n) (((ζ : Aˣ) : A)) *
        Matrix.scalar (Fin n) (((ξ : Aˣ) : A))
    simp

/-- The underlying matrix of `rootsOfUnityScalarSL` is the corresponding scalar matrix. -/
@[simp]
theorem coe_rootsOfUnityScalarSL {A : Type v} [CommRing A] (ζ : rootsOfUnity n A) :
    ((rootsOfUnityScalarSL n ζ : Matrix.SpecialLinearGroup (Fin n) A) :
      Matrix (Fin n) (Fin n) A) = Matrix.scalar (Fin n) ((ζ : Aˣ) : A) :=
  rfl

/-- Send a roots-of-unity point to the corresponding scalar special-linear point. -/
noncomputable def rootsOfUnityScalarPoints
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] :
    WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R n →ₐ[R] A) :=
  (TauCeti.SpecialLinear.pointsMulEquiv (R := R) (A := A) n).symm.toMonoidHom.comp <|
    (rootsOfUnityScalarSL n).comp
      (RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) n).toMonoidHom

/-- Under the standard point equivalences, `rootsOfUnityScalarPoints` is the scalar matrix
attached to a root of unity. -/
@[simp]
theorem pointsMulEquiv_rootsOfUnityScalarPoints
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    TauCeti.SpecialLinear.pointsMulEquiv (R := R) (A := A) n
        (rootsOfUnityScalarPoints n f) =
      rootsOfUnityScalarSL n
        (RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) n f) := by
  simp [rootsOfUnityScalarPoints]

/-- The central special-linear matrix attached to a root of unity is a scalar matrix. -/
@[simp]
theorem coe_pointsMulEquiv_rootsOfUnityScalarPoints
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    ((TauCeti.SpecialLinear.pointsMulEquiv (R := R) (A := A) n
        (rootsOfUnityScalarPoints n f) :
        Matrix.SpecialLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) =
      Matrix.scalar (Fin n)
        ((RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) n f : Aˣ) : A) := by
  rw [pointsMulEquiv_rootsOfUnityScalarPoints, coe_rootsOfUnityScalarSL]

/-- For `0 < n`, the scalar roots-of-unity map is injective. -/
theorem rootsOfUnityScalarPoints_injective (hn : 0 < n)
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] :
    Function.Injective (rootsOfUnityScalarPoints (R := R) n (A := A)) := by
  intro f g hfg
  apply (RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) n).injective
  apply Subtype.ext
  apply Units.ext
  have h := congrArg (TauCeti.SpecialLinear.pointsMulEquiv (R := R) (A := A) n) hfg
  have hmatrix := congrArg Subtype.val h
  rw [coe_pointsMulEquiv_rootsOfUnityScalarPoints,
    coe_pointsMulEquiv_rootsOfUnityScalarPoints] at hmatrix
  exact (@Matrix.scalar_inj (Fin n) A inferInstance inferInstance inferInstance
    ⟨⟨0, hn⟩⟩ _ _).mp hmatrix

/-- The scalar roots-of-unity construction is natural in the value algebra. -/
theorem mapValue_rootsOfUnityScalarPoints
    {R : Type u} [CommRing R] {A : Type v} {B : Type w}
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R n) φ (rootsOfUnityScalarPoints n f) =
      rootsOfUnityScalarPoints n
        (AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (ZMod n))) φ f) := by
  apply (SpecialLinear.pointsMulEquiv (R := R) (A := B) n).injective
  have hmap := SpecialLinear.pointsMulEquiv_mapValue (R := R) (A := A) (B := B) n φ
    (rootsOfUnityScalarPoints n f)
  rw [hmap]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe,
    coe_pointsMulEquiv_rootsOfUnityScalarPoints,
    coe_pointsMulEquiv_rootsOfUnityScalarPoints]
  ext i j
  rw [RootsOfUnityGroup.pointsMulEquiv_mapValue]
  by_cases hij : i = j <;>
    simp [hij, RootsOfUnityGroup.pointsMulEquiv_apply]

section Center

variable {S : Type u} [CommRing S]

/-- A scalar roots-of-unity point is universally central over any commutative base ring. -/
theorem isCentralPoint_rootsOfUnityScalarPoints
    {A : Type u} [CommRing A] [Algebra S A]
    (f : WithConv (MonoidAlgebra S (Multiplicative (ZMod n)) →ₐ[S] A)) :
    HopfAlgebra.IsCentralPoint (rootsOfUnityScalarPoints n f) := by
  rw [HopfAlgebra.isCentralPoint_def]
  intro B _ _ φ g
  apply (SpecialLinear.pointsMulEquiv (R := S) (A := B) n).injective
  rw [map_mul, map_mul, mapValue_rootsOfUnityScalarPoints,
    pointsMulEquiv_rootsOfUnityScalarPoints]
  apply Subtype.ext
  exact (Matrix.scalar_commute _ (fun r ↦ Commute.all _ r)
    (SpecialLinear.pointsMulEquiv (R := S) (A := B) n g).1).eq

/-- The scalar roots-of-unity map with codomain restricted to the universal center. -/
noncomputable def rootsOfUnityScalarCenterHom
    (A : Type u) [CommRing A] [Algebra S A] :
    WithConv (MonoidAlgebra S (Multiplicative (ZMod n)) →ₐ[S] A) →*
      HopfAlgebra.center S (coordinateHopfAlgebra S n) A :=
  (rootsOfUnityScalarPoints (R := S) n (A := A)).codRestrict
    (HopfAlgebra.center S (coordinateHopfAlgebra S n) A)
    fun f ↦ HopfAlgebra.mem_center.mpr (isCentralPoint_rootsOfUnityScalarPoints n f)

/-- The value of `rootsOfUnityScalarCenterHom` is the underlying scalar point. -/
@[simp]
theorem coe_rootsOfUnityScalarCenterHom_apply
    (A : Type u) [CommRing A] [Algebra S A]
    (f : WithConv (MonoidAlgebra S (Multiplicative (ZMod n)) →ₐ[S] A)) :
    (rootsOfUnityScalarCenterHom n A f).1 = rootsOfUnityScalarPoints n f := by
  rfl

/-- For `0 < n`, scalar roots of unity give every universally central point of `SLₙ`. -/
theorem rootsOfUnityScalarCenterHom_bijective (hn : 0 < n)
    (A : Type u) [CommRing A] [Algebra S A] :
    Function.Bijective (rootsOfUnityScalarCenterHom (S := S) n A) := by
  constructor
  · intro f g hfg
    apply rootsOfUnityScalarPoints_injective (R := S) n hn
    exact congrArg Subtype.val hfg
  · intro g
    have hgcentral :
        SpecialLinear.pointsMulEquiv (R := S) (A := A) n g.1 ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A) := by
      apply MulEquivClass.apply_mem_center
      apply HopfAlgebra.center_le_center
      exact g.2
    let c : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A) :=
      ⟨SpecialLinear.pointsMulEquiv (R := S) (A := A) n g.1, hgcentral⟩
    let ζ : rootsOfUnity n A :=
      Matrix.SpecialLinearGroup.centerMulEquivRootsOfUnityFin n hn A c
    refine ⟨(RootsOfUnityGroup.pointsMulEquiv (R := S) (A := A) n).symm ζ, ?_⟩
    apply Subtype.ext
    rw [coe_rootsOfUnityScalarCenterHom_apply]
    apply (SpecialLinear.pointsMulEquiv (R := S) (A := A) n).injective
    apply Subtype.ext
    rw [coe_pointsMulEquiv_rootsOfUnityScalarPoints, MulEquiv.apply_symm_apply,
      ← Matrix.SpecialLinearGroup.coe_centerMulEquivRootsOfUnityFin_symm_apply n hn A ζ]
    simpa only [ζ] using
      congrArg (fun x : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A) ↦
        (((x : Matrix.SpecialLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A)))
        ((Matrix.SpecialLinearGroup.centerMulEquivRootsOfUnityFin n hn A).symm_apply_apply c)

/-- For `0 < n`, scalar roots of unity identify `μₙ` with the universal center of `SLₙ`
pointwise over any commutative base ring. -/
noncomputable def rootsOfUnityScalarCenterMulEquiv (hn : 0 < n)
    (A : Type u) [CommRing A] [Algebra S A] :
    WithConv (MonoidAlgebra S (Multiplicative (ZMod n)) →ₐ[S] A) ≃*
      HopfAlgebra.center S (coordinateHopfAlgebra S n) A :=
  MulEquiv.ofBijective (rootsOfUnityScalarCenterHom (S := S) n A)
    (rootsOfUnityScalarCenterHom_bijective (S := S) n hn A)

/-- The forward map of `rootsOfUnityScalarCenterMulEquiv` is the scalar-point map. -/
@[simp]
theorem rootsOfUnityScalarCenterMulEquiv_apply (hn : 0 < n)
    (A : Type u) [CommRing A] [Algebra S A]
    (f : WithConv (MonoidAlgebra S (Multiplicative (ZMod n)) →ₐ[S] A)) :
    (rootsOfUnityScalarCenterMulEquiv n hn A f).1 = rootsOfUnityScalarPoints n f := by
  rfl

/-- Read the root of unity from the upper-left entry of a universally central `SLₙ`-point. -/
noncomputable def rootsOfUnityOfCenterPoint (hn : 0 < n)
    {A : Type u} [CommRing A] [Algebra S A]
    (g : HopfAlgebra.center S (coordinateHopfAlgebra S n) A) : rootsOfUnity n A :=
  Matrix.SpecialLinearGroup.centerMulEquivRootsOfUnityFin n hn A
    ⟨SpecialLinear.pointsMulEquiv (R := S) (A := A) n g.1, by
      apply MulEquivClass.apply_mem_center
      exact HopfAlgebra.center_le_center g.2⟩

/-- The inverse pointwise center equivalence reads off the root of unity from the central
special-linear matrix. -/
@[simp]
theorem rootsOfUnityScalarCenterMulEquiv_symm_apply (hn : 0 < n)
    (A : Type u) [CommRing A] [Algebra S A]
    (g : HopfAlgebra.center S (coordinateHopfAlgebra S n) A) :
    (rootsOfUnityScalarCenterMulEquiv (S := S) n hn A).symm g =
      (RootsOfUnityGroup.pointsMulEquiv (R := S) (A := A) n).symm
        (rootsOfUnityOfCenterPoint (S := S) n hn g) := by
  apply (rootsOfUnityScalarCenterMulEquiv (S := S) n hn A).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [rootsOfUnityScalarCenterMulEquiv_apply]
  apply (SpecialLinear.pointsMulEquiv (R := S) (A := A) n).injective
  apply Subtype.ext
  rw [coe_pointsMulEquiv_rootsOfUnityScalarPoints, MulEquiv.apply_symm_apply,
    ← Matrix.SpecialLinearGroup.coe_centerMulEquivRootsOfUnityFin_symm_apply n hn A
      (rootsOfUnityOfCenterPoint (S := S) n hn g)]
  simp only [rootsOfUnityOfCenterPoint]
  simpa only using (congrArg
    (fun c : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A) ↦
      ((c : Matrix.SpecialLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A))
    ((Matrix.SpecialLinearGroup.centerMulEquivRootsOfUnityFin n hn A).symm_apply_apply
      (⟨SpecialLinear.pointsMulEquiv (R := S) (A := A) n g.1, by
        apply MulEquivClass.apply_mem_center
        exact HopfAlgebra.center_le_center g.2⟩ :
        Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A)))).symm

variable {k : Type u} [Field k]

/-- Every roots-of-unity scalar point is a point of the represented center of `SLₙ`. -/
theorem rootsOfUnityScalarPoints_mem_centerPointsSubgroup
    {A : Type u} [CommRing A] [Algebra k A]
    (f : WithConv (MonoidAlgebra k (Multiplicative (ZMod n)) →ₐ[k] A)) :
    rootsOfUnityScalarPoints n f ∈ CommHopfAlgCat.centerPointsSubgroup
      (coordinateHopfAlgebra k n) (CommAlgCat.of k A) :=
  (CommHopfAlgCat.mem_centerPointsSubgroup_iff _ _ _).2
    (isCentralPoint_rootsOfUnityScalarPoints n f)

/-- For every value algebra, scalar roots of unity identify `μₙ` with the represented center
of `SLₙ`. -/
noncomputable def rootsOfUnityScalarCenterIso (hn : 0 < n) (A : CommAlgCat.{u} k) :
    HopfAlgebra.points (R := k)
        (H := MonoidAlgebra k (Multiplicative (ZMod n))) A ≅
      GrpCat.of (CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A) :=
  ((rootsOfUnityScalarCenterMulEquiv (S := k) n hn A).trans <|
    MulEquiv.subgroupCongr
      (CommHopfAlgCat.centerPointsSubgroup_eq_center (coordinateHopfAlgebra k n) A).symm).toGrpIso

/-- The forward component of `rootsOfUnityScalarCenterIso` is the scalar-matrix map. -/
@[simp]
theorem rootsOfUnityScalarCenterIso_hom_apply (hn : 0 < n) (A : CommAlgCat.{u} k)
    (f : HopfAlgebra.points (R := k)
      (H := MonoidAlgebra k (Multiplicative (ZMod n))) A) :
    ((rootsOfUnityScalarCenterIso n hn A).hom f).1 = rootsOfUnityScalarPoints n f := by
  rfl

/-- The inverse represented-center equivalence reads off the root of unity from the central
special-linear matrix. -/
@[simp]
theorem rootsOfUnityScalarCenterIso_inv_apply (hn : 0 < n) (A : CommAlgCat.{u} k)
    (g : CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A) :
    (rootsOfUnityScalarCenterIso n hn A).inv g =
      (RootsOfUnityGroup.pointsMulEquiv (R := k) (A := A) n).symm
        (rootsOfUnityOfCenterPoint (S := k) n hn
          (⟨g.1, by
            rw [← CommHopfAlgCat.centerPointsSubgroup_eq_center]
            exact g.2⟩ : HopfAlgebra.center k (coordinateHopfAlgebra k n) A)) := by
  -- This theorem establishes the public inverse-application rule. The isomorphism is assembled
  -- from `MulEquiv.trans` and `MulEquiv.toGrpIso`, for which there is no application rewrite
  -- lemma connecting the categorical inverse to the underlying multiplicative equivalence.
  change (rootsOfUnityScalarCenterMulEquiv (S := k) n hn A).symm _ = _
  rw [rootsOfUnityScalarCenterMulEquiv_symm_apply]
  congr 2

/-- Scalar roots of unity identify the `μₙ` point functor with the represented center
subfunctor of `SLₙ`. -/
noncomputable def rootsOfUnityScalarCenterNatIso (hn : 0 < n) :
    HopfAlgebra.pointsFunctor (R := k)
        (H := MonoidAlgebra k (Multiplicative (ZMod n))) ≅
      CommHopfAlgCat.quotientPointsSubgroupFunctor
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)) :=
  NatIso.ofComponents (rootsOfUnityScalarCenterIso n hn) (by
    intro A B φ
    ext f
    apply Subtype.ext
    -- Naturality is presented as an equality of composed `GrpCat` morphisms. There is no
    -- rewrite lemma that lowers those compositions and their concrete coercions to applications;
    -- `change` exposes that layer, after which the public component and value-map lemmas apply.
    change ((rootsOfUnityScalarCenterIso n hn B).hom
        (AlgHom.mapValue φ.hom f)).1 =
      AlgHom.mapValue φ.hom ((rootsOfUnityScalarCenterIso n hn A).hom f).1
    calc
      _ = rootsOfUnityScalarPoints n (AlgHom.mapValue φ.hom f) :=
        rootsOfUnityScalarCenterIso_hom_apply n hn B _
      _ = AlgHom.mapValue φ.hom (rootsOfUnityScalarPoints n f) :=
        (mapValue_rootsOfUnityScalarPoints n φ.hom f).symm
      _ = _ := congrArg (AlgHom.mapValue φ.hom)
        (rootsOfUnityScalarCenterIso_hom_apply n hn A f).symm)

/-- The natural isomorphism sends a `μₙ`-point to its scalar matrix. -/
@[simp]
theorem rootsOfUnityScalarCenterNatIso_hom_app_apply
    (hn : 0 < n) (A : CommAlgCat.{u} k)
    (f : HopfAlgebra.points (R := k)
      (H := MonoidAlgebra k (Multiplicative (ZMod n))) A) :
    (CategoryTheory.ConcreteCategory.hom
        (X := (HopfAlgebra.pointsFunctor (R := k)
          (H := MonoidAlgebra k (Multiplicative (ZMod n)))).obj A)
        (Y := GrpCat.of (CommHopfAlgCat.centerPointsSubgroup
          (coordinateHopfAlgebra k n) A))
        ((rootsOfUnityScalarCenterNatIso n hn).hom.app A) f).1 =
      rootsOfUnityScalarPoints n f := by
  exact rootsOfUnityScalarCenterIso_hom_apply n hn A f

/-- The inverse natural-isomorphism component reads off the root of unity from the central
special-linear matrix. -/
@[simp]
theorem rootsOfUnityScalarCenterNatIso_inv_app_apply
    (hn : 0 < n) (A : CommAlgCat.{u} k)
    (g : CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A) :
    CategoryTheory.ConcreteCategory.hom
        (X := GrpCat.of (CommHopfAlgCat.centerPointsSubgroup
          (coordinateHopfAlgebra k n) A))
        (Y := (HopfAlgebra.pointsFunctor (R := k)
          (H := MonoidAlgebra k (Multiplicative (ZMod n)))).obj A)
        ((rootsOfUnityScalarCenterNatIso n hn).inv.app A) g =
      (RootsOfUnityGroup.pointsMulEquiv (R := k) (A := A) n).symm
        (rootsOfUnityOfCenterPoint (S := k) n hn
          (⟨g.1, by
            rw [← CommHopfAlgCat.centerPointsSubgroup_eq_center]
            exact g.2⟩ : HopfAlgebra.center k (coordinateHopfAlgebra k n) A)) := by
  exact rootsOfUnityScalarCenterIso_inv_apply n hn A g

/-- The point functor of `μₙ` is naturally isomorphic to the point functor represented by the
center coordinate Hopf algebra of `SLₙ`. -/
noncomputable def rootsOfUnityScalarCenterCoordinatePointsNatIso (hn : 0 < n) :
    (CommHopfAlgCat.pointsFunctor (R := k)).obj
        (Opposite.op (CommHopfAlgCat.of k
          (MonoidAlgebra k (Multiplicative (ZMod n))))) ≅
      (CommHopfAlgCat.pointsFunctor (R := k)).obj
        (Opposite.op (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
          (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)))) :=
  rootsOfUnityScalarCenterNatIso n hn ≪≫
    (CommHopfAlgCat.quotientPointsSubgroupNatIso
      (coordinateHopfAlgebra k n)
      (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))).symm

/-- For `0 < n`, the coordinate Hopf algebra of the center of `SLₙ` is the group algebra of
`Multiplicative (ZMod n)`, the coordinate Hopf algebra of `μₙ`. -/
noncomputable def centerCoordinateIsoGroupAlgebra (hn : 0 < n) :
    CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)) ≅
      CommHopfAlgCat.of k (MonoidAlgebra k (Multiplicative (ZMod n))) :=
  Iso.unop <| (Functor.FullyFaithful.ofFullyFaithful
    (CommHopfAlgCat.pointsFunctor (R := k))).preimageIso
      (rootsOfUnityScalarCenterCoordinatePointsNatIso n hn)

/-- Applying the functor of points to `centerCoordinateIsoGroupAlgebra` recovers the
scalar-matrix natural isomorphism used to construct it. -/
theorem pointsFunctor_mapIso_centerCoordinateIsoGroupAlgebra (hn : 0 < n) :
    (CommHopfAlgCat.pointsFunctor (R := k)).mapIso
        (centerCoordinateIsoGroupAlgebra n hn).op =
      rootsOfUnityScalarCenterCoordinatePointsNatIso n hn := by
  apply Iso.ext
  exact (Functor.FullyFaithful.ofFullyFaithful
    (CommHopfAlgCat.pointsFunctor (R := k))).map_preimage _

end Center

end SpecialLinear

end TauCeti
