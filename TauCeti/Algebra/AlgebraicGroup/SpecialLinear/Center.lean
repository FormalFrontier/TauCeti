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

* `TauCeti.SpecialLinear.scalarRootsPoints`: the scalar-matrix map from `μₙ`-points to
  `SLₙ`-points.
* `TauCeti.SpecialLinear.scalarRootsCenterNatIso`: the natural isomorphism from `μₙ`-points
  to the represented center of `SLₙ`.
* `TauCeti.SpecialLinear.centerCoordinateIso`: the center coordinate Hopf algebra of `SLₙ`
  is the group algebra of `Multiplicative (ZMod n)`.

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

variable {R : Type u} [CommRing R]
variable (n : ℕ)

/-- For `0 < n`, the center of the special linear group is the group of `n`th roots of unity.
This specializes Mathlib's finite-index-type equivalence to matrices indexed by `Fin n`. -/
noncomputable def centerMulEquivRootsOfUnity (hn : 0 < n)
    (A : Type v) [CommRing A] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A) ≃* rootsOfUnity n A :=
  (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := A)
    (⟨0, hn⟩ : Fin n)).trans <| MulEquiv.subgroupCongr <| by
      rw [Fintype.card_fin]

/-- The inverse center equivalence sends a root of unity to its scalar matrix. -/
@[simp]
theorem coe_centerMulEquivRootsOfUnity_symm_apply (hn : 0 < n)
    (A : Type v) [CommRing A] (ζ : rootsOfUnity n A) :
    (((centerMulEquivRootsOfUnity n hn A).symm ζ :
        Matrix.SpecialLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) =
      Matrix.scalar (Fin n) ((ζ : Aˣ) : A) := by
  let hcard : rootsOfUnity (Fintype.card (Fin n)) A = rootsOfUnity n A :=
    congrArg (fun m ↦ rootsOfUnity m A) (Fintype.card_fin n)
  have hunit :
      (((MulEquiv.subgroupCongr hcard).symm ζ :
        rootsOfUnity (Fintype.card (Fin n)) A) : Aˣ) = (ζ : Aˣ) :=
    MulEquiv.subgroupCongr_symm_apply hcard ζ
  have hval := congrArg Units.val hunit
  -- Unfolding the two equivalences leaves the scalar action used by Mathlib's inverse.
  change (((((MulEquiv.subgroupCongr hcard).symm ζ :
      rootsOfUnity (Fintype.card (Fin n)) A) : Aˣ) : A) •
        (1 : Matrix (Fin n) (Fin n) A)) = Matrix.scalar (Fin n) ((ζ : Aˣ) : A)
  rw [hval, Matrix.smul_one_eq_diagonal]
  rfl

/-- Send a roots-of-unity point to the corresponding scalar special-linear point. -/
noncomputable def scalarRootsPoints {A : Type v} [CommRing A] [Algebra R A] :
    WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A) →*
      WithConv (coordinateHopfAlgebra R n →ₐ[R] A) :=
  (TauCeti.SpecialLinear.pointsMulEquiv (R := R) (A := A) n).symm.toMonoidHom.comp
    (({
      toFun ζ := ⟨Matrix.scalar (Fin n) (((ζ : Aˣ) : A)), by
        change (Matrix.diagonal fun _ : Fin n ↦ (((ζ : Aˣ) : A))).det = 1
        rw [Matrix.det_diagonal]
        simpa using congrArg Units.val ζ.property⟩
      map_one' := by
        apply Subtype.ext
        change Matrix.scalar (Fin n) (1 : A) = 1
        exact map_one (Matrix.scalar (Fin n))
      map_mul' ζ ξ := by
        apply Subtype.ext
        change Matrix.scalar (Fin n) ((((ζ * ξ : rootsOfUnity n A) : Aˣ) : A)) =
          Matrix.scalar (Fin n) (((ζ : Aˣ) : A)) *
            Matrix.scalar (Fin n) (((ξ : Aˣ) : A))
        simp
    } : rootsOfUnity n A →* Matrix.SpecialLinearGroup (Fin n) A).comp
      (RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) n).toMonoidHom)

/-- Under the standard point equivalences, `scalarRootsPoints` is the central scalar matrix
attached to a root of unity. -/
@[simp]
theorem pointsMulEquiv_scalarRootsPoints {A : Type v} [CommRing A] [Algebra R A]
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    TauCeti.SpecialLinear.pointsMulEquiv (R := R) (A := A) n
        (scalarRootsPoints n f) =
      (⟨Matrix.scalar (Fin n)
          ((RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) n f : Aˣ) : A), by
        change (Matrix.diagonal fun _ : Fin n ↦
          ((RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) n f : Aˣ) : A)).det = 1
        rw [Matrix.det_diagonal]
        simpa using congrArg Units.val
          (RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) n f).property⟩ :
        Matrix.SpecialLinearGroup (Fin n) A) := by
  change (TauCeti.SpecialLinear.pointsMulEquiv (R := R) (A := A) n)
    ((TauCeti.SpecialLinear.pointsMulEquiv (R := R) (A := A) n).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The central special-linear matrix attached to a root of unity is a scalar matrix. -/
@[simp]
theorem coe_pointsMulEquiv_scalarRootsPoints {A : Type v} [CommRing A] [Algebra R A]
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    ((TauCeti.SpecialLinear.pointsMulEquiv (R := R) (A := A) n
        (scalarRootsPoints n f) :
        Matrix.SpecialLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A) =
      Matrix.scalar (Fin n)
        ((RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) n f : Aˣ) : A) := by
  rw [pointsMulEquiv_scalarRootsPoints]

/-- For `0 < n`, the scalar roots-of-unity map is injective. -/
theorem scalarRootsPoints_injective (hn : 0 < n)
    {A : Type v} [CommRing A] [Algebra R A] :
    Function.Injective (scalarRootsPoints (R := R) n (A := A)) := by
  intro f g hfg
  apply (RootsOfUnityGroup.pointsMulEquiv (R := R) (A := A) n).injective
  apply Subtype.ext
  apply Units.ext
  have h := congrArg (TauCeti.SpecialLinear.pointsMulEquiv (R := R) (A := A) n) hfg
  have hmatrix := congrArg Subtype.val h
  rw [coe_pointsMulEquiv_scalarRootsPoints,
    coe_pointsMulEquiv_scalarRootsPoints] at hmatrix
  have hentry := congrFun₂ hmatrix (⟨0, hn⟩ : Fin n) ⟨0, hn⟩
  simpa using hentry

/-- The scalar roots-of-unity construction is natural in the value algebra. -/
theorem mapValue_scalarRootsPoints {A : Type v} {B : Type w}
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    AlgHom.mapValue (H := coordinateHopfAlgebra R n) φ (scalarRootsPoints n f) =
      scalarRootsPoints n
        (AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (ZMod n))) φ f) := by
  apply (SpecialLinear.pointsMulEquiv (R := R) (A := B) n).injective
  have hmap := SpecialLinear.pointsMulEquiv_mapValue (R := R) (A := A) (B := B) n φ
    (scalarRootsPoints n f)
  rw [hmap]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe,
    coe_pointsMulEquiv_scalarRootsPoints, coe_pointsMulEquiv_scalarRootsPoints]
  ext i j
  rw [RootsOfUnityGroup.pointsMulEquiv_mapValue]
  by_cases hij : i = j <;>
    simp [hij, RootsOfUnityGroup.pointsMulEquiv_apply]

section Center

variable {k : Type u} [Field k]

/-- Every roots-of-unity scalar point is a point of the represented center of `SLₙ`. -/
theorem scalarRootsPoints_mem_centerPointsSubgroup {A : Type u} [CommRing A] [Algebra k A]
    (f : WithConv (MonoidAlgebra k (Multiplicative (ZMod n)) →ₐ[k] A)) :
    scalarRootsPoints n f ∈ CommHopfAlgCat.centerPointsSubgroup
      (coordinateHopfAlgebra k n) (CommAlgCat.of k A) := by
  rw [CommHopfAlgCat.mem_centerPointsSubgroup_iff, HopfAlgebra.isCentralPoint_def]
  intro B _ _ φ g
  apply (SpecialLinear.pointsMulEquiv (R := k) (A := B) n).injective
  rw [map_mul, map_mul, mapValue_scalarRootsPoints,
    pointsMulEquiv_scalarRootsPoints]
  apply Subtype.ext
  exact (Matrix.scalar_commute _ (fun r ↦ Commute.all _ r)
    (SpecialLinear.pointsMulEquiv (R := k) (A := B) n g).1).eq

/-- The scalar roots-of-unity map with codomain restricted to the represented center. -/
noncomputable def scalarRootsCenterHom (A : CommAlgCat.{u} k) :
    HopfAlgebra.points (R := k)
        (H := MonoidAlgebra k (Multiplicative (ZMod n))) A →*
      CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A :=
  (scalarRootsPoints (R := k) n (A := A)).codRestrict
    (CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A)
    (scalarRootsPoints_mem_centerPointsSubgroup n)

/-- The value of `scalarRootsCenterHom` is the underlying scalar special-linear point. -/
@[simp]
theorem coe_scalarRootsCenterHom_apply (A : CommAlgCat.{u} k)
    (f : HopfAlgebra.points (R := k)
      (H := MonoidAlgebra k (Multiplicative (ZMod n))) A) :
    (scalarRootsCenterHom n A f).1 = scalarRootsPoints n f := by
  rfl

/-- For `0 < n`, scalar roots of unity give every universally central point of `SLₙ`. -/
theorem scalarRootsCenterHom_bijective (hn : 0 < n) (A : CommAlgCat.{u} k) :
    Function.Bijective (scalarRootsCenterHom n A) := by
  constructor
  · intro f g hfg
    apply scalarRootsPoints_injective (R := k) n hn
    exact congrArg Subtype.val hfg
  · intro g
    have hgcentral :
        SpecialLinear.pointsMulEquiv (R := k) (A := A) n g.1 ∈
          Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A) := by
      apply MulEquivClass.apply_mem_center
      apply HopfAlgebra.center_le_center
      rw [← CommHopfAlgCat.centerPointsSubgroup_eq_center]
      exact g.2
    let c : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A) :=
      ⟨SpecialLinear.pointsMulEquiv (R := k) (A := A) n g.1, hgcentral⟩
    let ζ : rootsOfUnity n A :=
      centerMulEquivRootsOfUnity n hn A c
    refine ⟨(RootsOfUnityGroup.pointsMulEquiv (R := k) (A := A) n).symm ζ, ?_⟩
    apply Subtype.ext
    rw [coe_scalarRootsCenterHom_apply]
    apply (SpecialLinear.pointsMulEquiv (R := k) (A := A) n).injective
    apply Subtype.ext
    rw [coe_pointsMulEquiv_scalarRootsPoints, MulEquiv.apply_symm_apply,
      ← coe_centerMulEquivRootsOfUnity_symm_apply n hn A ζ]
    simpa only [ζ] using
      congrArg (fun x : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) A) ↦
        (((x : Matrix.SpecialLinearGroup (Fin n) A) : Matrix (Fin n) (Fin n) A)))
        ((centerMulEquivRootsOfUnity n hn A).symm_apply_apply c)

/-- For every value algebra, scalar roots of unity identify `μₙ` with the represented center
of `SLₙ`. -/
noncomputable def scalarRootsCenterIso (hn : 0 < n) (A : CommAlgCat.{u} k) :
    HopfAlgebra.points (R := k)
        (H := MonoidAlgebra k (Multiplicative (ZMod n))) A ≅
      GrpCat.of (CommHopfAlgCat.centerPointsSubgroup (coordinateHopfAlgebra k n) A) :=
  (MulEquiv.ofBijective (scalarRootsCenterHom n A)
    (scalarRootsCenterHom_bijective n hn A)).toGrpIso

/-- The forward component of `scalarRootsCenterIso` is the scalar-matrix homomorphism. -/
@[simp]
theorem scalarRootsCenterIso_hom_apply (hn : 0 < n) (A : CommAlgCat.{u} k)
    (f : HopfAlgebra.points (R := k)
      (H := MonoidAlgebra k (Multiplicative (ZMod n))) A) :
    (scalarRootsCenterIso n hn A).hom f = scalarRootsCenterHom n A f := by
  rfl

/-- Scalar roots of unity identify the `μₙ` point functor with the represented center
subfunctor of `SLₙ`. -/
noncomputable def scalarRootsCenterNatIso (hn : 0 < n) :
    HopfAlgebra.pointsFunctor (R := k)
        (H := MonoidAlgebra k (Multiplicative (ZMod n))) ≅
      CommHopfAlgCat.quotientPointsSubgroupFunctor
        (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)) :=
  NatIso.ofComponents (scalarRootsCenterIso n hn) (by
    intro A B φ
    ext f
    apply Subtype.ext
    -- The component and its application lemma cannot be used while this natural isomorphism is
    -- being constructed. After subgroup extensionality, `codRestrict` and the restricted functor
    -- map reduce definitionally, leaving precisely the scalar-point naturality theorem.
    exact (mapValue_scalarRootsPoints n φ.hom f).symm)

/-- The natural isomorphism sends a `μₙ`-point to its scalar matrix. -/
@[simp]
theorem scalarRootsCenterNatIso_hom_app_apply (hn : 0 < n) (A : CommAlgCat.{u} k)
    (f : HopfAlgebra.points (R := k)
      (H := MonoidAlgebra k (Multiplicative (ZMod n))) A) :
    CategoryTheory.ConcreteCategory.hom
        (X := (HopfAlgebra.pointsFunctor (R := k)
          (H := MonoidAlgebra k (Multiplicative (ZMod n)))).obj A)
        (Y := GrpCat.of (CommHopfAlgCat.centerPointsSubgroup
          (coordinateHopfAlgebra k n) A))
        ((scalarRootsCenterNatIso n hn).hom.app A) f =
      scalarRootsCenterHom n A f := by
  rfl

/-- The point functor of `μₙ` is naturally isomorphic to the point functor represented by the
center coordinate Hopf algebra of `SLₙ`. -/
noncomputable def scalarRootsCenterCoordinatePointsNatIso (hn : 0 < n) :
    (CommHopfAlgCat.pointsFunctor (R := k)).obj
        (Opposite.op (CommHopfAlgCat.of k
          (MonoidAlgebra k (Multiplicative (ZMod n))))) ≅
      (CommHopfAlgCat.pointsFunctor (R := k)).obj
        (Opposite.op (CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
          (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)))) :=
  scalarRootsCenterNatIso n hn ≪≫
    (CommHopfAlgCat.quotientPointsSubgroupNatIso
      (coordinateHopfAlgebra k n)
      (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n))).symm

/-- For `0 < n`, the coordinate Hopf algebra of the center of `SLₙ` is the group algebra of
`Multiplicative (ZMod n)`, the coordinate Hopf algebra of `μₙ`. -/
noncomputable def centerCoordinateIso (hn : 0 < n) :
    CommHopfAlgCat.quotient (coordinateHopfAlgebra k n)
        (CommHopfAlgCat.centerDefiningIdeal (coordinateHopfAlgebra k n)) ≅
      CommHopfAlgCat.of k (MonoidAlgebra k (Multiplicative (ZMod n))) :=
  Iso.unop <| (Functor.FullyFaithful.ofFullyFaithful
    (CommHopfAlgCat.pointsFunctor (R := k))).preimageIso
      (scalarRootsCenterCoordinatePointsNatIso n hn)

/-- Applying the functor of points to `centerCoordinateIso` recovers the scalar-matrix natural
isomorphism used to construct it. -/
theorem pointsFunctor_mapIso_centerCoordinateIso (hn : 0 < n) :
    (CommHopfAlgCat.pointsFunctor (R := k)).mapIso (centerCoordinateIso n hn).op =
      scalarRootsCenterCoordinatePointsNatIso n hn := by
  apply Iso.ext
  exact (Functor.FullyFaithful.ofFullyFaithful
    (CommHopfAlgCat.pointsFunctor (R := k))).map_preimage _

end Center

end SpecialLinear

end TauCeti
