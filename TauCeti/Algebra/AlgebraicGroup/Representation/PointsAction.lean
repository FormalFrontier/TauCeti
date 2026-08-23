/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.PointsFunctor
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.PointsAction
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# The points action of a comodule, by automorphisms

Over a Hopf algebra the points form a group under convolution — the points of the
corresponding affine group scheme, when `H` is commutative — so the points action of
a comodule (`TauCeti.Comodule.endOfPoint`,
`TauCeti.Comodule.pointsRepresentation`) lands in the units of the endomorphism
monoid: the action upgrades to linear automorphisms of the scalar extension via
`Representation.asGroupHom`, with inverses provided by the group structure rather
than by an antipode computation. For points valued in the base ring, the scalar-extension
action transports across `R ⊗[R] V ≃ₗ[R] V` to a representation on `V` itself.

## Main declarations

* `TauCeti.Comodule.pointsAction`: the action of the group of points by linear
  automorphisms of `A ⊗[R] V`.
* `TauCeti.Comodule.pointsAction_corestrict`: compatibility of point actions with
  corestriction and precomposition, also provided for bundled finite comodules by
  `TauCeti.Comodule.pointsAction_corestrict_obj`.
* `TauCeti.Comodule.basePointsRepresentation`: the action of base-valued points on the original
  comodule.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace Comodule

open _root_.Coalgebra WithConv TensorProduct

variable {R H V A : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
  [AddCommMonoid V] [Module R V] [Comodule R H V]
  [CommSemiring A] [Algebra R A]

variable (V) in
/-- Over a Hopf algebra the points act by linear automorphisms of the scalar
extension: the group of points lands in the units of the endomorphism monoid, with
inverses provided by the group structure rather than by an antipode computation. -/
noncomputable def pointsAction :
    WithConv (H →ₐ[R] A) →* ((A ⊗[R] V) ≃ₗ[A] (A ⊗[R] V)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[R] V)).toMonoidHom.comp
    (pointsRepresentation V).asGroupHom

variable (V) in
@[simp]
lemma pointsAction_toLinearMap (g : WithConv (H →ₐ[R] A)) :
    (pointsAction V g : A ⊗[R] V →ₗ[A] A ⊗[R] V) = endOfPoint V g.ofConv := by
  -- `pointsAction` has no equation lemma to rewrite with; `change` spells out its
  -- definitional unfolding once, explicitly.
  change ((LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[R] V))
    ((pointsRepresentation V).asGroupHom g) : A ⊗[R] V →ₗ[A] A ⊗[R] V) = _
  rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
    Representation.asGroupHom_apply, pointsRepresentation_apply]

universe u v w x y

section BasePointsRepresentation

variable {R : Type u} {H : Type v}
variable [CommRing R] [Semiring H] [HopfAlgebra R H]

/-- The representation of the group of base-valued points on the original comodule.

`pointsRepresentation` acts on `R ⊗[R] M`; this is its transport across the canonical
equivalence `R ⊗[R] M ≃ₗ[R] M`. -/
noncomputable def basePointsRepresentation
    (M : Type w) [AddCommMonoid M] [Module R M] [Comodule R H M] :
    Representation R (HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) M where
  toFun g :=
    (TensorProduct.lid R M).toLinearMap ∘ₗ
      pointsRepresentation M g ∘ₗ
        (TensorProduct.lid R M).symm.toLinearMap
  map_one' := by
    rw [map_one]
    ext m
    simp
  map_mul' g h := by
    rw [map_mul]
    ext m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Module.End.mul_apply,
      LinearEquiv.symm_apply_apply]

variable {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- A base-valued point acts on `m` by contracting the coefficient leg of its coaction. -/
@[simp]
theorem basePointsRepresentation_apply (g : HopfAlgebra.points
    (R := R) (H := H) (CommAlgCat.of R R)) (m : M) :
    basePointsRepresentation (H := H) M g m =
      TensorProduct.lid R M (endOfPoint M g.ofConv (1 ⊗ₜ[R] m)) := by
  -- Expose the transported action once so `pointsRepresentation_apply` can rewrite it.
  change (TensorProduct.lid R M)
    (pointsRepresentation M g ((TensorProduct.lid R M).symm m)) = _
  rw [pointsRepresentation_apply]
  simp

/-- The scalar-extension action of a base-valued point is the pure tensor of its action on the
original comodule. -/
theorem endOfPoint_one_tmul_eq_tmul_basePointsRepresentation
    (g : HopfAlgebra.points (R := R) (H := H) (CommAlgCat.of R R)) (m : M) :
    endOfPoint M g.ofConv (1 ⊗ₜ[R] m) =
      1 ⊗ₜ[R] basePointsRepresentation (H := H) M g m := by
  apply (TensorProduct.lid R M).injective
  rw [basePointsRepresentation_apply]
  simp

section Corestrict

variable {H₁ : Type v} {H₂ : Type x} [Semiring H₁] [Semiring H₂]
variable [HopfAlgebra R H₁] [HopfAlgebra R H₂]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Comodule R H₁ M]

/-- Acting by a base-valued point on a corestricted comodule agrees with acting by the point
precomposed with the bialgebra morphism. -/
theorem basePointsRepresentation_corestrict (φ : H₁ →ₐc[R] H₂)
    (g : HopfAlgebra.points (R := R) (H := H₂) (CommAlgCat.of R R)) :
    (letI : Comodule R H₂ M := Corestrict φ.toCoalgHom
     basePointsRepresentation (R := R) (H := H₂) M g) =
      basePointsRepresentation (R := R) (H := H₁) M (AlgHom.mapDomain φ g) := by
  let _ : Comodule R H₂ M := Corestrict φ.toCoalgHom
  apply LinearMap.ext
  intro m
  rw [basePointsRepresentation_apply, basePointsRepresentation_apply]
  congr 1
  exact LinearMap.congr_fun (endOfPoint_corestrict φ g.ofConv) (1 ⊗ₜ[R] m)

end Corestrict

end BasePointsRepresentation

section Corestrict

variable {R : Type u} {H₁ : Type v} {H₂ : Type w} {A : Type x}
variable [CommSemiring R] [Semiring H₁] [Semiring H₂]
variable [CommSemiring A] [Algebra R A]

section HopfAlgebra

variable [HopfAlgebra R H₁] [HopfAlgebra R H₂]
variable {V : Type*} [AddCommMonoid V] [Module R V] [Comodule R H₁ V]

/-- The linear action of a precomposed point agrees with the action of the original point on
the corestricted comodule. -/
theorem pointsAction_corestrict (φ : H₁ →ₐc[R] H₂)
    (g : WithConv (H₂ →ₐ[R] A)) :
    (letI : Comodule R H₂ V := Corestrict φ.toCoalgHom
     pointsAction V g) = pointsAction V (AlgHom.mapDomain φ g) := by
  let : Comodule R H₂ V := Corestrict φ.toCoalgHom
  apply LinearEquiv.ext
  exact LinearMap.congr_fun <|
    (pointsAction_toLinearMap V g).trans <|
      (endOfPoint_corestrict φ g.ofConv).trans <|
        (by
          rw [AlgHom.mapDomain_apply, ofConv_toConv]
          exact (pointsAction_toLinearMap V
            (toConv (g.ofConv.comp (φ : H₁ →ₐ[R] H₂)))).symm)

/-- Simp-normal form of `pointsAction_corestrict`, with the precomposed point written
after normalization by `AlgHom.mapDomain_apply`. -/
@[simp]
theorem pointsAction_corestrict_toConv_comp (φ : H₁ →ₐc[R] H₂)
    (g : WithConv (H₂ →ₐ[R] A)) :
    (letI : Comodule R H₂ V := Corestrict φ.toCoalgHom
     pointsAction V g) =
      pointsAction V (toConv (g.ofConv.comp (φ : H₁ →ₐ[R] H₂))) := by
  simpa only [AlgHom.mapDomain_apply] using pointsAction_corestrict φ g

/-- Bundled finite-comodule form of `pointsAction_corestrict`. This avoids exposing the
definitionally equal comodule instance carried by the corestricted object to callers. -/
theorem pointsAction_corestrict_obj (φ : H₁ →ₐc[R] H₂)
    (M : FGComoduleCat.{u, v, y} R H₁) (g : WithConv (H₂ →ₐ[R] A)) :
    pointsAction ((FGComoduleCat.corestrict φ.toCoalgHom).obj M) g =
      pointsAction M (AlgHom.mapDomain φ g) := by
  -- The bundled object's comodule instance is definitionally `Corestrict`; expose that
  -- identification once here so downstream proofs can rewrite by a named theorem.
  change (letI : Comodule R H₂ M := Corestrict φ.toCoalgHom
    pointsAction M g) = pointsAction M (AlgHom.mapDomain φ g)
  exact pointsAction_corestrict φ g

/-- Simp-normal form of `pointsAction_corestrict_obj`, with the precomposed point written
after normalization by `AlgHom.mapDomain_apply`. -/
-- Prefer this bundled normal form before `corestrict_obj_coe` exposes the carrier.
@[simp↓ high]
theorem pointsAction_corestrict_obj_toConv_comp (φ : H₁ →ₐc[R] H₂)
    (M : FGComoduleCat.{u, v, y} R H₁) (g : WithConv (H₂ →ₐ[R] A)) :
    pointsAction ((FGComoduleCat.corestrict φ.toCoalgHom).obj M) g =
      pointsAction M (toConv (g.ofConv.comp (φ : H₁ →ₐ[R] H₂))) := by
  simpa only [AlgHom.mapDomain_apply] using pointsAction_corestrict_obj φ M g

end HopfAlgebra

end Corestrict

end Comodule

end TauCeti
