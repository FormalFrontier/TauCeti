/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Naturality

/-!
# The adjoint representation on the base Lie algebra

For a commutative Hopf algebra `H` over a commutative ring `R`, the adjoint action is initially
defined on the coefficient-dependent tangent modules

`Derivation R H (Bialgebra.CounitAlgebra R H A)`.

When the augmentation cotangent space is finite projective, these tangent modules are scalar
extensions of the single `R`-module dual to the cotangent space. This file transports the
coefficient-natural adjoint action across that equivalence. The result is a point representation,
its corresponding comodule, and, after choosing a finite basis, the coordinate morphism
`O(GL_n) ⟶ H` opposite to `Ad : Spec H ⟶ GL_n`.

## Main declarations

* `TauCeti.Derivation.mapValue_tangentScalarExtensionEquiv`: scalar extension of tangent vectors
  is natural in the coefficient algebra.
* `TauCeti.Derivation.adjointPointRepresentation`: the adjoint action on the base Lie algebra as a
  natural point representation.
* `TauCeti.Derivation.adjointComodule`: the corresponding right `H`-comodule.
* `TauCeti.Derivation.adjointCoordinateBialgHom`: the coordinate morphism of the adjoint
  representation in a finite basis.

## References

* J. S. Milne, *Algebraic Groups* (2017), §14.

This is the fixed-module packaging of the adjoint representation requested in Layer 2 of the
ReductiveGroups roadmap.
-/

public section

open CategoryTheory TensorProduct WithConv
open scoped TensorProduct

namespace TauCeti.Derivation

universe u v

variable {R : Type u} {H : Type v}
variable [CommRing R] [CommRing H]

section Bialgebra

variable [Bialgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

/-- Scalar extension of tangent vectors commutes with a morphism of coefficient algebras. -/
@[simp]
theorem mapValue_tangentScalarExtensionEquiv
    {A B : CommAlgCat.{max u v} R} (phi : A ⟶ B)
    (x : A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :
    mapValue phi.hom (tangentScalarExtensionEquiv (R := R) (A := H) (B := A) x) =
      tangentScalarExtensionEquiv (R := R) (A := H) (B := B)
        (GeneralLinear.scalarExtensionMap
          (V := Module.Dual R (Bialgebra.CotangentSpace R H)) phi x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a f =>
      ext h
      rw [mapValue_apply, tangentScalarExtensionEquiv_tmul_apply,
        GeneralLinear.scalarExtensionMap_tmul, tangentScalarExtensionEquiv_tmul_apply]
      rw [map_mul, phi.hom.commutes]

end Bialgebra

variable [HopfAlgebra R H]
variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

/-- Regard a point with values in `A` as one with values in the indexed copy of `A` carrying the
counit-induced `H`-algebra structure. -/
noncomputable def pointInCounitAlgebra
    (A : CommAlgCat.{max u v} R) :
    HopfAlgebra.points (H := H) A →*
      WithConv (H →ₐ[R] Bialgebra.CounitAlgebra R H A) :=
  AlgHom.mapValue
    (Bialgebra.CounitAlgebra.algEquivSelf R H A).symm.toAlgHom

omit [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)] in
/-- Regarding a point as counit-algebra-valued does not change its values. -/
@[simp]
theorem pointInCounitAlgebra_apply
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A) (h : H) :
    (pointInCounitAlgebra A g).ofConv h = g.ofConv h := by
  unfold pointInCounitAlgebra
  rw [AlgHom.mapValue_apply]
  simp only [AlgHom.comp_apply]
  exact Bialgebra.CounitAlgebra.algEquivSelf_symm_apply
    (R := R) (A := H) (B := A) (g.ofConv h)

omit [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)] in
/-- Changing the value algebra of a point commutes with regarding it as a point valued in the
counit-indexed copy of that algebra. -/
@[simp]
theorem pointInCounitAlgebra_mapPoints
    {A B : CommAlgCat.{max u v} R} (phi : A ⟶ B)
    (g : HopfAlgebra.points (H := H) A) :
    pointInCounitAlgebra B (HopfAlgebra.mapPoints (H := H) phi g) =
      AlgHom.mapValue (Bialgebra.CounitAlgebra.mapAlgHom
        (R := R) (A := H) (B := A) (C := B) phi.hom)
        (pointInCounitAlgebra A g) := by
  apply WithConv.ofConv_injective
  ext h
  rw [pointInCounitAlgebra_apply, AlgHom.mapValue_apply, HopfAlgebra.mapPoints_apply]
  simp only [AlgHom.comp_apply, Bialgebra.CounitAlgebra.mapAlgHom_apply]
  exact congrArg phi.hom (pointInCounitAlgebra_apply A g h).symm

/-- The adjoint action at a coefficient algebra, transported from coefficient-valued derivations
to the scalar extension of the dual cotangent space. -/
noncomputable def adjointAction
    (A : CommAlgCat.{max u v} R) :
    HopfAlgebra.points (H := H) A ⟶
      GeneralLinear.scalarExtensionAutomorphisms
        (V := Module.Dual R (Bialgebra.CotangentSpace R H)) A :=
  GrpCat.ofHom <|
    (LinearMap.GeneralLinearGroup.congrLinearEquiv
      (tangentScalarExtensionEquiv (R := R) (A := H) (B := A)).symm).toMonoidHom.comp
        ((adRepresentation A).asGroupHom.comp (pointInCounitAlgebra A))

/-- The transported adjoint action is conjugation of the coefficient-valued adjoint operator by
the tangent scalar-extension equivalence. -/
theorem adjointAction_apply
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A) :
    adjointAction A g =
      LinearMap.GeneralLinearGroup.congrLinearEquiv
        (tangentScalarExtensionEquiv (R := R) (A := H) (B := A)).symm
        ((adRepresentation A).asGroupHom (pointInCounitAlgebra A g)) := by
  unfold adjointAction
  rfl

/-- Transporting the fixed-module adjoint action to coefficient-valued derivations recovers
convolution conjugation. -/
@[simp]
theorem tangentScalarExtensionEquiv_adjointAction
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A)
    (x : A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :
    tangentScalarExtensionEquiv (R := R) (A := H) (B := A)
        ((adjointAction A g).val x) =
      adDerivation A (pointInCounitAlgebra A g)
        (tangentScalarExtensionEquiv (R := R) (A := H) (B := A) x) := by
  rw [adjointAction_apply, LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]
  simp only [LinearMap.GeneralLinearGroup.coe_ofLinearEquiv, LinearEquiv.trans_apply]
  rw [(tangentScalarExtensionEquiv (R := R) (A := H) (B := A)).apply_symm_apply]
  have h := DFunLike.congr_fun
    (Representation.asGroupHom_apply (adRepresentation A) (pointInCounitAlgebra A g))
    (tangentScalarExtensionEquiv (R := R) (A := H) (B := A) x)
  simpa only [LinearEquiv.symm_symm, LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
    adRepresentation_apply] using h

private theorem adjointAction_naturality
    {A B : CommAlgCat.{max u v} R} (phi : A ⟶ B)
    (g : HopfAlgebra.points (H := H) A) :
    GeneralLinear.mapScalarExtensionAutomorphisms
        (V := Module.Dual R (Bialgebra.CotangentSpace R H)) phi (adjointAction A g) =
      adjointAction B (HopfAlgebra.mapPoints (H := H) phi g) := by
  symm
  apply GeneralLinear.eq_mapScalarExtensionAutomorphisms_of_apply_scalarExtensionMap_eq
  intro x
  apply (tangentScalarExtensionEquiv (R := R) (A := H) (B := B)).injective
  calc
    tangentScalarExtensionEquiv (R := R) (A := H) (B := B)
          ((adjointAction B (HopfAlgebra.mapPoints (H := H) phi g)).val
            (GeneralLinear.scalarExtensionMap
              (V := Module.Dual R (Bialgebra.CotangentSpace R H)) phi x)) =
        adDerivation B
          (pointInCounitAlgebra B (HopfAlgebra.mapPoints (H := H) phi g))
          (tangentScalarExtensionEquiv (R := R) (A := H) (B := B)
            (GeneralLinear.scalarExtensionMap
              (V := Module.Dual R (Bialgebra.CotangentSpace R H)) phi x)) :=
      tangentScalarExtensionEquiv_adjointAction B _ _
    _ = adDerivation B
          (pointInCounitAlgebra B (HopfAlgebra.mapPoints (H := H) phi g))
          (mapValue phi.hom
            (tangentScalarExtensionEquiv (R := R) (A := H) (B := A) x)) := by
      rw [mapValue_tangentScalarExtensionEquiv]
    _ = mapValue phi.hom
          (adDerivation A (pointInCounitAlgebra A g)
            (tangentScalarExtensionEquiv (R := R) (A := H) (B := A) x)) := by
      rw [pointInCounitAlgebra_mapPoints]
      exact (mapValue_adDerivation phi.hom (pointInCounitAlgebra A g)
        (tangentScalarExtensionEquiv (R := R) (A := H) (B := A) x)).symm
    _ = mapValue phi.hom
          (tangentScalarExtensionEquiv (R := R) (A := H) (B := A)
            ((adjointAction A g).val x)) := by
      rw [tangentScalarExtensionEquiv_adjointAction]
    _ = tangentScalarExtensionEquiv (R := R) (A := H) (B := B)
          (GeneralLinear.scalarExtensionMap
            (V := Module.Dual R (Bialgebra.CotangentSpace R H)) phi
              ((adjointAction A g).val x)) :=
      mapValue_tangentScalarExtensionEquiv phi _

/-- The adjoint action on the base Lie algebra, expressed as a natural point representation on
the dual of the augmentation cotangent space. -/
noncomputable def adjointPointRepresentation :
    HopfAlgebra.PointRepresentation (R := R) (H := H)
      (V := Module.Dual R (Bialgebra.CotangentSpace R H)) where
  app A := adjointAction A ≫
    eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj
      (V := Module.Dual R (Bialgebra.CotangentSpace R H)) A).symm
  naturality A B phi := by
    -- The functor object is definitionally the concrete scalar-extension automorphism group,
    -- but that equality is opaque; no rewrite lemma exposes this natural-transformation field.
    change
      HopfAlgebra.mapPoints (H := H) phi ≫ adjointAction B ≫
          eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj
            (V := Module.Dual R (Bialgebra.CotangentSpace R H)) B).symm =
        adjointAction A ≫
          eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj
            (V := Module.Dual R (Bialgebra.CotangentSpace R H)) A).symm ≫
          (GeneralLinear.scalarExtensionAutomorphismsFunctor
            (V := Module.Dual R (Bialgebra.CotangentSpace R H))).map phi
    have hraw :
        HopfAlgebra.mapPoints (H := H) phi ≫ adjointAction B =
          adjointAction A ≫
            GeneralLinear.mapScalarExtensionAutomorphisms
              (V := Module.Dual R (Bialgebra.CotangentSpace R H)) phi := by
      apply GrpCat.ext
      intro g
      exact (adjointAction_naturality phi g).symm
    rw [GeneralLinear.scalarExtensionAutomorphismsFunctor_map]
    rw [← Category.assoc, hraw]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The concrete action of the adjoint point representation is the transported convolution
adjoint action. -/
@[simp]
theorem adjointPointRepresentation_action
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A) :
    (adjointPointRepresentation (R := R) (H := H)).action A g = adjointAction A g := by
  rw [HopfAlgebra.PointRepresentation.action_def]
  unfold adjointPointRepresentation
  -- The concrete action inserts and then removes the functor object's equality transport.
  change
    ((adjointAction A ≫
      eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj
        (V := Module.Dual R (Bialgebra.CotangentSpace R H)) A).symm) ≫
      eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj
        (V := Module.Dual R (Bialgebra.CotangentSpace R H)) A)) g = adjointAction A g
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The adjoint comodule on the dual of the augmentation cotangent space. -/
@[irreducible]
noncomputable def adjointComodule :
    Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
  HopfAlgebra.PointRepresentation.toComodule (adjointPointRepresentation (R := R) (H := H))

/-- The adjoint coaction is the flipped action of the universal point. -/
@[simp]
theorem adjointComodule_coact_apply
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    (adjointComodule (R := R) (H := H)).coact x =
      TensorProduct.comm R H (Module.Dual R (Bialgebra.CotangentSpace R H))
        (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id
          (((adjointPointRepresentation (R := R) (H := H)).action
            (CommAlgCat.of R (ULift.{max u v} H))
            (toConv ULift.algEquiv.symm.toAlgHom)).val (1 ⊗ₜ[R] x))) := by
  unfold adjointComodule
  exact HopfAlgebra.PointRepresentation.toComodule_coact_apply _ x

/-- The point action of the adjoint comodule is convolution conjugation after the canonical
scalar-extension identification of tangent vectors. -/
theorem tangentScalarExtensionEquiv_adjointComodule_endOfPoint
    (A : CommAlgCat.{max u v} R) (g : HopfAlgebra.points (H := H) A)
    (x : A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :
    tangentScalarExtensionEquiv (R := R) (A := H) (B := A)
        (letI := adjointComodule (R := R) (H := H)
         Comodule.endOfPoint (Module.Dual R (Bialgebra.CotangentSpace R H)) g.ofConv x) =
      adDerivation A (pointInCounitAlgebra A g)
        (tangentScalarExtensionEquiv (R := R) (A := H) (B := A) x) := by
  let : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  have haction := HopfAlgebra.PointRepresentation.ofComodule_action_val_eq_endOfPoint
    (adjointComodule (R := R) (H := H)) A g
  have hrecover :
      HopfAlgebra.PointRepresentation.ofComodule
          (adjointComodule (R := R) (H := H)) =
        adjointPointRepresentation (R := R) (H := H) := by
    unfold adjointComodule
    exact HopfAlgebra.PointRepresentation.ofComodule_toComodule _
  rw [hrecover, adjointPointRepresentation_action] at haction
  rw [← haction]
  exact tangentScalarExtensionEquiv_adjointAction A g x

/-- The coordinate Hopf-algebra morphism opposite to the adjoint representation in a basis
indexed by `Fin n`. -/
noncomputable def adjointCoordinateBialgHom {n : ℕ}
    (b : Module.Basis (Fin n) R (Module.Dual R (Bialgebra.CotangentSpace R H))) :
    GeneralLinear.coordinateHopfAlgebra R n →ₐc[R] H := by
  letI := adjointComodule (R := R) (H := H)
  exact Comodule.coordinateBialgHom b

/-- The adjoint coordinate morphism sends a generic matrix entry to the corresponding matrix
coefficient of the adjoint comodule. -/
@[simp]
theorem adjointCoordinateBialgHom_X {n : ℕ}
    (b : Module.Basis (Fin n) R (Module.Dual R (Bialgebra.CotangentSpace R H)))
    (i j : Fin n) :
    adjointCoordinateBialgHom b
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
          (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, j)))) =
      (let _ : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
          adjointComodule (R := R) (H := H)
       Comodule.coefficientMatrix (C := H) b i j) := by
  let : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  unfold adjointCoordinateBialgHom
  exact Comodule.coordinateBialgHom_X b i j

/-- The adjoint coordinate morphism sends an antipode generator to the antipode of the
corresponding matrix coefficient. -/
@[simp]
theorem adjointCoordinateBialgHom_antipode_X {n : ℕ}
    (b : Module.Basis (Fin n) R (Module.Dual R (Bialgebra.CotangentSpace R H)))
    (i j : Fin n) :
    adjointCoordinateBialgHom b
        (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
          ((GeneralLinear.localizedGenericMatrix R n)⁻¹ i j)) =
      (let _ : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
          adjointComodule (R := R) (H := H)
       HopfAlgebra.antipode R (Comodule.coefficientMatrix (C := H) b i j)) := by
  let : Comodule R H (Module.Dual R (Bialgebra.CotangentSpace R H)) :=
    adjointComodule (R := R) (H := H)
  unfold adjointCoordinateBialgHom
  exact Comodule.coordinateBialgHom_antipode_X b i j

end TauCeti.Derivation
