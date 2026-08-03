/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Basic

/-!
# Morphisms of point representations and comodules

For two natural point representations of the affine group represented by a commutative Hopf
algebra, this file characterizes the linear maps between their recovered comodules. A linear map
is colinear exactly when every scalar extension intertwines the actions of every algebra-valued
point. It also records the specialization to point representations induced by two given
comodules.

The converse uses the universal point of the Hopf algebra: evaluating equivariance there recovers
the colinearity square. Consequently the pointwise condition ranges over all commutative value
algebras, including nonreduced ones.

## Main declarations

* `TauCeti.HopfAlgebra.PointRepresentation.map_coact_iff_baseChange_comp_action`: the
  fixed-morphism representation--comodule dictionary for arbitrary point representations.
* `TauCeti.HopfAlgebra.PointRepresentation.map_coact_iff_baseChange_comp_ofComodule_action`: the
  specialization to point actions induced by explicit comodules.

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter VIII, §§2, 4, and 6.
-/

public section

open CategoryTheory TensorProduct WithConv
open scoped TensorProduct

namespace TauCeti.HopfAlgebra.PointRepresentation

universe u v w

variable {R : Type u} {H : Type v} {V W : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid V] [Module R V]
variable [AddCommMonoid W] [Module R W]

/-- A linear map between two natural point representations is colinear between their recovered
comodules if and only if all its scalar extensions intertwine every algebra-valued point action.

The two carriers share a universe so that the point representations are defined on the same
literal category of value algebras. No finiteness or flatness assumption is required. -/
theorem map_coact_iff_baseChange_comp_action
    (Theta : PointRepresentation (R := R) (H := H) (V := V))
    (Psi : PointRepresentation (R := R) (H := H) (V := W)) (f : V →ₗ[R] W) :
    TensorProduct.map f LinearMap.id ∘ₗ (toComodule Theta).coact =
        (toComodule Psi).coact ∘ₗ f ↔
      ∀ (A : CommAlgCat.{max u v w} R) (x : points (H := H) A),
        f.baseChange A ∘ₗ (Theta.action A x).val =
          (Psi.action A x).val ∘ₗ f.baseChange A := by
  constructor
  · intro hcolinear
    let : Comodule R H V := toComodule Theta
    let : Comodule R H W := toComodule Psi
    let fHom : Comodule.Hom R H V W :=
      { toLinearMap := f
        map_coact := hcolinear }
    intro A x
    have hTheta :
        (Theta.action A x).val = Comodule.endOfPoint V x.ofConv := by
      simpa only [ofComodule_toComodule] using
        (ofComodule_action_val_eq_endOfPoint (toComodule Theta) A x)
    have hPsi :
        (Psi.action A x).val = Comodule.endOfPoint W x.ofConv := by
      simpa only [ofComodule_toComodule] using
        (ofComodule_action_val_eq_endOfPoint (toComodule Psi) A x)
    rw [hTheta, hPsi]
    simpa only [fHom] using Comodule.baseChange_comp_endOfPoint fHom x.ofConv
  · intro hintertwines
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply]
    rw [toComodule_coact_apply, toComodule_coact_apply]
    have huniversal := LinearMap.congr_fun
      (hintertwines (CommAlgCat.of R (ULift.{max u v w} H))
        (toConv ULift.algEquiv.symm.toAlgHom)) (1 ⊗ₜ[R] v)
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul] at huniversal
    have hdown := congrArg
      (TensorProduct.map ULift.algEquiv.toLinearMap
        (LinearMap.id : W →ₗ[R] W)) huniversal
    calc
      TensorProduct.map f LinearMap.id
          (TensorProduct.comm R H V
            (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id
              ((Theta.action (CommAlgCat.of R (ULift.{max u v w} H))
                (toConv ULift.algEquiv.symm.toAlgHom)).val (1 ⊗ₜ[R] v)))) =
        TensorProduct.comm R H W
          (f.lTensor H
            (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id
              ((Theta.action (CommAlgCat.of R (ULift.{max u v w} H))
                (toConv ULift.algEquiv.symm.toAlgHom)).val (1 ⊗ₜ[R] v)))) := by
          exact LinearMap.rTensor_comm f _
      _ = TensorProduct.comm R H W
          (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id
            (f.baseChange (ULift.{max u v w} H)
              ((Theta.action (CommAlgCat.of R (ULift.{max u v w} H))
                (toConv ULift.algEquiv.symm.toAlgHom)).val (1 ⊗ₜ[R] v)))) := by
          congr 1
          simp only [LinearMap.baseChange_eq_ltensor, LinearMap.lTensor_def,
            TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp]
      _ = TensorProduct.comm R H W
          (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id
            ((Psi.action (CommAlgCat.of R (ULift.{max u v w} H))
              (toConv ULift.algEquiv.symm.toAlgHom)).val (1 ⊗ₜ[R] f v))) := by
          rw [hdown]

/-- A linear map between two right comodules is a comodule morphism if and only if all its scalar
extensions intertwine the point representations induced by those comodules. -/
theorem map_coact_iff_baseChange_comp_ofComodule_action
    (rho : Comodule R H V) (sigma : Comodule R H W) (f : V →ₗ[R] W) :
    TensorProduct.map f LinearMap.id ∘ₗ rho.coact = sigma.coact ∘ₗ f ↔
      ∀ (A : CommAlgCat.{max u v w} R) (x : points (H := H) A),
        f.baseChange A ∘ₗ ((ofComodule rho).action A x).val =
          ((ofComodule sigma).action A x).val ∘ₗ f.baseChange A := by
  have hrho : (toComodule (ofComodule rho)).coact = rho.coact :=
    congrArg (fun tau : Comodule R H V ↦ tau.coact) (toComodule_ofComodule rho)
  have hsigma : (toComodule (ofComodule sigma)).coact = sigma.coact :=
    congrArg (fun tau : Comodule R H W ↦ tau.coact) (toComodule_ofComodule sigma)
  rw [← hrho, ← hsigma]
  exact map_coact_iff_baseChange_comp_action (ofComodule rho) (ofComodule sigma) f

end TauCeti.HopfAlgebra.PointRepresentation
