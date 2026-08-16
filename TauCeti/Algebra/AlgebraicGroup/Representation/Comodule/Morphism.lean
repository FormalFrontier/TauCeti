/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Basic

/-!
# Morphisms of point representations and comodules

This file characterizes the morphisms of comodules and natural point representations of the
affine group represented by a commutative Hopf algebra. A linear map is colinear exactly when
every scalar extension intertwines the actions of every algebra-valued point. Explicit comodules
may have carriers in independent universes; arbitrary point representations share the universe
of their value-algebra category.

The converse uses the universal point of the Hopf algebra: evaluating equivariance there recovers
the colinearity square. Consequently the pointwise condition ranges over all commutative value
algebras, including nonreduced ones.

## Main declarations

* `TauCeti.HopfAlgebra.PointRepresentation.map_coact_of_baseChange_comp_endOfPoint_universal`:
  intertwining at the universal point alone already forces colinearity.
* `TauCeti.HopfAlgebra.PointRepresentation.map_coact_iff_baseChange_comp_endOfPoint`: the
  fixed-morphism criterion for explicit comodules with carriers in independent universes.
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

universe u v w x

variable {R : Type u} {H : Type v} {V : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid V] [Module R V]

private theorem coact_apply_eq_universal_endOfPoint
    (_W : Type x) (rho : Comodule R H V) (z : V) :
    rho.coact z =
      TensorProduct.comm R H V
        (TensorProduct.map
          (ULift.algEquiv (R := R) : ULift.{max u v w x} H ≃ₐ[R] H).toLinearMap
          LinearMap.id
          (Comodule.endOfPoint V
            (ULift.algEquiv (R := R) :
              ULift.{max u v w x} H ≃ₐ[R] H).symm.toAlgHom
            (1 ⊗ₜ[R] z))) := by
  have hend :
      Comodule.endOfPoint V
          (ULift.algEquiv (R := R) :
            ULift.{max u v w x} H ≃ₐ[R] H).symm.toAlgHom
          (1 ⊗ₜ[R] z) =
        TensorProduct.comm R V (ULift.{max u v w x} H)
          (LinearMap.lTensor V
            (ULift.algEquiv (R := R) :
              ULift.{max u v w x} H ≃ₐ[R] H).symm.toAlgHom.toLinearMap
            (rho.coact z)) := by
    rw [Comodule.endOfPoint_tmul]
    exact one_smul _ _
  rw [hend]
  induction rho.coact z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simpa only [map_add] using congrArg₂ (fun c d ↦ c + d) ha hb
  | tmul a b =>
      simp only [LinearMap.lTensor_tmul, AlgEquiv.toLinearMap_apply,
        TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.comm_tmul,
        AlgHom.toLinearMap_apply, AlgEquiv.toAlgHom_apply,
        AlgEquiv.apply_symm_apply]

section IndependentCarrierUniverses

variable {W : Type x} [AddCommMonoid W] [Module R W]

/-- **Intertwining at the universal point suffices for colinearity.** A linear map between two
right comodules is colinear as soon as its scalar extension to `ULift H` intertwines the point
actions of the universal point; no condition at other value algebras is needed. -/
theorem map_coact_of_baseChange_comp_endOfPoint_universal
    (rho : Comodule R H V) (sigma : Comodule R H W) (f : V →ₗ[R] W)
    (huniv : f.baseChange (CommAlgCat.of R (ULift.{max u v w x} H)) ∘ₗ
          Comodule.endOfPoint V
            (toConv ULift.algEquiv.symm.toAlgHom :
              points (H := H) (CommAlgCat.of R (ULift.{max u v w x} H))).ofConv =
        Comodule.endOfPoint W
            (toConv ULift.algEquiv.symm.toAlgHom :
              points (H := H) (CommAlgCat.of R (ULift.{max u v w x} H))).ofConv ∘ₗ
          f.baseChange (CommAlgCat.of R (ULift.{max u v w x} H))) :
    TensorProduct.map f LinearMap.id ∘ₗ rho.coact = sigma.coact ∘ₗ f := by
  apply LinearMap.ext
  intro z
  simp only [LinearMap.comp_apply]
  rw [coact_apply_eq_universal_endOfPoint W rho z,
    coact_apply_eq_universal_endOfPoint V sigma (f z)]
  have huniversal := LinearMap.congr_fun huniv (1 ⊗ₜ[R] z)
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul] at huniversal
  have hdown := congrArg
    (TensorProduct.map ULift.algEquiv.toLinearMap
      (LinearMap.id : W →ₗ[R] W)) huniversal
  calc
    TensorProduct.map f LinearMap.id
        (TensorProduct.comm R H V
          (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id
            (Comodule.endOfPoint V ULift.algEquiv.symm.toAlgHom (1 ⊗ₜ[R] z)))) =
      TensorProduct.comm R H W
        (f.lTensor H
          (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id
            (Comodule.endOfPoint V ULift.algEquiv.symm.toAlgHom (1 ⊗ₜ[R] z)))) := by
        exact LinearMap.rTensor_comm f _
    _ = TensorProduct.comm R H W
        (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id
          (f.baseChange (ULift.{max u v w x} H)
            (Comodule.endOfPoint V ULift.algEquiv.symm.toAlgHom (1 ⊗ₜ[R] z)))) := by
        congr 1
        simp only [LinearMap.baseChange_eq_ltensor, LinearMap.lTensor_def,
          TensorProduct.map_map, LinearMap.comp_id, LinearMap.id_comp]
    _ = TensorProduct.comm R H W
        (TensorProduct.map ULift.algEquiv.toLinearMap LinearMap.id
          (Comodule.endOfPoint W ULift.algEquiv.symm.toAlgHom (1 ⊗ₜ[R] f z))) := by
        rw [hdown]

/-- A linear map between two right comodules is colinear if and only if all its scalar extensions
intertwine their point actions.

The two carriers may lie in independent universes. The value algebras lie in one common universe
large enough for the base ring, Hopf algebra, and both carriers. No finiteness or flatness
assumption is required. -/
theorem map_coact_iff_baseChange_comp_endOfPoint
    (rho : Comodule R H V) (sigma : Comodule R H W) (f : V →ₗ[R] W) :
    TensorProduct.map f LinearMap.id ∘ₗ rho.coact = sigma.coact ∘ₗ f ↔
      ∀ (A : CommAlgCat.{max u v w x} R) (p : points (H := H) A),
        f.baseChange A ∘ₗ Comodule.endOfPoint V p.ofConv =
          Comodule.endOfPoint W p.ofConv ∘ₗ f.baseChange A := by
  constructor
  · intro hcolinear
    let fHom : Comodule.Hom R H V W :=
      { toLinearMap := f
        map_coact := hcolinear }
    intro A p
    simpa only [fHom] using Comodule.baseChange_comp_endOfPoint fHom p.ofConv
  · intro hintertwines
    exact map_coact_of_baseChange_comp_endOfPoint_universal rho sigma f
      (hintertwines _ _)

end IndependentCarrierUniverses

variable {W : Type w} [AddCommMonoid W] [Module R W]

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
  rw [map_coact_iff_baseChange_comp_endOfPoint
    (toComodule Theta) (toComodule Psi) f]
  apply forall_congr'
  intro A
  apply forall_congr'
  intro x
  let : Comodule R H V := toComodule Theta
  let : Comodule R H W := toComodule Psi
  have hTheta :
      (Theta.action A x).val = Comodule.endOfPoint V x.ofConv := by
    simpa only [ofComodule_toComodule] using
      (ofComodule_action_val_eq_endOfPoint (toComodule Theta) A x)
  have hPsi :
      (Psi.action A x).val = Comodule.endOfPoint W x.ofConv := by
    simpa only [ofComodule_toComodule] using
      (ofComodule_action_val_eq_endOfPoint (toComodule Psi) A x)
  rw [hTheta, hPsi]

/-- A linear map between two right comodules is a comodule morphism if and only if all its scalar
extensions intertwine the point representations induced by those comodules. -/
theorem map_coact_iff_baseChange_comp_ofComodule_action
    (rho : Comodule R H V) (sigma : Comodule R H W) (f : V →ₗ[R] W) :
    TensorProduct.map f LinearMap.id ∘ₗ rho.coact = sigma.coact ∘ₗ f ↔
      ∀ (A : CommAlgCat.{max u v w} R) (x : points (H := H) A),
        f.baseChange A ∘ₗ ((ofComodule rho).action A x).val =
          ((ofComodule sigma).action A x).val ∘ₗ f.baseChange A := by
  rw [map_coact_iff_baseChange_comp_endOfPoint rho sigma f]
  apply forall_congr'
  intro A
  apply forall_congr'
  intro x
  rw [ofComodule_action_val_eq_endOfPoint rho A x,
    ofComodule_action_val_eq_endOfPoint sigma A x]

end TauCeti.HopfAlgebra.PointRepresentation
