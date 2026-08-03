/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct

/-!
# Tensor products of point representations

This file synchronizes tensor-product operations across the fixed-object correspondence between
point representations of an affine group and comodules over its commutative Hopf algebra.

Two point representations on `V` and `W` have a tensor representation on `V ⊗ W`: at a value
algebra `A`, its action is the tensor product of the two component automorphisms, transported
across the canonical equivalence

`A ⊗[R] (V ⊗[R] W) ≃ (A ⊗[R] V) ⊗[A] (A ⊗[R] W)`.

This construction agrees with the point representation induced by the diagonal tensor-product
comodule. No finiteness, freeness, projectivity, flatness, or nontriviality hypothesis is used.

## Main declarations

* `HopfAlgebra.PointRepresentation.tensor`: the diagonal action on the tensor product of two
  modules.
* `HopfAlgebra.PointRepresentation.ofComodule_tensor`: compatibility with the tensor-product
  comodule.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 9.44.
* J. S. Milne, *Reductive Groups*, §§5.1--5.4.
-/

public section

open CategoryTheory TensorProduct WithConv
open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable {R : Type u} {H : Type v} {V W : Type w} [CommRing R] [CommRing H]
variable [_root_.HopfAlgebra R H]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

namespace PointRepresentation

private noncomputable def tensorAutomorphism (_H : Type v)
    (A : CommAlgCat.{max u v w} R)
    (g : GeneralLinear.scalarExtensionAutomorphisms (V := V) A)
    (h : GeneralLinear.scalarExtensionAutomorphisms (V := W) A) :
    GeneralLinear.scalarExtensionAutomorphisms (V := V ⊗[R] W) A :=
  LinearMap.GeneralLinearGroup.congrLinearEquiv
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (TensorProduct.congr g.toLinearEquiv h.toLinearEquiv))

@[simp]
private theorem tensorAutomorphism_tmul (_H : Type v) (A : CommAlgCat.{max u v w} R)
    (g : GeneralLinear.scalarExtensionAutomorphisms (V := V) A)
    (h : GeneralLinear.scalarExtensionAutomorphisms (V := W) A)
    (a : A) (v : V) (w : W) :
    (tensorAutomorphism (R := R) _H A g h).val (a ⊗ₜ[R] (v ⊗ₜ[R] w)) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm
        (g.val (a ⊗ₜ[R] v) ⊗ₜ[A] h.val (1 ⊗ₜ[R] w)) := by
  -- This is the sole intentional unfolding of `tensorAutomorphism`; the named Mathlib lemmas
  -- expose its general-linear conjugation, tensor congruence, and base-change computation.
  simp only [tensorAutomorphism, LinearMap.GeneralLinearGroup.congrLinearEquiv_apply,
    LinearMap.GeneralLinearGroup.coe_ofLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_symm, TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
    TensorProduct.congr_tmul, LinearMap.GeneralLinearGroup.coe_toLinearEquiv]

private theorem tensorAutomorphism_one (_H : Type v) (A : CommAlgCat.{max u v w} R) :
    tensorAutomorphism (R := R) (V := V) (W := W) _H A 1 1 = 1 := by
  apply Units.ext
  refine TensorProduct.AlgebraTensorModule.ext fun a z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, map_zero]
  | add z t hz ht =>
      simpa only [tmul_add, map_add] using congrArg₂ (fun p q ↦ p + q) hz ht
  | tmul v w => simp

private theorem tensorAutomorphism_mul (_H : Type v) (A : CommAlgCat.{max u v w} R)
    (g g' : GeneralLinear.scalarExtensionAutomorphisms (V := V) A)
    (h h' : GeneralLinear.scalarExtensionAutomorphisms (V := W) A) :
    tensorAutomorphism (R := R) _H A (g * g') (h * h') =
      tensorAutomorphism (R := R) _H A g h * tensorAutomorphism (R := R) _H A g' h' := by
  simp only [tensorAutomorphism, LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
    TensorProduct.congr_mul, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul, map_mul]

private noncomputable def rawTensorAction
    (Theta : PointRepresentation (R := R) (H := H) (V := V))
    (Psi : PointRepresentation (R := R) (H := H) (V := W))
    (A : CommAlgCat.{max u v w} R) :
    points (H := H) A ⟶ GeneralLinear.scalarExtensionAutomorphisms (V := V ⊗[R] W) A :=
  GrpCat.ofHom
    { toFun := fun x ↦ tensorAutomorphism (R := R) H A (Theta.action A x) (Psi.action A x)
      map_one' := by
        rw [map_one, map_one]
        exact tensorAutomorphism_one (R := R) (V := V) (W := W) H A
      map_mul' := fun x y ↦ by
        rw [map_mul, map_mul]
        exact tensorAutomorphism_mul (R := R) H A _ _ _ _ }

@[simp]
private theorem rawTensorAction_tmul
    (Theta : PointRepresentation (R := R) (H := H) (V := V))
    (Psi : PointRepresentation (R := R) (H := H) (V := W))
    (A : CommAlgCat.{max u v w} R) (x : points (H := H) A)
    (a : A) (v : V) (w : W) :
    (rawTensorAction Theta Psi A x).val (a ⊗ₜ[R] (v ⊗ₜ[R] w)) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm
        ((Theta.action A x).val (a ⊗ₜ[R] v) ⊗ₜ[A]
          (Psi.action A x).val (1 ⊗ₜ[R] w)) := by
  exact tensorAutomorphism_tmul H A _ _ a v w

private theorem scalarExtensionMap_distribBaseChange_symm_tmul (_H : Type v)
    {A B : CommAlgCat.{max u v w} R} (phi : A ⟶ B)
    (p : A ⊗[R] V) (q : A ⊗[R] W) :
    GeneralLinear.scalarExtensionMap (V := V ⊗[R] W) phi
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm
          (p ⊗ₜ[A] q)) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R B V W).symm
        (GeneralLinear.scalarExtensionMap (V := V) phi p ⊗ₜ[B]
          GeneralLinear.scalarExtensionMap (V := W) phi q) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | add p p' hp hp' => simpa only [add_tmul, map_add] using congrArg₂ (fun a b ↦ a + b) hp hp'
  | tmul a v =>
      induction q using TensorProduct.induction_on with
      | zero => simp
      | add q q' hq hq' =>
          simpa only [tmul_add, map_add] using congrArg₂ (fun a b ↦ a + b) hq hq'
      | tmul b w => simp

private theorem rawTensorAction_naturality
    (Theta : PointRepresentation (R := R) (H := H) (V := V))
    (Psi : PointRepresentation (R := R) (H := H) (V := W))
    {A B : CommAlgCat.{max u v w} R} (phi : A ⟶ B) (x : points (H := H) A) :
    GeneralLinear.mapScalarExtensionAutomorphisms (V := V ⊗[R] W) phi
        (rawTensorAction Theta Psi A x) =
      rawTensorAction Theta Psi B (mapPoints (H := H) phi x) := by
  symm
  apply GeneralLinear.eq_mapScalarExtensionAutomorphisms_of_apply_scalarExtensionMap_eq
    (V := V ⊗[R] W) phi (rawTensorAction Theta Psi A x)
      (rawTensorAction Theta Psi B (mapPoints (H := H) phi x))
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z t hz ht => simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hz ht
  | tmul a z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z t hz ht =>
          simpa only [tmul_add, map_add] using congrArg₂ (fun a b ↦ a + b) hz ht
      | tmul v w =>
          rw [GeneralLinear.scalarExtensionMap_tmul, rawTensorAction_tmul,
            rawTensorAction_tmul,
            scalarExtensionMap_distribBaseChange_symm_tmul H]
          have hTheta := Theta.action_naturality phi x
          have hPsi := Psi.action_naturality phi x
          rw [← hTheta, ← hPsi]
          have hThetaApply :=
            GeneralLinear.mapScalarExtensionAutomorphisms_apply_scalarExtensionMap
              (V := V) phi (Theta.action A x) (a ⊗ₜ[R] v)
          have hPsiApply :=
            GeneralLinear.mapScalarExtensionAutomorphisms_apply_scalarExtensionMap
              (V := W) phi (Psi.action A x) (1 ⊗ₜ[R] w)
          simpa using congrArg₂ (fun p q ↦ p ⊗ₜ[B] q) hThetaApply hPsiApply

/-- The tensor product of two point representations. At each value algebra, the tensor product
of the component automorphisms is transported across scalar-extension distributivity. -/
noncomputable def tensor
    (Theta : PointRepresentation (R := R) (H := H) (V := V))
    (Psi : PointRepresentation (R := R) (H := H) (V := W)) :
    PointRepresentation (R := R) (H := H) (V := V ⊗[R] W) where
  app A := rawTensorAction Theta Psi A ≫
    eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V ⊗[R] W) A).symm
  naturality A B phi := by
    -- `pointsFunctor_obj` and the scalar-extension object theorem are categorical equalities,
    -- with no computation lemma that rewrites this structure-field goal before it is exposed.
    change
      mapPoints (H := H) phi ≫ rawTensorAction Theta Psi B ≫
          eqToHom
            (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V ⊗[R] W) B).symm =
        rawTensorAction Theta Psi A ≫
          eqToHom
            (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V ⊗[R] W) A).symm ≫
          (GeneralLinear.scalarExtensionAutomorphismsFunctor (V := V ⊗[R] W)).map phi
    have hraw :
        mapPoints (H := H) phi ≫ rawTensorAction Theta Psi B =
          rawTensorAction Theta Psi A ≫
            GeneralLinear.mapScalarExtensionAutomorphisms (V := V ⊗[R] W) phi := by
      apply GrpCat.ext
      intro x
      exact (rawTensorAction_naturality Theta Psi phi x).symm
    rw [GeneralLinear.scalarExtensionAutomorphismsFunctor_map]
    rw [← Category.assoc, hraw]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

@[simp]
private theorem action_tensor
    (Theta : PointRepresentation (R := R) (H := H) (V := V))
    (Psi : PointRepresentation (R := R) (H := H) (V := W))
    (A : CommAlgCat.{max u v w} R) :
    (tensor Theta Psi).action A = rawTensorAction Theta Psi A := by
  rw [action_def, tensor]
  -- The natural-transformation component is stored with the inverse of the opaque object
  -- equality; expose that categorical composite before cancelling the two transports.
  change
    (rawTensorAction Theta Psi A ≫
        eqToHom
          (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V ⊗[R] W) A).symm) ≫
      eqToHom (GeneralLinear.scalarExtensionAutomorphismsFunctor_obj (V := V ⊗[R] W) A) =
        rawTensorAction Theta Psi A
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The tensor point action, expressed by conjugating the tensor of the two component linear maps
through scalar-extension distributivity. -/
theorem tensor_action_apply
    (Theta : PointRepresentation (R := R) (H := H) (V := V))
    (Psi : PointRepresentation (R := R) (H := H) (V := W))
    (A : CommAlgCat.{max u v w} R) (x : points (H := H) A)
    (z : A ⊗[R] (V ⊗[R] W)) :
    ((tensor Theta Psi).action A x).val z =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm
        (TensorProduct.map (Theta.action A x).val (Psi.action A x).val
          (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W z)) := by
  rw [action_tensor]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z t hz ht => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) hz ht
  | tmul a z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z t hz ht =>
          simpa only [tmul_add, map_add] using congrArg₂ (fun p q ↦ p + q) hz ht
      | tmul v w =>
          rw [rawTensorAction_tmul,
            TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul]

/-- On a pure tensor, the tensor point action applies the two component actions diagonally and
transports the result back through scalar-extension distributivity. -/
@[simp]
theorem tensor_action_tmul
    (Theta : PointRepresentation (R := R) (H := H) (V := V))
    (Psi : PointRepresentation (R := R) (H := H) (V := W))
    (A : CommAlgCat.{max u v w} R) (x : points (H := H) A)
    (a : A) (v : V) (w : W) :
    ((tensor Theta Psi).action A x).val (a ⊗ₜ[R] (v ⊗ₜ[R] w)) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm
        ((Theta.action A x).val (a ⊗ₜ[R] v) ⊗ₜ[A]
          (Psi.action A x).val (1 ⊗ₜ[R] w)) := by
  rw [action_tensor]
  exact rawTensorAction_tmul Theta Psi A x a v w

private theorem comm_tensorCombine_eq_distribBaseChange_symm_tmul
    (_H : Type v) (A : CommAlgCat.{max u v w} R) (p : V ⊗[R] A) (q : W ⊗[R] A) :
    TensorProduct.comm R (V ⊗[R] W) A
        (Comodule.tensorCombine (R := R) (C := A) (M := V) (N := W) (p ⊗ₜ[R] q)) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm
        (TensorProduct.comm R V A p ⊗ₜ[A] TensorProduct.comm R W A q) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | add p p' hp hp' => simpa only [add_tmul, map_add] using congrArg₂ (fun a b ↦ a + b) hp hp'
  | tmul v a =>
      induction q using TensorProduct.induction_on with
      | zero => simp
      | add q q' hq hq' =>
          simpa only [tmul_add, map_add] using congrArg₂ (fun a b ↦ a + b) hq hq'
      | tmul w b => simp

private theorem evaluated_tensorCombine
    (A : CommAlgCat.{max u v w} R) (x : H →ₐ[R] A)
    (p : V ⊗[R] H) (q : W ⊗[R] H) :
    TensorProduct.comm R (V ⊗[R] W) A
        (TensorProduct.map LinearMap.id x.toLinearMap
          (Comodule.tensorCombine (R := R) (C := H) (M := V) (N := W) (p ⊗ₜ[R] q))) =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm
        (TensorProduct.comm R V A (TensorProduct.map LinearMap.id x.toLinearMap p) ⊗ₜ[A]
          TensorProduct.comm R W A (TensorProduct.map LinearMap.id x.toLinearMap q)) := by
  have h := LinearMap.congr_fun
    (Comodule.lTensor_comp_tensorCombine (R := R) (C := H) (D := A)
      (M := V) (N := W) x) (p ⊗ₜ[R] q)
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul] at h
  rw [LinearMap.lTensor_def] at h
  rw [h]
  exact comm_tensorCombine_eq_distribBaseChange_symm_tmul H A _ _

/-- The point representation induced by the tensor product of two comodules is the tensor product
of their induced point representations. -/
@[simp]
theorem ofComodule_tensor (rhoV : Comodule R H V) (rhoW : Comodule R H W) :
    letI : Comodule R H V := rhoV
    letI : Comodule R H W := rhoW
    ofComodule (Comodule.tensor R H V W) = tensor (ofComodule rhoV) (ofComodule rhoW) := by
  let _ : Comodule R H V := rhoV
  let _ : Comodule R H W := rhoW
  apply ext
  intro A x
  apply Units.ext
  refine TensorProduct.AlgebraTensorModule.ext fun a z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, map_zero]
  | add z t hz ht =>
      simpa only [tmul_add, map_add] using congrArg₂ (fun p q ↦ p + q) hz ht
  | tmul v w =>
      rw [ofComodule_action_tmul, tensor_action_tmul, Comodule.tensor_coact,
        Comodule.tensorCoact_tmul, ofComodule_action_tmul, ofComodule_action_tmul]
      rw [evaluated_tensorCombine A x.ofConv
        (Comodule.coact (R := R) (C := H) (M := V) v)
        (Comodule.coact (R := R) (C := H) (M := W) w)]
      simp only [one_smul]
      rw [← (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm.map_smul,
        TensorProduct.smul_tmul']

end PointRepresentation

end HopfAlgebra

end TauCeti
