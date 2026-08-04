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
* `HopfAlgebra.PointRepresentation.ofComodule_tensor` and
  `HopfAlgebra.PointRepresentation.toComodule_tensor`: compatibility with the tensor-product
  comodule in both directions.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 9.44.
* J. S. Milne, *Reductive Groups*, §§5.1--5.4.
-/

public section

open TensorProduct
open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable {R : Type u} {H : Type v} {V W : Type w} [CommRing R] [CommRing H]
variable [_root_.HopfAlgebra R H]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

namespace PointRepresentation

/-- The tensor product of two point representations. At each value algebra, the tensor product
of the component automorphisms is transported across scalar-extension distributivity. -/
noncomputable def tensor
    (Theta : PointRepresentation (R := R) (H := H) (V := V))
    (Psi : PointRepresentation (R := R) (H := H) (V := W)) :
    PointRepresentation (R := R) (H := H) (V := V ⊗[R] W) :=
  let _ : Comodule R H V := toComodule Theta
  let _ : Comodule R H W := toComodule Psi
  ofComodule (Comodule.tensor R H V W)

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
  let _ : Comodule R H V := toComodule Theta
  let _ : Comodule R H W := toComodule Psi
  rw [tensor, ofComodule_action_tmul, Comodule.tensor_coact, Comodule.tensorCoact_tmul]
  rw [evaluated_tensorCombine A x.ofConv
    (Comodule.coact (R := R) (C := H) (M := V) v)
    (Comodule.coact (R := R) (C := H) (M := W) w)]
  rw [← ofComodule_toComodule Theta, ← ofComodule_toComodule Psi,
    ofComodule_action_tmul, ofComodule_action_tmul]
  simp only [one_smul]
  rw [← (TensorProduct.AlgebraTensorModule.distribBaseChange R A V W).symm.map_smul,
    TensorProduct.smul_tmul']

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
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z t hz ht => simpa only [map_add] using congrArg₂ (fun p q ↦ p + q) hz ht
  | tmul a z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z t hz ht =>
          simpa only [tmul_add, map_add] using congrArg₂ (fun p q ↦ p + q) hz ht
      | tmul v w =>
          rw [tensor_action_tmul,
            TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.map_tmul]

/-- The point representation induced by the tensor product of two comodules is the tensor product
of their induced point representations. -/
@[simp]
theorem ofComodule_tensor (rhoV : Comodule R H V) (rhoW : Comodule R H W) :
    letI : Comodule R H V := rhoV
    letI : Comodule R H W := rhoW
    ofComodule (Comodule.tensor R H V W) = tensor (ofComodule rhoV) (ofComodule rhoW) := by
  unfold tensor
  rw [toComodule_ofComodule, toComodule_ofComodule]

/-- Recovering the comodule of a tensor-product point representation gives the tensor product
of the recovered comodules. -/
@[simp]
theorem toComodule_tensor
    (Theta : PointRepresentation (R := R) (H := H) (V := V))
    (Psi : PointRepresentation (R := R) (H := H) (V := W)) :
    letI : Comodule R H V := toComodule Theta
    letI : Comodule R H W := toComodule Psi
    toComodule (tensor Theta Psi) = Comodule.tensor R H V W := by
  simp only [tensor, toComodule_ofComodule]

end PointRepresentation

end HopfAlgebra

end TauCeti
