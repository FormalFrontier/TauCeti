/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import TauCeti.RingTheory.GradedAlgebra.TensorProduct

import Mathlib.Tactic.LinearCombination

/-!
# Tensor products of differential graded algebras

The tensor product of two differential graded algebras `(A, d_A)` and `(B, d_B)` is Mathlib's
Koszul-signed graded tensor product `𝒜 ᵍ⊗[R] ℬ`, graded by total degree, with the differential

`d (a ᵍ⊗ₜ b) = d_A a ᵍ⊗ₜ b + (-1) ^ |a| • (a ᵍ⊗ₜ d_B b)`.

The sign is the one forced by the Koszul rule `(f ⊗ g) (x ⊗ y) = (-1) ^ (|g| |x|) f x ⊗ g y` for
tensor products of homogeneous maps: the differential is `d_A ⊗ 1` plus `1 ⊗ d_B`, and since `d_B`
has degree one the second summand carries the twist `a ↦ (-1) ^ |a| a` on the left factor.

## Main definitions

* `TauCeti.dgTensorDifferential`: the differential of the tensor product.
* `TauCeti.dgTensorIncludeLeft` and `TauCeti.dgTensorIncludeRight`: the inclusions of the two
  factors, as morphisms of differential graded algebras.

## Main results

* `TauCeti.isDGAlgebra_gradedTensorGrading`: the graded tensor product of two differential graded
  algebras is a differential graded algebra for the total-degree grading.
* `TauCeti.dgTensorDifferential_tmul_of_mem`: the sign rule on pure tensors with a homogeneous
  left factor.

Only the left factor of a pure tensor has to be homogeneous for the sign rule, and only the left
factor of a product has to be homogeneous for the Leibniz rule, exactly as in the one-factor
Leibniz axiom `TauCeti.IsDGAlgebra.leibniz`.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
* N. Bourbaki, *Algebra I*, Chapter III, §4.7, example (2).
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]

variable (𝒜 : ℤ → Submodule R A) (ℬ : ℤ → Submodule R B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

/-- The differential of the tensor product of two differential graded algebras: the sum of
`d_A ⊗ 1` and of `d_B` preceded, on the left factor, by the Koszul twist `a ↦ (-1) ^ |a| a`. -/
noncomputable def dgTensorDifferential (dA : A →ₗ[R] A) (dB : B →ₗ[R] B) :
    (𝒜 ᵍ⊗[R] ℬ) →ₗ[R] (𝒜 ᵍ⊗[R] ℬ) :=
  (GradedTensorProduct.of R 𝒜 ℬ).toLinearMap ∘ₗ
    (TensorProduct.map dA LinearMap.id +
      TensorProduct.map ((InternalGrading.ofDecomposition 𝒜).koszulTwist 1) dB) ∘ₗ
    (GradedTensorProduct.of R 𝒜 ℬ).symm.toLinearMap

variable {𝒜 ℬ} {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}

/-- The differential of a tensor product, evaluated on a pure tensor. -/
theorem dgTensorDifferential_tmul (a : A) (b : B) :
    dgTensorDifferential 𝒜 ℬ dA dB (a ᵍ⊗ₜ[R] b) =
      dA a ᵍ⊗ₜ[R] b + (InternalGrading.ofDecomposition 𝒜).koszulTwist 1 a ᵍ⊗ₜ[R] dB b := by
  simp [dgTensorDifferential, GradedTensorProduct.tmul]

/-- The sign rule for the differential of a tensor product on a pure tensor with homogeneous left
factor: `d (a ᵍ⊗ₜ b) = d_A a ᵍ⊗ₜ b + (-1) ^ |a| • (a ᵍ⊗ₜ d_B b)`. -/
theorem dgTensorDifferential_tmul_of_mem {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) (b : B) :
    dgTensorDifferential 𝒜 ℬ dA dB (a ᵍ⊗ₜ[R] b) =
      dA a ᵍ⊗ₜ[R] b + p.negOnePow • (a ᵍ⊗ₜ[R] dB b : 𝒜 ᵍ⊗[R] ℬ) := by
  rw [dgTensorDifferential_tmul,
    (InternalGrading.ofDecomposition 𝒜).koszulTwist_apply_of_mem
      (by simpa only [InternalGrading.ofDecomposition_piece] using ha) 1]
  congr 1
  rw [gradedTensor_smul_tmul, Units.smul_def, ← Int.cast_smul_eq_zsmul R, one_mul]

/-- A sign `(-1) ^ k`, acting through the units of `ℤ`, acts as the image of `(-1) ^ k` in the
ground ring. -/
private theorem negOnePow_smul_eq (k : ℤ) {M : Type*} [AddCommGroup M] [Module R M] (x : M) :
    k.negOnePow • x = (((k.negOnePow : ℤ) : R)) • x := by
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul R]

/-- The sign rule for the differential of a tensor product, with the sign written as a scalar of
the ground ring. -/
private theorem dgTensorDifferential_tmul_of_mem' {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) (b : B) :
    dgTensorDifferential 𝒜 ℬ dA dB (a ᵍ⊗ₜ[R] b) =
      dA a ᵍ⊗ₜ[R] b + (((p.negOnePow : ℤ) : R)) • (a ᵍ⊗ₜ[R] dB b : 𝒜 ᵍ⊗[R] ℬ) := by
  rw [dgTensorDifferential_tmul_of_mem ha, negOnePow_smul_eq (R := R)]

/-- The Leibniz rule of the tensor product, on two pure tensors of homogeneous elements. -/
private theorem dgTensorDifferential_leibniz_tmul (hA : IsDGAlgebra 𝒜 dA) (hB : IsDGAlgebra ℬ dB)
    {p q p' : ℤ} {a a' : A} {b : B}
    (ha : a ∈ 𝒜 p) (hb : b ∈ ℬ q) (ha' : a' ∈ 𝒜 p') (b' : B) :
    dgTensorDifferential 𝒜 ℬ dA dB ((a ᵍ⊗ₜ[R] b) * (a' ᵍ⊗ₜ[R] b') : 𝒜 ᵍ⊗[R] ℬ) =
      dgTensorDifferential 𝒜 ℬ dA dB (a ᵍ⊗ₜ[R] b) * (a' ᵍ⊗ₜ[R] b') +
        (((p + q).negOnePow : ℤ) : R) •
          ((a ᵍ⊗ₜ[R] b) * dgTensorDifferential 𝒜 ℬ dA dB (a' ᵍ⊗ₜ[R] b')) := by
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜 ℬ a ⟨b, hb⟩ ⟨a', ha'⟩ b',
    ← Int.negOnePow_def, negOnePow_smul_eq (R := R), map_smul,
    dgTensorDifferential_tmul_of_mem' (SetLike.mul_mem_graded ha ha'),
    hA.leibniz ha a', hB.leibniz hb b']
  rw [dgTensorDifferential_tmul_of_mem' ha, dgTensorDifferential_tmul_of_mem' ha']
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜 ℬ (dA a) ⟨b, hb⟩ ⟨a', ha'⟩ b',
    GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜 ℬ a ⟨dB b, hB.map_mem hb⟩ ⟨a', ha'⟩ b',
    GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜 ℬ a ⟨b, hb⟩ ⟨dA a', hA.map_mem ha'⟩ b',
    GradedTensorProduct.tmul_coe_mul_coe_tmul 𝒜 ℬ a ⟨b, hb⟩ ⟨a', ha'⟩ (dB b')]
  simp only [← Int.negOnePow_def, negOnePow_smul_eq (R := R), gradedTensor_add_tmul,
    gradedTensor_tmul_add, gradedTensor_smul_tmul, gradedTensor_tmul_smul, smul_add, smul_smul]
  have hq : ((q.negOnePow : ℤ) : R) * ((q.negOnePow : ℤ) : R) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, ← Int.negOnePow_add, Int.negOnePow_even _ ⟨q, rfl⟩]
    norm_num
  simp only [show (q + 1) * p' = q * p' + p' by ring, show q * (p' + 1) = q * p' + q by ring,
    Int.negOnePow_add, Units.val_mul, Int.cast_mul]
  match_scalars
  · ring
  · linear_combination (-(((q * p').negOnePow : ℤ) : R) * ((p.negOnePow : ℤ) : R)) * hq
  · ring
  · ring

/-- The Leibniz rule of the tensor product, for a homogeneous pure tensor on the left and an
arbitrary element on the right. -/
private theorem dgTensorDifferential_leibniz_tmul_left (hA : IsDGAlgebra 𝒜 dA)
    (hB : IsDGAlgebra ℬ dB) {p q : ℤ} {a : A} {b : B} (ha : a ∈ 𝒜 p) (hb : b ∈ ℬ q)
    (y : 𝒜 ᵍ⊗[R] ℬ) :
    dgTensorDifferential 𝒜 ℬ dA dB ((a ᵍ⊗ₜ[R] b) * y) =
      dgTensorDifferential 𝒜 ℬ dA dB (a ᵍ⊗ₜ[R] b) * y +
        (((p + q).negOnePow : ℤ) : R) •
          ((a ᵍ⊗ₜ[R] b) * dgTensorDifferential 𝒜 ℬ dA dB y) := by
  have key : (dgTensorDifferential 𝒜 ℬ dA dB ∘ₗ
        GradedTensorProduct.mulHom 𝒜 ℬ (a ᵍ⊗ₜ[R] b) : (𝒜 ᵍ⊗[R] ℬ) →ₗ[R] (𝒜 ᵍ⊗[R] ℬ)) =
      GradedTensorProduct.mulHom 𝒜 ℬ (dgTensorDifferential 𝒜 ℬ dA dB (a ᵍ⊗ₜ[R] b)) +
        (((p + q).negOnePow : ℤ) : R) •
          (GradedTensorProduct.mulHom 𝒜 ℬ (a ᵍ⊗ₜ[R] b) ∘ₗ
            dgTensorDifferential 𝒜 ℬ dA dB) := by
    refine linearMap_ext_of_tmul 𝒜 ℬ fun p' q' a' ha' b' _ ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      ← GradedTensorProduct.mul_def]
    exact dgTensorDifferential_leibniz_tmul hA hB ha hb ha' b'
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    ← GradedTensorProduct.mul_def] using LinearMap.congr_fun key y

/-- The tensor product of two differential graded algebras is a differential graded algebra: the
total-degree grading of `𝒜 ᵍ⊗[R] ℬ` and the differential
`d (a ᵍ⊗ₜ b) = d_A a ᵍ⊗ₜ b + (-1) ^ |a| • (a ᵍ⊗ₜ d_B b)` satisfy the degree, square-zero, and
graded Leibniz axioms. -/
theorem isDGAlgebra_gradedTensorGrading (hA : IsDGAlgebra 𝒜 dA) (hB : IsDGAlgebra ℬ dB) :
    IsDGAlgebra (gradedTensorGrading 𝒜 ℬ) (dgTensorDifferential 𝒜 ℬ dA dB) where
  map_mem {n x} hx := by
    refine gradedTensorGrading_le 𝒜 ℬ (C := Submodule.comap (dgTensorDifferential 𝒜 ℬ dA dB)
      (gradedTensorGrading 𝒜 ℬ (n + 1))) (fun p a ha b hb ↦ ?_) hx
    rw [Submodule.mem_comap, dgTensorDifferential_tmul_of_mem' ha]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
    · rw [show n + 1 = p + 1 + (n - p) by ring]
      exact tmul_mem_gradedTensorGrading 𝒜 ℬ (hA.map_mem ha) hb
    · rw [show n + 1 = p + (n - p + 1) by ring]
      exact tmul_mem_gradedTensorGrading 𝒜 ℬ ha (hB.map_mem hb)
  sq_zero x := by
    have key : (dgTensorDifferential 𝒜 ℬ dA dB ∘ₗ dgTensorDifferential 𝒜 ℬ dA dB :
        (𝒜 ᵍ⊗[R] ℬ) →ₗ[R] (𝒜 ᵍ⊗[R] ℬ)) = 0 := by
      refine linearMap_ext_of_tmul 𝒜 ℬ fun p q a ha b hb ↦ ?_
      rw [LinearMap.comp_apply, dgTensorDifferential_tmul_of_mem' ha, map_add, map_smul,
        dgTensorDifferential_tmul_of_mem' (hA.map_mem ha),
        dgTensorDifferential_tmul_of_mem' ha, hA.sq_zero, hB.sq_zero, Int.negOnePow_succ]
      simp only [gradedTensor_zero_tmul, gradedTensor_tmul_zero, Units.val_neg, Int.cast_neg,
        LinearMap.zero_apply, smul_zero, neg_smul]
      module
    exact LinearMap.congr_fun key x
  leibniz {m x} hx y := by
    have key : x ∈ LinearMap.ker
        (dgTensorDifferential 𝒜 ℬ dA dB ∘ₗ (GradedTensorProduct.mulHom 𝒜 ℬ).flip y -
          (((GradedTensorProduct.mulHom 𝒜 ℬ).flip y ∘ₗ dgTensorDifferential 𝒜 ℬ dA dB) +
            (((m.negOnePow : ℤ) : R)) • ((GradedTensorProduct.mulHom 𝒜 ℬ).flip
              (dgTensorDifferential 𝒜 ℬ dA dB y)))) := by
      refine gradedTensorGrading_le 𝒜 ℬ (fun p a ha b hb ↦ ?_) hx
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.add_apply, LinearMap.smul_apply, LinearMap.flip_apply,
        ← GradedTensorProduct.mul_def, sub_eq_zero]
      rw [show m = p + (m - p) by ring]
      exact dgTensorDifferential_leibniz_tmul_left hA hB ha hb y
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.flip_apply,
      ← GradedTensorProduct.mul_def, sub_eq_zero] at key
    rw [key, negOnePow_smul_eq (R := R)]

/-- The inclusion `a ↦ a ᵍ⊗ₜ 1` of the left factor, as a morphism of differential graded
algebras. -/
noncomputable def dgTensorIncludeLeft (hA : IsDGAlgebra 𝒜 dA) (hB : IsDGAlgebra ℬ dB) :
    DGAlgHom hA (isDGAlgebra_gradedTensorGrading hA hB) where
  toGradedAlgHom := gradedTensorIncludeLeft 𝒜 ℬ
  map_d' a := by
    simp only [gradedTensorIncludeLeft_apply]
    rw [dgTensorDifferential_tmul, hB.map_one_eq_zero, gradedTensor_tmul_zero, add_zero]

@[simp]
theorem dgTensorIncludeLeft_apply (hA : IsDGAlgebra 𝒜 dA) (hB : IsDGAlgebra ℬ dB) (a : A) :
    dgTensorIncludeLeft hA hB a = a ᵍ⊗ₜ[R] (1 : B) := by
  change gradedTensorIncludeLeft 𝒜 ℬ a = _
  exact gradedTensorIncludeLeft_apply 𝒜 ℬ a

/-- The inclusion `b ↦ 1 ᵍ⊗ₜ b` of the right factor, as a morphism of differential graded
algebras. -/
noncomputable def dgTensorIncludeRight (hA : IsDGAlgebra 𝒜 dA) (hB : IsDGAlgebra ℬ dB) :
    DGAlgHom hB (isDGAlgebra_gradedTensorGrading hA hB) where
  toGradedAlgHom := gradedTensorIncludeRight 𝒜 ℬ
  map_d' b := by
    simp only [gradedTensorIncludeRight_apply]
    rw [dgTensorDifferential_tmul_of_mem (SetLike.one_mem_graded 𝒜), hA.map_one_eq_zero,
      gradedTensor_zero_tmul, zero_add, Int.negOnePow_zero, one_smul]

@[simp]
theorem dgTensorIncludeRight_apply (hA : IsDGAlgebra 𝒜 dA) (hB : IsDGAlgebra ℬ dB) (b : B) :
    dgTensorIncludeRight hA hB b = (1 : A) ᵍ⊗ₜ[R] b := by
  change gradedTensorIncludeRight 𝒜 ℬ b = _
  exact gradedTensorIncludeRight_apply 𝒜 ℬ b

end TauCeti
