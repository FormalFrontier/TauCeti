/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# Comultiplication as a convolution product

Let `C` be an `R`-algebra carrying a comultiplication. This file records that, in the convolution
monoid of linear maps `C →ₗ[R] C ⊗[R] C`, comultiplication is the convolution product of the two
canonical inclusions `c ↦ c ⊗ₜ 1` and `c ↦ 1 ⊗ₜ c` of `C` into its tensor square.

## Main declarations

* `TauCeti.Coalgebra.comul_eq_convMul_includeLeft_includeRight`: comultiplication as the
  convolution product of the two tensor inclusions.
-/

public section

open TensorProduct WithConv

namespace TauCeti

namespace Coalgebra

variable {R : Type*} {C : Type*} [CommSemiring R] [Semiring C] [Algebra R C]
  [_root_.CoalgebraStruct R C]

/-- **Comultiplication is the convolution product of the two tensor inclusions.** In the
convolution monoid of maps `C →ₗ[R] C ⊗[R] C`, the product of `includeLeft` and `includeRight`
multiplies the two legs of `Δ c` back together in order, which is `Δ` itself.

Only the comultiplication *data* is used, so this needs `CoalgebraStruct` rather than
`Coalgebra`: no coalgebra law, bialgebra compatibility or antipode axiom enters. -/
theorem comul_eq_convMul_includeLeft_includeRight :
    (toConv (Coalgebra.comul : C →ₗ[R] C ⊗[R] C) : WithConv (C →ₗ[R] C ⊗[R] C)) =
      toConv (Algebra.TensorProduct.includeLeft (R := R) (A := C) (B := C)).toLinearMap *
        toConv (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := C)).toLinearMap := by
  apply WithConv.ofConv_injective
  have hmul : LinearMap.mul' R (C ⊗[R] C) ∘ₗ
      TensorProduct.map
        (Algebra.TensorProduct.includeLeft (R := R) (A := C) (B := C)).toLinearMap
        (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := C)).toLinearMap =
      LinearMap.id := by
    -- Mathlib's `lmul'_comp_map` requires a commutative target algebra, whereas `C ⊗[R] C`
    -- is only a semiring here. `lift_includeLeft_includeRight` computes the same pure tensors,
    -- but identifying this linear composite still requires tensor-product extensionality.
    apply TensorProduct.ext
    ext x y
    simp
  simp only [LinearMap.convMul_def]
  rw [← LinearMap.comp_assoc, hmul]
  simp

end Coalgebra


section ExteriorProduct

open WithConv TensorProduct

variable {R M S : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [Semiring S] [Algebra R S]

namespace LinearMap



/-- The exterior convolution product on `M ⊗[R] M`: apply one factor on each tensor
leg and multiply the results in the coefficients. It underlies the Leibniz-rule
manipulations for counit-valued derivations: composing with the multiplication of the
bialgebra lands in this product's image. -/
def mulTensor (s t : WithConv (M →ₗ[R] S)) :
    WithConv (M ⊗[R] M →ₗ[R] S) :=
  toConv (LinearMap.mul' R S ∘ₗ map s.ofConv t.ofConv)

/-- The exterior product evaluates a pure tensor legwise and multiplies the results
in the coefficients. -/
@[simp]
lemma mulTensor_apply_tmul
    (s t : WithConv (M →ₗ[R] S)) (x y : M) :
    (mulTensor s t).ofConv (x ⊗ₜ[R] y) = s.ofConv x * t.ofConv y := by
  simp [mulTensor]


/-- The exterior product vanishes when the left factor is zero. -/
@[simp]
lemma mulTensor_zero_left (t : WithConv (M →ₗ[R] S)) :
    mulTensor 0 t = 0 := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp

/-- The exterior product vanishes when the right factor is zero. -/
@[simp]
lemma mulTensor_zero_right (s : WithConv (M →ₗ[R] S)) :
    mulTensor s 0 = 0 := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp

/-- The exterior product is additive in the left factor. -/
@[simp]
lemma mulTensor_add_left (s₁ s₂ t : WithConv (M →ₗ[R] S)) :
    mulTensor (s₁ + s₂) t = mulTensor s₁ t + mulTensor s₂ t := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp [add_mul]

/-- The exterior product is additive in the right factor. -/
@[simp]
lemma mulTensor_add_right (s t₁ t₂ : WithConv (M →ₗ[R] S)) :
    mulTensor s (t₁ + t₂) = mulTensor s t₁ + mulTensor s t₂ := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp [mul_add]

/-- Scalars pull out of the left factor of the exterior product. -/
@[simp]
lemma mulTensor_smul_left (r : R) (s t : WithConv (M →ₗ[R] S)) :
    mulTensor (r • s) t = r • mulTensor s t := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp

/-- Scalars pull out of the right factor of the exterior product. -/
@[simp]
lemma mulTensor_smul_right (r : R) (s t : WithConv (M →ₗ[R] S)) :
    mulTensor s (r • t) = r • mulTensor s t := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp

end LinearMap

namespace AlgHom

variable {A : Type*} [Semiring A] [Algebra R A]

open TauCeti.LinearMap in
/-- An algebra-map point composed with multiplication is its own exterior square:
the multiplicativity of the point, in convolution form. -/
lemma toConv_toLinearMap_comp_mul' (g : A →ₐ[R] S) :
    toConv (g.toLinearMap ∘ₗ LinearMap.mul' R A) =
      mulTensor (toConv g.toLinearMap) (toConv g.toLinearMap) := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp [map_mul]

end AlgHom

end ExteriorProduct

section ExteriorConvolution

open WithConv TensorProduct

variable {R A S : Type*} [CommSemiring R] [Semiring A] [Bialgebra R A]
  [CommSemiring S] [Algebra R S]

namespace LinearMap

/-- The exterior product is multiplicative for convolution: products interleave
legwise. -/
lemma mulTensor_convMul
    (s t u v : WithConv (A →ₗ[R] S)) :
    mulTensor s t * mulTensor u v = mulTensor (s * u) (t * v) := by
  have h := LinearMap.algHom_comp_convMul_distrib
    (Algebra.TensorProduct.lmul' R (S := S))
    (toConv (map s.ofConv t.ofConv)) (toConv (map u.ofConv v.ofConv))
  rw [map_convMul_map] at h
  -- The commutative multiplication algebra map and the plain multiplication linear map
  -- agree; restate `h` in the linear form used by `mulTensor`.
  rw [Algebra.TensorProduct.lmul'_toLinearMap] at h
  calc mulTensor s t * mulTensor u v
      = toConv (LinearMap.mul' R S ∘ₗ map (s * u).ofConv (t * v).ofConv) := by
        rw [mulTensor, mulTensor, ← toConv_ofConv (toConv _ * toConv _), ← h]
    _ = mulTensor (s * u) (t * v) := rfl

end LinearMap

end ExteriorConvolution

end TauCeti
