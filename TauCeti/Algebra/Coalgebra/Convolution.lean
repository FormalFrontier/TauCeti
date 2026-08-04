/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import TauCeti.Algebra.Bialgebra.TensorProduct

/-!
# Comultiplication as a convolution product

Let `C` be an `R`-algebra carrying a comultiplication. This file records that, in the convolution
monoid of linear maps `C →ₗ[R] C ⊗[R] C`, comultiplication is the convolution product of the two
canonical inclusions `c ↦ c ⊗ₜ 1` and `c ↦ 1 ⊗ₜ c` of `C` into its tensor square.

## Main declarations

* `TauCeti.Coalgebra.comul_eq_convMul_includeLeft_includeRight`: comultiplication as the
  convolution product of the two tensor inclusions.
* `TauCeti.Bialgebra.comulPoint_eq_include_mul`: the corresponding identity for the
  algebra-hom points of a commutative bialgebra.
* `TauCeti.Bialgebra.toConv_comp_comulAlgHom`: the functorial form of the previous identity,
  after post-composing with an arbitrary algebra map out of the tensor square.
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

namespace Bialgebra

variable {R : Type*} [CommSemiring R]

section Semiring

variable {H : Type*} [Semiring H] [_root_.Bialgebra R H]

/-- **Post-composition splits the comultiplication point into its two inclusions.** For any
algebra map `φ` out of the tensor square, the point `φ ∘ Δ` is the convolution product of `φ`
restricted along the two inclusions.

The convolution monoid here is the one on points of `H` with values in the *commutative* algebra
`A`, so `H` itself need only be a semiring: the tensor square `H ⊗[R] H` is used solely as the
source of `φ`, never as a convolution target. That is why this is proved from the linear-map
identity `TauCeti.Coalgebra.comul_eq_convMul_includeLeft_includeRight` rather than from
`TauCeti.Bialgebra.comulPoint_eq_include_mul`, which needs `H ⊗[R] H` to be commutative. -/
theorem toConv_comp_comulAlgHom {A : Type*} [CommSemiring A] [Algebra R A]
    (phi : H ⊗[R] H →ₐ[R] A) :
    toConv (phi.comp (Bialgebra.comulAlgHom R H)) =
      toConv (phi.comp (Bialgebra.TensorProduct.includeLeft
        (R := R) (H₁ := H) (H₂ := H)).toAlgHom) *
      toConv (phi.comp (Bialgebra.TensorProduct.includeRight
        (R := R) (H₁ := H) (H₂ := H)).toAlgHom) := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul]
  have hcomul :
      (Bialgebra.comulAlgHom R H).toLinearMap =
        (toConv (Algebra.TensorProduct.includeLeft (R := R) (A := H) (B := H)).toLinearMap *
          toConv (Algebra.TensorProduct.includeRight
            (R := R) (A := H) (B := H)).toLinearMap).ofConv := by
    rw [← Coalgebra.comul_eq_convMul_includeLeft_includeRight (R := R) (C := H)]
    simp
  simp only [AlgHom.comp_toLinearMap, Bialgebra.TensorProduct.includeLeft_toAlgHom,
    Bialgebra.TensorProduct.includeRight_toAlgHom, hcomul]
  exact congrArg WithConv.toConv (LinearMap.algHom_comp_convMul_distrib phi _ _)

end Semiring

variable {H : Type*} [CommSemiring H] [_root_.Bialgebra R H]

/-- The comultiplication point of a commutative bialgebra is the convolution product of the
two canonical tensor-factor points. This is the algebra-hom form of
`Coalgebra.comul_eq_convMul_includeLeft_includeRight`. -/
theorem comulPoint_eq_include_mul :
    toConv (Bialgebra.comulAlgHom R H) =
      toConv (Bialgebra.TensorProduct.includeLeft
        (R := R) (H₁ := H) (H₂ := H)).toAlgHom *
      toConv (Bialgebra.TensorProduct.includeRight
        (R := R) (H₁ := H) (H₂ := H)).toAlgHom := by
  apply WithConv.ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.toLinearMap_convMul]
  simpa only [Bialgebra.toLinearMap_comulAlgHom,
    Bialgebra.TensorProduct.includeLeft_toAlgHom,
    Bialgebra.TensorProduct.includeRight_toAlgHom] using
      (Coalgebra.comul_eq_convMul_includeLeft_includeRight (R := R) (C := H))

end Bialgebra

end TauCeti
