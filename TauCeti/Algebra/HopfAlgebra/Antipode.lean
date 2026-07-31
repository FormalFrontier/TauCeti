/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# The antipode reverses comultiplication

The antipode of a Hopf algebra is an antihomomorphism for both its algebra and coalgebra
structures. Mathlib already proves the multiplicative statement directly, as
`HopfAlgebra.antipode_mul_antidistrib`. This file records the coalgebraic statement: applying
the antipode before comultiplication is the same as comultiplying, swapping the two tensor
factors, and applying the antipode to each factor.

## Main declarations

* `TauCeti.HopfAlgebra.antipode_comul_antidistrib`: the identity as an equality of linear maps.
* `TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply`: the pointwise form.

## Implementation notes

The proof takes place in the convolution monoid of linear maps from the Hopf algebra to its
tensor square. Comultiplication factors as the convolution product of the two canonical tensor
inclusions, and postcomposing Mathlib's antipode convolution identity
`LinearMap.antipode_mul_id` with those inclusions exhibits the proposed opposite
comultiplication as a left inverse of comultiplication. Mathlib's `LinearMap.comul_right_inv`
supplies the matching right inverse, so uniqueness of inverses finishes the proof.

## References

This is the standard anti-coalgebra identity for a Hopf antipode; see Sweedler,
*Hopf Algebras*, Chapter 4. Mathlib formalizes it for a Hopf object in a braided monoidal
category as `CategoryTheory.HopfObj.antipode_comul`, by the same left-inverse-equals-right-inverse
argument in the convolution monoid; the proof below is the ring-level analogue of that argument,
stated for `HopfAlgebra R C` so that it applies directly to `Coalgebra.comul`.
-/

public section

open HopfAlgebra TensorProduct WithConv
open scoped RingTheory.LinearMap

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable {R : Type u} {C : Type v}
variable [CommSemiring R] [Semiring C] [_root_.HopfAlgebra R C]

noncomputable section

/-- Postcomposing the antipode convolution identity `LinearMap.antipode_mul_id` with an algebra
homomorphism `f`: the map `f ∘ₗ antipode` is a left convolution inverse of `f`. -/
private lemma algHom_comp_antipode_mul_self {D : Type w} [Semiring D] [Algebra R D]
    (f : C →ₐ[R] D) :
    (toConv (f.toLinearMap ∘ₗ antipode R) : WithConv (C →ₗ[R] D)) *
        toConv f.toLinearMap = 1 := by
  refine WithConv.ofConv_injective ?_
  calc ((toConv (f.toLinearMap ∘ₗ antipode R) : WithConv (C →ₗ[R] D)) *
        toConv f.toLinearMap).ofConv
      = f.toLinearMap ∘ₗ
          (toConv (antipode R) * toConv LinearMap.id : WithConv (C →ₗ[R] C)).ofConv := by
        rw [LinearMap.algHom_comp_convMul_distrib]
        simp
    -- `LinearMap.algHom_comp_convOne` is the last step, but it lives in
    -- `Mathlib.RingTheory.HopfAlgebra.Quotient`, whose Hopf-ideal theory is unrelated here.
    _ = (1 : WithConv (C →ₗ[R] D)).ofConv := by
        rw [LinearMap.antipode_mul_id]
        ext c
        simp

/-- The antipode reverses comultiplication: after comultiplication, swap the tensor factors
and apply the antipode to each of them. This is the coalgebraic counterpart of
`HopfAlgebra.antipode_mul_antidistrib`. -/
theorem antipode_comul_antidistrib :
    Coalgebra.comul ∘ₗ antipode R =
      TensorProduct.map (antipode R) (antipode R) ∘ₗ
        (TensorProduct.comm R C C).toLinearMap ∘ₗ Coalgebra.comul := by
  let ιl : C →ₗ[R] C ⊗[R] C :=
    Algebra.TensorProduct.includeLeft.toLinearMap
  let ιr : C →ₗ[R] C ⊗[R] C :=
    Algebra.TensorProduct.includeRight.toLinearMap
  let Δ : WithConv (C →ₗ[R] C ⊗[R] C) :=
    toConv Coalgebra.comul
  let SΔop : WithConv (C →ₗ[R] C ⊗[R] C) :=
    toConv
      (TensorProduct.map (antipode R) (antipode R) ∘ₗ
        (TensorProduct.comm R C C).toLinearMap ∘ₗ Coalgebra.comul)
  let L : WithConv (C →ₗ[R] C ⊗[R] C) := toConv ιl
  let P : WithConv (C →ₗ[R] C ⊗[R] C) := toConv ιr
  let LS : WithConv (C →ₗ[R] C ⊗[R] C) :=
    toConv (ιl ∘ₗ antipode R)
  let PS : WithConv (C →ₗ[R] C ⊗[R] C) :=
    toConv (ιr ∘ₗ antipode R)
  -- Comultiplication is the convolution product of the two tensor inclusions.
  have hmul_ιl_ιr :
      LinearMap.mul' R (C ⊗[R] C) ∘ₗ TensorProduct.map ιl ιr =
        LinearMap.id := by
    apply TensorProduct.ext
    ext x y
    simp [ιl, ιr]
  have hΔ : Δ = L * P := by
    apply WithConv.ofConv_injective
    simp only [Δ, L, P, LinearMap.convMul_def]
    rw [← LinearMap.comp_assoc, hmul_ιl_ιr]
    simp
  -- Reversing the inclusions gives the proposed opposite comultiplication.
  have hmul_ιrS_ιlS :
      LinearMap.mul' R (C ⊗[R] C) ∘ₗ
          TensorProduct.map (ιr ∘ₗ antipode R) (ιl ∘ₗ antipode R) =
        TensorProduct.map (antipode R) (antipode R) ∘ₗ
          (TensorProduct.comm R C C).toLinearMap := by
    apply TensorProduct.ext
    ext x y
    simp [ιl, ιr]
  have hSΔop : SΔop = PS * LS := by
    apply WithConv.ofConv_injective
    simp only [SΔop, PS, LS, LinearMap.convMul_def]
    have h := congrArg (fun f => f ∘ₗ (Coalgebra.comul (R := R) (A := C)))
      hmul_ιrS_ιlS
    simpa only [LinearMap.comp_assoc] using h.symm
  -- Each inclusion, precomposed with the antipode, is a left convolution inverse of itself.
  have hLS : LS * L = 1 := by
    simpa only [LS, L, ιl] using
      (algHom_comp_antipode_mul_self
        (R := R) (C := C) (D := C ⊗[R] C)
        (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C))
  have hPS : PS * P = 1 := by
    simpa only [PS, P, ιr] using
      (algHom_comp_antipode_mul_self
        (R := R) (C := C) (D := C ⊗[R] C)
        (Algebra.TensorProduct.includeRight : C →ₐ[R] C ⊗[R] C))
  -- So the proposed opposite comultiplication is a left inverse of comultiplication, while
  -- `LinearMap.comul_right_inv` makes `comul ∘ₗ antipode` a right inverse of it.
  have hleft : SΔop * Δ = 1 := by
    rw [hΔ, hSΔop]
    calc
      (PS * LS) * (L * P) = PS * ((LS * L) * P) := by
        simp only [mul_assoc]
      _ = PS * P := by rw [hLS, one_mul]
      _ = 1 := hPS
  -- A left inverse and a right inverse of the same element coincide.
  exact (WithConv.toConv_injective
    (left_inv_eq_right_inv hleft LinearMap.comul_right_inv)).symm

/-- Pointwise form of `antipode_comul_antidistrib`. -/
@[simp]
theorem antipode_comul_antidistrib_apply (c : C) :
    Coalgebra.comul (antipode R c) =
      TensorProduct.map (antipode R) (antipode R)
        ((TensorProduct.comm R C C) (Coalgebra.comul c)) :=
  LinearMap.congr_fun antipode_comul_antidistrib c

end

end HopfAlgebra

end TauCeti
