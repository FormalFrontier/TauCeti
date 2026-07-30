/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.HopfAlgebra.Basic

/-!
# The antipode reverses comultiplication

The antipode of a Hopf algebra is an antihomomorphism for both its algebra and coalgebra
structures. Mathlib already proves the multiplicative statement directly. This file records
the coalgebraic statement: applying the antipode before comultiplication is the same as
comultiplying, swapping the two tensor factors, and applying the antipode to each factor.

## Main declarations

* `TauCeti.HopfAlgebra.antipode_comul_antidistrib`: the identity as an equality of linear maps.
* `TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply`: the pointwise form.

## Implementation notes

The proof takes place in the convolution monoid of linear maps from the Hopf algebra to its
tensor square. Comultiplication factors as the convolution product of the two canonical tensor
inclusions. The antipode identities, postcomposed with those inclusions, exhibit the proposed
opposite comultiplication as a right inverse to comultiplication. Comultiplication postcomposed
with the other antipode identity supplies a left inverse, so uniqueness of inverses finishes
the proof.

## References

This is the standard anti-coalgebra identity for a Hopf antipode; see Sweedler,
*Hopf Algebras*, Chapter 4.
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

private lemma algHom_comp_antipode_mul_self {D : Type w} [Semiring D] [Algebra R D]
    (f : C →ₐ[R] D) :
    (toConv (f.toLinearMap ∘ₗ antipode R) : WithConv (C →ₗ[R] D)) *
        toConv f.toLinearMap = 1 := by
  refine WithConv.ofConv_injective ?_
  have h := LinearMap.algHom_comp_convMul_distrib f
    (toConv (antipode R)) (toConv (LinearMap.id : C →ₗ[R] C))
  rw [antipode_convMul_id] at h
  change
    WithConv.ofConv
        ((toConv (f.toLinearMap ∘ₗ antipode R) : WithConv (C →ₗ[R] D)) *
          toConv f.toLinearMap) =
      WithConv.ofConv (1 : WithConv (C →ₗ[R] D))
  calc
    _ = f.toLinearMap.comp
        (1 : WithConv (C →ₗ[R] C)).ofConv := h.symm
    _ = (1 : WithConv (C →ₗ[R] D)).ofConv := by
      ext c
      simp [LinearMap.convOne_apply]

private lemma algHom_self_mul_comp_antipode {D : Type w} [Semiring D] [Algebra R D]
    (f : C →ₐ[R] D) :
    (toConv f.toLinearMap : WithConv (C →ₗ[R] D)) *
        toConv (f.toLinearMap ∘ₗ antipode R) = 1 := by
  refine WithConv.ofConv_injective ?_
  have h := LinearMap.algHom_comp_convMul_distrib f
    (toConv (LinearMap.id : C →ₗ[R] C)) (toConv (antipode R))
  rw [id_convMul_antipode] at h
  change
    WithConv.ofConv
        ((toConv f.toLinearMap : WithConv (C →ₗ[R] D)) *
          toConv (f.toLinearMap ∘ₗ antipode R)) =
      WithConv.ofConv (1 : WithConv (C →ₗ[R] D))
  calc
    _ = f.toLinearMap.comp
        (1 : WithConv (C →ₗ[R] C)).ofConv := h.symm
    _ = (1 : WithConv (C →ₗ[R] D)).ofConv := by
      ext c
      simp [LinearMap.convOne_apply]

/-- The antipode reverses comultiplication: after comultiplication, swap the tensor factors
and apply the antipode to each of them. -/
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
  let ΔS : WithConv (C →ₗ[R] C ⊗[R] C) :=
    toConv (Coalgebra.comul ∘ₗ antipode R)
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
  -- The ordinary and proposed comultiplications are opposite-sided inverses.
  have hleft : ΔS * Δ = 1 := by
    simpa only [ΔS, Δ, Bialgebra.toLinearMap_comulAlgHom] using
      (algHom_comp_antipode_mul_self
        (R := R) (C := C) (D := C ⊗[R] C)
        (Bialgebra.comulAlgHom R C))
  have hP : P * PS = 1 := by
    simpa only [P, PS, ιr] using
      (algHom_self_mul_comp_antipode
        (R := R) (C := C) (D := C ⊗[R] C)
        (Algebra.TensorProduct.includeRight : C →ₐ[R] C ⊗[R] C))
  have hL : L * LS = 1 := by
    simpa only [L, LS, ιl] using
      (algHom_self_mul_comp_antipode
        (R := R) (C := C) (D := C ⊗[R] C)
        (Algebra.TensorProduct.includeLeft : C →ₐ[R] C ⊗[R] C))
  have hright : Δ * SΔop = 1 := by
    rw [hΔ, hSΔop]
    calc
      (L * P) * (PS * LS) = L * ((P * PS) * LS) := by
        simp only [mul_assoc]
      _ = L * LS := by rw [hP, one_mul]
      _ = 1 := hL
  -- A left inverse and a right inverse of the same element coincide.
  exact WithConv.toConv_injective (left_inv_eq_right_inv hleft hright)

/-- Pointwise form of `antipode_comul_antidistrib`. -/
theorem antipode_comul_antidistrib_apply (c : C) :
    Coalgebra.comul (antipode R c) =
      TensorProduct.map (antipode R) (antipode R)
        ((TensorProduct.comm R C C) (Coalgebra.comul c)) :=
  LinearMap.congr_fun antipode_comul_antidistrib c

end

end HopfAlgebra

end TauCeti
