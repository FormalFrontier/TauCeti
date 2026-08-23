/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Conjugation
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Contracting the tensor square of an inner product space against an orthonormal basis

An orthonormal basis `e` of an inner product space `V` carries a genuinely **bilinear** form,
`B(v, w) = ⟪J v, w⟫` for `J` the coordinatewise conjugation of
`TauCeti/Analysis/InnerProductSpace/Conjugation.lean`: the inner product is conjugate-linear in its
first argument and `J` is conjugate-linear, so the two conjugations cancel. In coordinates `B` is
the standard symmetric form `∑ vᵢ wᵢ`, and it is what lets the tensor square of `V` be contracted
into the endomorphisms of `V`,

`v ⊗ w ↦ (u ↦ B(v, u) • w)`.

That contraction is a **linear equivalence** `V ⊗[𝕜] V ≃ₗ[𝕜] (V →ₗ[𝕜] V)`, with inverse
`A ↦ ∑ i, e i ⊗ₜ A (e i)`; only the finiteness of the index type is needed, no completeness and no
`FiniteDimensional` instance beyond it. Both composites collapse because `∑ i, ⟪e i, x⟫ • e i = x`
and `⟪J v, e i⟫ = ⟪e i, v⟫` (`TauCeti.inner_conjugation_left_basis`).

The equivalence depends on the basis, exactly as the conjugation it is built from does, and that is
the point: `V` has no canonical bilinear form, so a choice has to enter. Its consumer is
`TauCeti/RepresentationTheory/Continuous/Square/Invariants.lean`, where an invariant tensor of a
unitary representation is turned into an intertwiner and Schur's lemma bounds how many there can
be.

## Main definitions

* `TauCeti.conjBilin`: the bilinear form `B(v, w) = ⟪J v, w⟫` of an orthonormal basis.
* `TauCeti.tensorSquareEquivEnd`: the contraction `V ⊗[𝕜] V ≃ₗ[𝕜] (V →ₗ[𝕜] V)`.

## Main statements

* `TauCeti.tensorSquareEquivEnd_tmul_apply` and `TauCeti.tensorSquareEquivEnd_symm_apply`: the two
  directions on generators. Everything downstream goes through these rather than through the
  definitions.
* `TauCeti.conjBilin_symm`: the form is symmetric, which is why the same contraction reads the
  tensor square from either side.
-/

public section

open scoped InnerProductSpace TensorProduct

namespace TauCeti

variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (e : OrthonormalBasis ι 𝕜 V)

/-- **The bilinear form of an orthonormal basis**, `B(v, w) = ⟪J v, w⟫`. It is `𝕜`-bilinear, and
not merely sesquilinear, because the conjugate-linearity of the conjugation cancels the
conjugate-linearity of the first argument of the inner product. -/
noncomputable def conjBilin : V →ₗ[𝕜] V →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂ 𝕜 (fun v w ↦ ⟪conjugation e v, w⟫_𝕜)
    (fun v₁ v₂ w ↦ by rw [conjugation_add, inner_add_left])
    (fun c v w ↦ by rw [conjugation_smul, inner_smul_left, RingHomCompTriple.comp_apply,
      RingHom.id_apply, smul_eq_mul])
    (fun v w₁ w₂ ↦ inner_add_right _ _ _)
    (fun c v w ↦ by rw [inner_smul_right, smul_eq_mul])

@[simp]
theorem conjBilin_apply (v w : V) : conjBilin e v w = ⟪conjugation e v, w⟫_𝕜 := (rfl)

/-- The form is symmetric: in the coordinates of `e` it is `∑ i, vᵢ wᵢ`. -/
theorem conjBilin_symm (v w : V) : conjBilin e v w = conjBilin e w v := by
  rw [conjBilin_apply, conjBilin_apply]
  conv_rhs => rw [← conjugation_conjugation e v]
  rw [inner_conjugation_conjugation, inner_conj_symm]

/-- Contracting the first factor of a pure tensor away, `v ⊗ w ↦ (u ↦ B(v, u) • w)`. This is the
forward direction of `TauCeti.tensorSquareEquivEnd`. -/
noncomputable def tensorToEnd : V ⊗[𝕜] V →ₗ[𝕜] (V →ₗ[𝕜] V) :=
  TensorProduct.lift <| LinearMap.mk₂ 𝕜 (fun v w ↦ (conjBilin e v).smulRight w)
    (fun v₁ v₂ w ↦ LinearMap.ext fun u ↦ by
      simp only [LinearMap.smulRight_apply, LinearMap.add_apply, map_add, add_smul])
    (fun c v w ↦ LinearMap.ext fun u ↦ by
      simp only [LinearMap.smulRight_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, mul_smul])
    (fun v w₁ w₂ ↦ LinearMap.ext fun u ↦ by
      simp only [LinearMap.smulRight_apply, LinearMap.add_apply, smul_add])
    (fun c v w ↦ LinearMap.ext fun u ↦ by
      simp only [LinearMap.smulRight_apply, LinearMap.smul_apply]
      exact smul_comm _ _ _)

@[simp]
theorem tensorToEnd_tmul_apply (v w u : V) :
    tensorToEnd e (v ⊗ₜ[𝕜] w) u = ⟪conjugation e v, u⟫_𝕜 • w := (rfl)

/-- Spreading an endomorphism over the basis, `A ↦ ∑ i, e i ⊗ₜ A (e i)`. This is the inverse
direction of `TauCeti.tensorSquareEquivEnd`. -/
noncomputable def endToTensor : (V →ₗ[𝕜] V) →ₗ[𝕜] V ⊗[𝕜] V where
  toFun A := ∑ i, e i ⊗ₜ[𝕜] A (e i)
  map_add' A B := by
    simp only [LinearMap.add_apply, TensorProduct.tmul_add]
    exact Finset.sum_add_distrib
  map_smul' c A := by
    simp only [LinearMap.smul_apply, TensorProduct.tmul_smul, RingHom.id_apply]
    exact (Finset.smul_sum).symm

@[simp]
theorem endToTensor_apply (A : V →ₗ[𝕜] V) : endToTensor e A = ∑ i, e i ⊗ₜ[𝕜] A (e i) := (rfl)

/-- Spreading an endomorphism over the basis and contracting again returns it: the contraction
reads `A` off its values on the basis. -/
theorem tensorToEnd_endToTensor (A : V →ₗ[𝕜] V) : tensorToEnd e (endToTensor e A) = A := by
  refine LinearMap.ext fun u ↦ ?_
  rw [endToTensor_apply, map_sum, LinearMap.sum_apply]
  calc ∑ i, tensorToEnd e (e i ⊗ₜ[𝕜] A (e i)) u
      = A (∑ i, ⟪e i, u⟫_𝕜 • e i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by
          rw [tensorToEnd_tmul_apply, conjugation_basis, map_smul]
    _ = A u := by rw [e.sum_repr' u]

/-- Contracting a tensor and spreading the result over the basis returns it: on a pure tensor the
first factor is reassembled from its coordinates. -/
theorem endToTensor_tensorToEnd (t : V ⊗[𝕜] V) : endToTensor e (tensorToEnd e t) = t := by
  induction t with
  | zero => rw [map_zero, map_zero]
  | tmul v w =>
      rw [endToTensor_apply]
      calc ∑ i, e i ⊗ₜ[𝕜] tensorToEnd e (v ⊗ₜ[𝕜] w) (e i)
          = (∑ i, ⟪e i, v⟫_𝕜 • e i) ⊗ₜ[𝕜] w := by
            rw [TensorProduct.sum_tmul]
            exact Finset.sum_congr rfl fun i _ ↦ by
              rw [tensorToEnd_tmul_apply, inner_conjugation_left_basis]
              exact (TensorProduct.smul_tmul _ _ _).symm
        _ = v ⊗ₜ[𝕜] w := by rw [e.sum_repr' v]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **The tensor square of an inner product space is its endomorphism space**, contracted along the
bilinear form of an orthonormal basis: `v ⊗ w` becomes `u ↦ B(v, u) • w`, and an endomorphism `A`
becomes `∑ i, e i ⊗ₜ A (e i)`. -/
noncomputable def tensorSquareEquivEnd : V ⊗[𝕜] V ≃ₗ[𝕜] (V →ₗ[𝕜] V) :=
  LinearEquiv.ofLinearMap (tensorToEnd e) (endToTensor e)
    (LinearMap.ext fun A ↦ tensorToEnd_endToTensor e A)
    (LinearMap.ext fun t ↦ endToTensor_tensorToEnd e t)

@[simp]
theorem tensorSquareEquivEnd_tmul_apply (v w u : V) :
    tensorSquareEquivEnd e (v ⊗ₜ[𝕜] w) u = ⟪conjugation e v, u⟫_𝕜 • w := (rfl)

@[simp]
theorem tensorSquareEquivEnd_symm_apply (A : V →ₗ[𝕜] V) :
    (tensorSquareEquivEnd e).symm A = ∑ i, e i ⊗ₜ[𝕜] A (e i) := (rfl)

/-- The contraction, applied to a tensor and then to a vector, as a linear map in the tensor. This
is the shape in which an invariant tensor is turned into an intertwiner. -/
theorem tensorSquareEquivEnd_apply_apply (t : V ⊗[𝕜] V) (u : V) :
    tensorSquareEquivEnd e t u = tensorToEnd e t u := (rfl)

end TauCeti
