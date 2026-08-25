/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Conjugation
public import Mathlib.LinearAlgebra.Contraction

/-!
# Contracting the tensor square of an inner product space against an orthonormal basis

An orthonormal basis `e` of an inner product space `V` identifies `V` with its dual, through
`Module.Basis.toDualEquiv` of the underlying basis: the dual vector of `v` is `u ↦ ∑ vᵢ uᵢ` in the
coordinates of `e`. That pairing is the **bilinear** form `⟪J v, u⟫`, for `J` the coordinatewise
conjugation of `TauCeti/Analysis/InnerProductSpace/Conjugation.lean`, because the
conjugate-linearity of `J` cancels the conjugate-linearity of the first argument of the inner
product (`TauCeti.toBasis_toDual_apply`).

Feeding that identification into Mathlib's contraction `dualTensorHomEquivOfBasis`, which turns
`Module.Dual 𝕜 V ⊗[𝕜] V` into the endomorphisms of `V`, contracts the tensor square:

`v ⊗ w ↦ (u ↦ ⟪J v, u⟫ • w)`.

The composite is a **linear equivalence** `V ⊗[𝕜] V ≃ₗ[𝕜] (V →ₗ[𝕜] V)` whose inverse spreads an
endomorphism over the basis, `A ↦ ∑ i, e i ⊗ₜ A (e i)`; only the finiteness of the index type is
needed, no completeness and no `FiniteDimensional` instance beyond it.

The equivalence depends on the basis, exactly as the conjugation describing it does, and that is
the point: `V` has no canonical bilinear form, so a choice has to enter. Its consumer is
`TauCeti/RepresentationTheory/Continuous/Square/Invariants.lean`, where an invariant tensor of a
unitary representation is turned into an intertwiner and Schur's lemma bounds how many there can
be.

## Main definitions

* `TauCeti.tensorSquareEquivEnd`: the contraction `V ⊗[𝕜] V ≃ₗ[𝕜] (V →ₗ[𝕜] V)`.

## Main statements

* `TauCeti.toBasis_toDual_apply`: the dual vector that an orthonormal basis attaches to `v` pairs
  against `u` as `⟪J v, u⟫`. This is the bridge between Mathlib's contraction and the conjugation.
* `TauCeti.tensorSquareEquivEnd_tmul_apply` and `TauCeti.tensorSquareEquivEnd_symm_apply`: the two
  directions on generators. Everything downstream goes through these rather than through the
  definition.
-/

public section

open scoped InnerProductSpace TensorProduct

namespace TauCeti

variable {𝕜 ι V : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] (e : OrthonormalBasis ι 𝕜 V)

/-- **The dual vector of an orthonormal basis is pairing against the conjugate.** In the
coordinates of `e` the dual vector `Module.Basis.toDual` attaches to `v` is `u ↦ ∑ vᵢ uᵢ`, which is
`⟪J v, u⟫`: the inner product is conjugate-linear in its first argument and `J` is
conjugate-linear, so the two conjugations cancel and the pairing is `𝕜`-bilinear. -/
@[simp]
theorem toBasis_toDual_apply (v u : V) : e.toBasis.toDual v u = ⟪conjugation e v, u⟫_𝕜 := by
  have hb : ∀ i : ι, e.toBasis.toDual v (e i) = ⟪conjugation e v, e i⟫_𝕜 := fun i ↦ by
    have h := Module.Basis.toDual_apply_left e.toBasis v i
    rw [OrthonormalBasis.coe_toBasis] at h
    rw [h, OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
      inner_conjugation_left_basis]
  conv_lhs => rw [← e.sum_repr' u]
  conv_rhs => rw [← e.sum_repr' u]
  rw [map_sum, inner_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [map_smul, smul_eq_mul, inner_smul_right, hb i]

/-- **The tensor square of an inner product space is its endomorphism space**, contracted along the
dual vectors of an orthonormal basis: `v ⊗ w` becomes `u ↦ ⟪J v, u⟫ • w`, and an endomorphism `A`
becomes `∑ i, e i ⊗ₜ A (e i)`. It is Mathlib's contraction `dualTensorHomEquivOfBasis` of
`Module.Dual 𝕜 V ⊗[𝕜] V`, precomposed with the identification of `V` with its dual. -/
noncomputable def tensorSquareEquivEnd : V ⊗[𝕜] V ≃ₗ[𝕜] (V →ₗ[𝕜] V) :=
  (TensorProduct.congr e.toBasis.toDualEquiv (LinearEquiv.refl 𝕜 V)).trans
    (dualTensorHomEquivOfBasis e.toBasis)

/-- **The contraction of a pure tensor.** `v ⊗ w` becomes the rank-one endomorphism that pairs its
argument against `v` through the bilinear form `⟪J v, -⟫` of the basis and scales `w` by the
result. -/
@[simp]
theorem tensorSquareEquivEnd_tmul_apply (v w u : V) :
    tensorSquareEquivEnd e (v ⊗ₜ[𝕜] w) u = ⟪conjugation e v, u⟫_𝕜 • w := by
  rw [tensorSquareEquivEnd, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, dualTensorHomEquivOfBasis_apply, dualTensorHom_apply,
    Module.Basis.toDualEquiv_apply, toBasis_toDual_apply]

/-- **The inverse of the contraction spreads an endomorphism over the basis**, as the sum
`∑ i, e i ⊗ₜ A (e i)` of the pure tensors recording where `A` sends each basis vector. -/
@[simp]
theorem tensorSquareEquivEnd_symm_apply (A : V →ₗ[𝕜] V) :
    (tensorSquareEquivEnd e).symm A = ∑ i, e i ⊗ₜ[𝕜] A (e i) := by
  rw [LinearEquiv.symm_apply_eq, map_sum]
  refine LinearMap.ext fun u ↦ ?_
  rw [LinearMap.sum_apply]
  calc A u = A (∑ i, ⟪e i, u⟫_𝕜 • e i) := by rw [e.sum_repr' u]
    _ = ∑ i, tensorSquareEquivEnd e (e i ⊗ₜ[𝕜] A (e i)) u := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by
          rw [tensorSquareEquivEnd_tmul_apply, conjugation_basis, map_smul]

end TauCeti
