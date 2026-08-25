/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.LinearAlgebra.Basis.SMul

/-!
# A positive-definite form is the standard one in suitable coordinates

Let `S` be a symmetric operator on a finite-dimensional inner product space `V` whose associated
Hermitian form `⟪S v, w⟫` is positive definite. This file produces a linear automorphism of `V`
along which that form pulls back to the inner product `V` already carries:

`TauCeti.exists_continuousLinearEquiv_inner_map_map` gives `e : V ≃L[𝕜] V` with
`⟪S (e x), e y⟫ = ⟪x, y⟫` for all `x` and `y`.

Equivalently `e` is an isometry from `(V, ⟪·,·⟫)` onto `(V, ⟪S ·, ·⟫)`, so its inverse is the
operator usually written `S ^ (1 / 2)`; the construction here avoids building an operator square
root by scaling an orthonormal eigenbasis of `S` instead. The eigenvalues of `S` are positive
because the form is definite, so dividing the `i`-th eigenvector by `√(λ i)` produces a basis that
is orthonormal *for the form*, and `e` is the map carrying the eigenbasis to it.

## Main statements

* `TauCeti.exists_continuousLinearEquiv_inner_map_map`: a positive-definite symmetric operator's
  form becomes the standard inner product after a change of coordinates.

Only the existence of `e` is exported, since it depends on a choice of eigenbasis. The operator is
taken continuous and the change of coordinates produced is a continuous linear equivalence; on a
finite-dimensional space that is no restriction either way, and it is the form the consumer both
supplies and wants.

The intended consumer is Weyl's unitarian trick: applied to the Gram operator of the Haar-averaged
inner product of a representation of a compact group, this is what turns the invariant form into
an honest unitary structure, in
`TauCeti/RepresentationTheory/Compact/UnitaryModel.lean`.
-/

public section

open RCLike
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [FiniteDimensional 𝕜 V]

/-- **A positive-definite form is standard in suitable coordinates.** If `S` is a symmetric
operator on a finite-dimensional inner product space whose form `⟪S ·, ·⟫` is positive definite,
then there is a continuous linear automorphism `e` with `⟪S (e x), e y⟫ = ⟪x, y⟫`.

The automorphism is the inverse of the square root of `S`, built without any operator functional
calculus: an orthonormal eigenbasis `b` of `S` has positive eigenvalues `λ i`, so the vectors
`(√(λ i))⁻¹ • b i` are orthonormal for the form `⟪S ·, ·⟫`, and `e` is the automorphism carrying
`b i` to them. -/
theorem exists_continuousLinearEquiv_inner_map_map (S : V →L[𝕜] V)
    (hsymm : (S : V →ₗ[𝕜] V).IsSymmetric) (hpos : ∀ v : V, v ≠ 0 → 0 < re ⟪S v, v⟫_𝕜) :
    ∃ e : V ≃L[𝕜] V, ∀ x y : V, ⟪S (e x), e y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  classical
  set n := Module.finrank 𝕜 V with hn
  set b := hsymm.eigenvectorBasis hn.symm
  set lam := hsymm.eigenvalues hn.symm
  have hSb : ∀ i, S (b i) = (lam i : 𝕜) • b i := fun i ↦
    hsymm.apply_eigenvectorBasis hn.symm i
  have hbb : ∀ i j, ⟪b i, b j⟫_𝕜 = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp b.orthonormal
  -- The eigenvalues are positive: `⟪S (b i), b i⟫ = λ i` and the form is definite.
  have hlam : ∀ i, 0 < lam i := fun i ↦ by
    have h := hpos (b i) (b.orthonormal.ne_zero i)
    rw [hSb i, inner_smul_left, hbb i i] at h
    simpa using h
  -- Scaling the `i`-th eigenvector by `(√(λ i))⁻¹` makes the family orthonormal for the form.
  set w : Fin n → 𝕜 := fun i ↦ ((Real.sqrt (lam i))⁻¹ : ℝ) with hwdef
  have hw : ∀ i, IsUnit (w i) := fun i ↦ by
    refine isUnit_iff_ne_zero.mpr ?_
    simp [hwdef, Real.sqrt_eq_zero', (hlam i).not_ge]
  set el : V ≃ₗ[𝕜] V := b.toBasis.equiv (b.toBasis.isUnitSMul hw) (Equiv.refl (Fin n)) with heldef
  set e : V ≃L[𝕜] V := el.toContinuousLinearEquiv with hedef
  have he' : ∀ i, e (b.toBasis i) = w i • b.toBasis i := fun i ↦ by
    simp only [hedef, heldef, LinearEquiv.coe_toContinuousLinearEquiv',
      Module.Basis.equiv_apply, Equiv.refl_apply, Module.Basis.isUnitSMul_apply]
  have he : ∀ i, e (b i) = w i • b i := by simpa only [b.coe_toBasis] using he'
  have hkey : ∀ i j, ⟪S (e (b i)), e (b j)⟫_𝕜 = if i = j then 1 else 0 := fun i j ↦ by
    rw [he i, he j, map_smul, hSb i, smul_smul, inner_smul_left, inner_smul_right, hbb i j]
    rcases eq_or_ne i j with rfl | hij
    · have hr : ((Real.sqrt (lam i))⁻¹ * lam i * (Real.sqrt (lam i))⁻¹ : ℝ) = 1 := by
        have hne : Real.sqrt (lam i) ≠ 0 := (Real.sqrt_pos.mpr (hlam i)).ne'
        field_simp
        exact (Real.sq_sqrt (hlam i).le).symm
      rw [ite_eq_left rfl, mul_one, hwdef, ← RCLike.ofReal_mul, conj_ofReal, ← RCLike.ofReal_mul,
        hr, RCLike.ofReal_one]
    · simp [hij]
  -- Both sides are sesquilinear, so the basis computation determines them.
  refine ⟨e, fun x y ↦ ?_⟩
  rw [← b.sum_inner_mul_inner x y]
  conv_lhs => rw [← b.sum_repr' x, ← b.sum_repr' y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hkey]
  simp [inner_conj_symm, mul_comm]

end TauCeti
