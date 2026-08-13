/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive-definite kernels

A *positive-definite kernel* on a type `α` is a function `K : α → α → 𝕜`, valued in an `RCLike`
field `𝕜` (so `ℝ` or `ℂ`), such that every finite Gram matrix `(K (v i) (v j))ᵢⱼ` is positive
semidefinite. Equivalently, `K` is conjugate-symmetric and, for every finite family `v` of
points and every coefficient vector `x`, the Hermitian form
`∑ᵢⱼ conj(xᵢ) · xⱼ · K (vᵢ) (vⱼ)` is nonnegative.

This is the two-variable companion of a positive-definite function: the roadmap's
`K(a, b) = F(a + b⋆)` construction turns a positive-definite function on an involutive monoid
into a positive-definite kernel, and conversely the kernel form is the object underlying the
GNS / Kolmogorov decomposition. Stating it via Mathlib's `Matrix.PosSemidef` lets the positive
semidefinite matrix calculus do the work: closure under (Schur / entrywise) products is exactly
the Schur product theorem `Matrix.PosSemidef.hadamard`, and the rank-one kernels
`(a, b) ↦ conj(g a) · g b` come from `Matrix.posSemidef_vecMulVec_star_self`.

This advances the `OneParameterSemigroups` roadmap, Part C ("Positive-definite functions and
Bochner's theorem") in `TauCetiRoadmap/OneParameterSemigroups/README.md`: the `API to develop`
bullet "the PD-function ↔ PD-kernel equivalence (`K(a, b) = F(a + b⋆)` ...), pullbacks, and the
GNS/Kolmogorov decomposition". A kernel is represented directly as a matrix, so the API uses
Mathlib's `Matrix.PosSemidef` rather than introducing a second predicate.

## Main statements

* `TauCeti.posSemidef_apply_self_nonneg`: diagonal entries of a positive-definite
  kernel are nonnegative.
* `TauCeti.posSemidef_conj_symm`: positive-definite kernels are
  conjugate-symmetric.
* `TauCeti.posSemidef_zero`, `TauCeti.posSemidef_one`, and
  `TauCeti.posSemidef_const_of_nonneg`: constant positive-definite kernels.
* `TauCeti.posSemidef_smul`: closure under nonnegative real scalar multiples.
* `TauCeti.posSemidef_iff`: the quadratic-form characterization, whose reverse
  direction builds a positive-definite kernel from conjugate symmetry and form nonnegativity.
* `TauCeti.posSemidef_conj_mul`: the rank-one kernels
  `(a, b) ↦ conj(g a) · g b`.
-/

public section

open Matrix
open scoped ComplexConjugate ComplexOrder

namespace TauCeti

universe u v z

variable {𝕜 : Type u} [RCLike 𝕜]
variable {α : Type v}

/-- Diagonal values of a positive-definite kernel are nonnegative. -/
theorem posSemidef_apply_self_nonneg {K : α → α → 𝕜}
    (hK : Matrix.PosSemidef K) (a : α) : 0 ≤ K a a := by
  simpa [Finsupp.sum_single_index] using hK.2 (Finsupp.single a 1)

/-- Positive-definite kernels are conjugate-symmetric. -/
theorem posSemidef_conj_symm {K : α → α → 𝕜}
    (hK : Matrix.PosSemidef K) (a b : α) : conj (K a b) = K b a := by
  have h := hK.isHermitian.apply b a
  rw [starRingEnd_apply]
  exact h

private theorem real_smul_kernel_eq (r : ℝ) (K : α → α → 𝕜) :
    (fun a b => r • K a b) = (r : 𝕜) • K := by
  ext a b
  exact Algebra.smul_def r (K a b)

/-- Nonnegative real scalar multiples of positive-definite kernels are positive definite. -/
theorem posSemidef_smul {K : α → α → 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hK : Matrix.PosSemidef K) :
    Matrix.PosSemidef (fun a b => r • K a b) := by
  have hr' : 0 ≤ (r : 𝕜) := by exact_mod_cast hr
  rw [real_smul_kernel_eq]
  exact hK.smul hr'

private theorem posSemidef_of_support_posSemidef (K : α → α → 𝕜)
    (hHerm : (Matrix.of fun a b => K a b).IsHermitian) (hgram : ∀ x : α →₀ 𝕜,
      (Matrix.of fun i j : x.support => K (i : α) (j : α)).PosSemidef) :
    (Matrix.of fun a b => K a b).PosSemidef := by
  classical
  refine ⟨hHerm, fun x => ?_⟩
  let y : x.support → 𝕜 := fun i => x i
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hgram x)).2 y
  have h' :
      0 ≤ ∑ i : x.support, ∑ j : x.support,
        star (x (i : α)) * (K (i : α) (j : α) * x (j : α)) := by
    simpa only [y, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
      Finset.mul_sum, RCLike.star_def, mul_assoc] using h
  have h'' :
      0 ≤ ∑ i ∈ x.support, ∑ j ∈ x.support,
        star (x i) * (K i j * x j) := by
    convert h' using 1
    rw [Finset.sum_subtype x.support (by intro a; rfl)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_subtype x.support (by intro a; rfl)]
  simpa only [Matrix.of_apply, Finsupp.sum, mul_assoc] using h''

private theorem matrixOf_conj_mul_eq_vecMulVec (g : α → 𝕜) :
    Matrix.of (fun a b => conj (g a) * g b) = Matrix.vecMulVec (star g) g := by
  ext a b
  simp only [Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, starRingEnd_apply]

private theorem conj_mul_kernel_isHermitian (g : α → 𝕜) :
    (Matrix.of fun a b => conj (g a) * g b).IsHermitian := by
  rw [matrixOf_conj_mul_eq_vecMulVec]
  ext a b
  simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Pi.star_apply, mul_comm]

/-- The rank-one kernels `(a, b) ↦ conj (g a) · g b` are positive definite. With `g ≡ 1` this gives
the constant kernel `1`; with general `g` these are building blocks whose nonnegative mixtures
and Schur products generate further positive-definite kernels. -/
theorem posSemidef_conj_mul (g : α → 𝕜) :
  Matrix.PosSemidef (fun a b => conj (g a) * g b) := by
  refine posSemidef_of_support_posSemidef _ (conj_mul_kernel_isHermitian g) ?_
  intro x
  exact (matrixOf_conj_mul_eq_vecMulVec (g := fun i : x.support => g (i : α))).symm ▸
    Matrix.posSemidef_vecMulVec_star_self _

/-- The zero kernel is positive definite. -/
theorem posSemidef_zero :
    Matrix.PosSemidef (fun _ _ : α => (0 : 𝕜)) := by
  simpa using posSemidef_conj_mul (𝕜 := 𝕜) (α := α) (fun _ => (0 : 𝕜))

/-- The constant kernel with value `1` is positive definite. -/
theorem posSemidef_one :
    Matrix.PosSemidef (fun _ _ : α => (1 : 𝕜)) := by
  simpa using posSemidef_conj_mul (𝕜 := 𝕜) (α := α) (fun _ => (1 : 𝕜))

private theorem smul_one_kernel_eq (c : 𝕜) :
    c • (fun _ _ : α => (1 : 𝕜)) = fun _ _ : α => c := by
  ext a b
  simp

/-- A nonnegative constant gives a positive-definite constant kernel. -/
theorem posSemidef_const_of_nonneg {c : 𝕜} (hc : 0 ≤ c) :
    Matrix.PosSemidef (fun _ _ : α => c) := by
  rw [← smul_one_kernel_eq]
  exact (posSemidef_one (𝕜 := 𝕜) (α := α)).smul hc

/-- The quadratic-form characterization of a positive-definite kernel: `K` is positive definite if
and only if it is conjugate-symmetric and every Hermitian form
`∑ᵢⱼ conj (x i) · x j · K (v i) (v j)` is nonnegative. The reverse direction is the introduction
rule that builds a positive-definite kernel directly from the quadratic-form condition (for
instance for the `K(a, b) = F(a + b⋆)` construction), without unfolding `Matrix.PosSemidef`. -/
theorem posSemidef_iff {K : α → α → 𝕜} :
    Matrix.PosSemidef K ↔
      (∀ a b, conj (K a b) = K b a) ∧
        ∀ {ι : Type*} [Fintype ι] (v : ι → α) (x : ι → 𝕜),
          0 ≤ ∑ i, ∑ j, conj (x i) * x j * K (v i) (v j) := by
  classical
  refine ⟨fun hK => ⟨posSemidef_conj_symm hK, ?_⟩, fun ⟨hsymm, hpos⟩ => ?_⟩
  · intro ι _ v x
    have hgram : (Matrix.of fun i j => K (v i) (v j)).PosSemidef := by
      simpa [Matrix.submatrix, Function.comp_def] using hK.submatrix v
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hgram).2 x
    simpa [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
      RCLike.star_def, mul_assoc, mul_left_comm, mul_comm] using h
  refine posSemidef_of_support_posSemidef K ?_ ?_
  · ext a b
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, ← starRingEnd_apply]
    exact hsymm b a
  · intro x
    let e : ULift (Fin (Fintype.card x.support)) ≃ x.support :=
      Equiv.ulift.trans (Fintype.equivFin x.support).symm
    refine (Matrix.posSemidef_submatrix_equiv e).mp ?_
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun y => ?_⟩
    · ext i j
      rw [Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.submatrix_apply,
        Matrix.of_apply, Matrix.of_apply, ← starRingEnd_apply]
      exact hsymm (e j : α) (e i : α)
    · refine (hpos (ι := ULift (Fin (Fintype.card x.support)))
        (fun i => (e i : α)) y).trans_eq ?_
      simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Matrix.of_apply,
        Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [starRingEnd_apply]
      ring

end TauCeti
