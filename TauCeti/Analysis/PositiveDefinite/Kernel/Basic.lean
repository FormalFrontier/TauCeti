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
GNS/Kolmogorov decomposition". Mathlib has positive definiteness only for matrices and quadratic
forms, with no positive-definite-kernel notion, so this is new; no code is vendored.

## Main definitions

* `TauCeti.IsPositiveDefiniteKernel`: the predicate that the full kernel matrix is positive
  semidefinite.

## Main statements

* `TauCeti.isPositiveDefiniteKernel_def`: the bridge to Mathlib's arbitrary-index
  `Matrix.PosSemidef` predicate on `Matrix.of K`.
* `TauCeti.isPositiveDefiniteKernel_apply_self_nonneg`: diagonal entries of a positive-definite
  kernel are nonnegative.
* `TauCeti.isPositiveDefiniteKernel_conj_symm`: positive-definite kernels are
  conjugate-symmetric.
* `TauCeti.isPositiveDefiniteKernel_comp`: positive definiteness is preserved by pullback.
* `TauCeti.isPositiveDefiniteKernel_zero`, `TauCeti.isPositiveDefiniteKernel_one`, and
  `TauCeti.isPositiveDefiniteKernel_const_of_nonneg`: constant positive-definite kernels.
* `TauCeti.isPositiveDefiniteKernel_add`, `TauCeti.isPositiveDefiniteKernel_smul`, and
  `TauCeti.isPositiveDefiniteKernel_smul_of_nonneg`: closure under sums, nonnegative real scalar
  multiples, and nonnegative scalar multiples in the codomain.
* `TauCeti.isPositiveDefiniteKernel_mul`: closure under pointwise products.
* `TauCeti.isPositiveDefiniteKernel_iff`: the quadratic-form characterization, whose reverse
  direction builds a positive-definite kernel from conjugate symmetry and form nonnegativity.
* `TauCeti.isPositiveDefiniteKernel_conj_mul`: the rank-one kernels
  `(a, b) ↦ conj(g a) · g b`.
-/

public section

open Matrix
open scoped ComplexConjugate ComplexOrder

namespace TauCeti

universe u v z

variable {𝕜 : Type u} [RCLike 𝕜]
variable {α : Type v}

/-- A kernel `K : α → α → 𝕜` is *positive definite* when the matrix indexed by all points of `α`
is positive semidefinite. -/
@[expose] def IsPositiveDefiniteKernel (K : α → α → 𝕜) : Prop :=
  (Matrix.of fun a b => K a b).PosSemidef

/-- The named kernel predicate is definitionally Mathlib's positive semidefinite predicate on the
full kernel matrix. -/
theorem isPositiveDefiniteKernel_def (K : α → α → 𝕜) :
    IsPositiveDefiniteKernel K ↔ (Matrix.of fun a b => K a b).PosSemidef := by
  rfl

/-- Diagonal values of a positive-definite kernel are nonnegative. -/
theorem isPositiveDefiniteKernel_apply_self_nonneg {K : α → α → 𝕜}
    (hK : IsPositiveDefiniteKernel K) (a : α) : 0 ≤ K a a := by
  have hK' := (isPositiveDefiniteKernel_def K).mp hK
  simpa [Finsupp.sum_single_index] using hK'.2 (Finsupp.single a 1)

/-- Positive-definite kernels are conjugate-symmetric. -/
theorem isPositiveDefiniteKernel_conj_symm {K : α → α → 𝕜}
    (hK : IsPositiveDefiniteKernel K) (a b : α) : conj (K a b) = K b a := by
  have hK' := (isPositiveDefiniteKernel_def K).mp hK
  have h := hK'.isHermitian.apply b a
  simp only [Matrix.of_apply] at h
  rw [starRingEnd_apply]
  exact h

/-- Pulling back a positive-definite kernel along a map preserves positive definiteness. -/
theorem isPositiveDefiniteKernel_comp {β : Type z} {K : α → α → 𝕜}
    (hK : IsPositiveDefiniteKernel K) (f : β → α) :
    IsPositiveDefiniteKernel (fun a b => K (f a) (f b)) := by
  have hK' := (isPositiveDefiniteKernel_def K).mp hK
  rw [isPositiveDefiniteKernel_def]
  simpa [Matrix.submatrix, Function.comp_def] using hK'.submatrix f

/-- Sums of positive-definite kernels are positive definite. -/
theorem isPositiveDefiniteKernel_add {K L : α → α → 𝕜}
    (hK : IsPositiveDefiniteKernel K) (hL : IsPositiveDefiniteKernel L) :
    IsPositiveDefiniteKernel (fun a b => K a b + L a b) := by
  rw [isPositiveDefiniteKernel_def] at hK hL ⊢
  convert hK.add hL using 1
  ext a b
  rfl

/-- Nonnegative scalar multiples in the codomain of positive-definite kernels are positive
definite. -/
theorem isPositiveDefiniteKernel_smul_of_nonneg {K : α → α → 𝕜} {c : 𝕜} (hc : 0 ≤ c)
    (hK : IsPositiveDefiniteKernel K) :
    IsPositiveDefiniteKernel (fun a b => c • K a b) := by
  rw [isPositiveDefiniteKernel_def] at hK ⊢
  convert hK.smul hc using 1
  ext a b
  rfl

/-- Nonnegative real scalar multiples of positive-definite kernels are positive definite. -/
theorem isPositiveDefiniteKernel_smul {K : α → α → 𝕜} {r : ℝ} (hr : 0 ≤ r)
    (hK : IsPositiveDefiniteKernel K) :
    IsPositiveDefiniteKernel (fun a b => r • K a b) := by
  convert isPositiveDefiniteKernel_smul_of_nonneg (𝕜 := 𝕜) (α := α) (K := K)
    (c := (r : 𝕜)) (by exact_mod_cast hr) hK using 1
  ext a b
  exact Algebra.smul_def r (K a b)

/-- Pointwise products of positive-definite kernels are positive definite. -/
theorem isPositiveDefiniteKernel_mul {K L : α → α → 𝕜}
    (hK : IsPositiveDefiniteKernel K) (hL : IsPositiveDefiniteKernel L) :
    IsPositiveDefiniteKernel (fun a b => K a b * L a b) := by
  rw [isPositiveDefiniteKernel_def] at hK hL ⊢
  convert hK.hadamard hL using 1
  ext a b
  rfl

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

/-- The rank-one kernels `(a, b) ↦ conj (g a) · g b` are positive definite. With `g ≡ 1` this gives
the constant kernel `1`; with general `g` these are building blocks whose nonnegative mixtures
and Schur products generate further positive-definite kernels. -/
theorem isPositiveDefiniteKernel_conj_mul (g : α → 𝕜) :
    IsPositiveDefiniteKernel (fun a b => conj (g a) * g b) := by
  classical
  rw [isPositiveDefiniteKernel_def]
  refine posSemidef_of_support_posSemidef _ ?_ ?_
  · ext a b
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, ← starRingEnd_apply]
    simp [mul_comm]
  · intro x
    have e : (Matrix.of fun i j : x.support => conj (g (i : α)) * g (j : α))
        = Matrix.vecMulVec (star fun i : x.support => g (i : α))
            (fun i : x.support => g (i : α)) := by
      ext i j
      simp only [Matrix.of_apply, Matrix.vecMulVec_apply, Pi.star_apply, starRingEnd_apply]
    rw [e]
    exact Matrix.posSemidef_vecMulVec_star_self _

/-- The zero kernel is positive definite. -/
theorem isPositiveDefiniteKernel_zero :
    IsPositiveDefiniteKernel (fun _ _ : α => (0 : 𝕜)) := by
  simpa using isPositiveDefiniteKernel_conj_mul (𝕜 := 𝕜) (α := α) (fun _ => (0 : 𝕜))

/-- The constant kernel with value `1` is positive definite. -/
theorem isPositiveDefiniteKernel_one :
    IsPositiveDefiniteKernel (fun _ _ : α => (1 : 𝕜)) := by
  simpa using isPositiveDefiniteKernel_conj_mul (𝕜 := 𝕜) (α := α) (fun _ => (1 : 𝕜))

/-- A nonnegative constant gives a positive-definite constant kernel. -/
theorem isPositiveDefiniteKernel_const_of_nonneg {c : 𝕜} (hc : 0 ≤ c) :
    IsPositiveDefiniteKernel (fun _ _ : α => c) := by
  convert isPositiveDefiniteKernel_smul_of_nonneg (𝕜 := 𝕜) (α := α)
    (K := fun _ _ : α => (1 : 𝕜)) hc isPositiveDefiniteKernel_one using 1
  ext a b
  simp

/-- The quadratic-form characterization of a positive-definite kernel: `K` is positive definite if
and only if it is conjugate-symmetric and every Hermitian form
`∑ᵢⱼ conj (x i) · x j · K (v i) (v j)` is nonnegative. The reverse direction is the introduction
rule that builds a positive-definite kernel directly from the quadratic-form condition (for
instance for the `K(a, b) = F(a + b⋆)` construction), without unfolding `Matrix.PosSemidef`. -/
theorem isPositiveDefiniteKernel_iff {K : α → α → 𝕜} :
    IsPositiveDefiniteKernel K ↔
      (∀ a b, conj (K a b) = K b a) ∧
        ∀ {ι : Type*} [Fintype ι] (v : ι → α) (x : ι → 𝕜),
          0 ≤ ∑ i, ∑ j, conj (x i) * x j * K (v i) (v j) := by
  classical
  refine ⟨fun hK => ⟨isPositiveDefiniteKernel_conj_symm hK, ?_⟩, fun ⟨hsymm, hpos⟩ => ?_⟩
  · intro ι _ v x
    have hgram : (Matrix.of fun i j => K (v i) (v j)).PosSemidef := by
      have hK' := (isPositiveDefiniteKernel_def K).mp hK
      simpa [Matrix.submatrix, Function.comp_def] using hK'.submatrix v
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hgram).2 x
    simpa [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
      RCLike.star_def, mul_assoc, mul_left_comm, mul_comm] using h
  rw [isPositiveDefiniteKernel_def]
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
