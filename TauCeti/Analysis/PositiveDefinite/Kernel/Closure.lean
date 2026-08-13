/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import TauCeti.Analysis.PositiveDefinite.Kernel.Basic

/-!
# Finite closure for positive-definite kernels

This file adds finite closure API for two-variable kernels whose corresponding matrix satisfies
Mathlib's `Matrix.PosSemidef` predicate, as used in the positive-definite-function and Bochner part
of the `OneParameterSemigroups` roadmap.

The basic kernel file already proves the constant kernels and binary closure operations: sums,
nonnegative scalar multiples, pointwise products, and rank-one kernels
`(a, b) ↦ conj (g a) * g b`. This module packages their finite consequences. These are the forms
used by finite-rank kernel constructions and by the finite-dimensional approximations that feed
the later GNS/Kolmogorov decomposition: finite sums of rank-one kernels are positive definite,
and finite Schur products of positive-definite kernels are positive definite.

No external formalization is vendored.

## Main declarations

* `TauCeti.posSemidef_prod`: finite pointwise products of positive-definite
  kernels.
* `TauCeti.posSemidef_sum_smul`: finite sums with nonnegative weights.
* `TauCeti.posSemidef_pow`: Schur powers of a positive-definite kernel.
* `TauCeti.posSemidef_sum_conj_mul`: finite sums of rank-one kernels.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open scoped ComplexConjugate ComplexOrder

namespace TauCeti

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {α : Type v}

/-- Finite pointwise products of positive-definite kernels are positive definite. -/
theorem posSemidef_prod {ι : Type w} {s : Finset ι}
    {K : ι → α → α → 𝕜} (hK : ∀ i ∈ s, Matrix.PosSemidef (K i)) :
    Matrix.PosSemidef (fun a b => ∏ i ∈ s, K i a b) := by
  have h := Finset.prod_induction K Matrix.PosSemidef
    (fun _ _ hA hB => hA.hadamard hB) posSemidef_one hK
  have heq : (∏ i ∈ s, K i) = fun a b => ∏ i ∈ s, K i a b := by
    ext a b
    simp
  rwa [heq] at h

/-- Finite sums of positive-definite kernels with nonnegative weights are positive
definite. This is the weighted finite-mixture form most often used in examples. -/
theorem posSemidef_sum_smul {ι : Type w} {s : Finset ι}
    {r : ι → 𝕜} {K : ι → α → α → 𝕜} (hr : ∀ i ∈ s, 0 ≤ r i)
    (hK : ∀ i ∈ s, Matrix.PosSemidef (K i)) :
    Matrix.PosSemidef (fun a b => ∑ i ∈ s, r i • K i a b) := by
  have h := Matrix.posSemidef_sum s fun i hi => (hK i hi).smul (hr i hi)
  have heq : (∑ i ∈ s, r i • K i) = fun a b => ∑ i ∈ s, r i • K i a b := by
    ext a b
    simp
  exact heq ▸ h

/-- Schur powers of a positive-definite kernel are positive definite. -/
theorem posSemidef_pow {K : α → α → 𝕜} (hK : Matrix.PosSemidef K) (n : ℕ) :
    Matrix.PosSemidef (fun a b => K a b ^ n) := by
  induction n with
  | zero =>
      simpa using posSemidef_one (𝕜 := 𝕜) (α := α)
  | succ n ih =>
      have h := ih.hadamard hK
      have heq : Matrix.hadamard (fun a b => K a b ^ n) K =
          fun a b => K a b ^ n * K a b := by
        ext a b
        rfl
      rw [heq] at h
      simpa [pow_succ] using h

/-- Finite sums of rank-one kernels `(a, b) ↦ conj (gᵢ a) * gᵢ b` are positive definite.
These are the finite-rank positive-definite kernels used as the elementary building blocks for
the later GNS/Kolmogorov decomposition. -/
theorem posSemidef_sum_conj_mul {ι : Type w} (s : Finset ι) (g : ι → α → 𝕜) :
    Matrix.PosSemidef
      (fun a b => ∑ i ∈ s, conj (g i a) * g i b) := by
  have h := Matrix.posSemidef_sum s fun i _ => posSemidef_conj_mul (g i)
  have heq : (∑ i ∈ s, fun a b => conj (g i a) * g i b) =
      fun a b => ∑ i ∈ s, conj (g i a) * g i b := by
    ext a b
    simp
  exact (congrArg (fun K => Matrix.PosSemidef K) heq).mp h

/-- Finite products of rank-one kernels are positive definite. This is the Schur-product
companion to `TauCeti.posSemidef_sum_conj_mul`. -/
theorem posSemidef_prod_conj_mul {ι : Type w} (s : Finset ι) (g : ι → α → 𝕜) :
    Matrix.PosSemidef
      (fun a b => ∏ i ∈ s, conj (g i a) * g i b) :=
  posSemidef_prod fun i _ => posSemidef_conj_mul (g i)

/-- Finite nonnegative combinations of rank-one kernels are positive definite. -/
theorem posSemidef_sum_smul_conj_mul {ι : Type w} {s : Finset ι}
    {r : ι → 𝕜} (hr : ∀ i ∈ s, 0 ≤ r i) (g : ι → α → 𝕜) :
    Matrix.PosSemidef
      (fun a b => ∑ i ∈ s, r i • (conj (g i a) * g i b)) :=
  posSemidef_sum_smul hr fun i _ => posSemidef_conj_mul (g i)

end TauCeti
