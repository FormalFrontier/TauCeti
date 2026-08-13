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

Mathlib's `Matrix.PosSemidef` API supplies binary addition, nonnegative scalar multiplication, and
pointwise-product closure. The basic kernel file proves constant and rank-one kernels
`(a, b) ↦ conj (g a) * g b`. This module packages the finite-product and power consequences used
by finite-rank kernel constructions and the finite-dimensional approximations that feed the later
GNS/Kolmogorov decomposition.

No external formalization is vendored.

## Main declarations

* `TauCeti.posSemidef_prod`: finite pointwise products of positive-definite
  kernels.
* `TauCeti.posSemidef_pow`: Schur powers of a positive-definite kernel.

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

end TauCeti
