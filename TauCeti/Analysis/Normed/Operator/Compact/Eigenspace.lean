/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finite-dimensional eigenspaces of compact operators

This file develops Riesz--Schauder input used for compact perturbations of Fredholm operators. A
compact operator on a normed space has a finite-dimensional eigenspace at every nonzero scalar.
More generally, every finite stage of the corresponding generalized eigenspace is finite
dimensional.

The eigenspace proof restricts the compact operator to its eigenspace, where it is a nonzero
scalar multiple of the identity. Compactness of that identity forces finite dimensionality. The
generalized statement then uses the filtration by kernels of `(T - μ)^n`: the difference operator
maps stage `n + 1` into stage `n`, and its kernel embeds into the ordinary eigenspace.

Mathlib proves the eigenspace result as
`ContinuousLinearMap.finite_dimensional_eigenspace` in the setting of complete inner-product
spaces over `RCLike` fields. The argument used there needs neither an inner product nor completeness
of the ambient space; the declarations below record it over arbitrary complete nontrivially normed
fields, the generality required by Fredholm theory.

## Main declarations

* `IsCompactOperator.finiteDimensional_eigenspace`: a nonzero eigenspace of a compact operator is
  finite dimensional.
* `IsCompactOperator.finiteDimensional_genEigenspace_nat`: every finite-order generalized
  eigenspace at a nonzero scalar is finite dimensional.

The mathematical argument is the finite-dimensional eigenspace step in the Riesz--Schauder
theory; see, for example, Conway, *A Course in Functional Analysis*, Chapter VI, Section 5.
-/

public section

namespace TauCeti

open Module End

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {T : E →L[𝕜] E} {μ : 𝕜}

namespace IsCompactOperator

/-- A nonzero eigenspace of a compact operator on a normed space is finite dimensional.

Unlike Mathlib's `ContinuousLinearMap.finite_dimensional_eigenspace`, this needs no inner product
and works over any complete nontrivially normed field. -/
theorem finiteDimensional_eigenspace (hT : IsCompactOperator T) (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (eigenspace T.toLinearMap μ) := by
  have hT' := hT.restrict
    ((mem_invtSubmodule_iff_forall_mem_of_mem _).mp
      (eigenspace_mem_invtSubmodule T.toLinearMap μ))
    (ContinuousLinearMap.isClosed_eigenspace T μ)
  rw [restrict_eigenspace, LinearMap.coe_smul, IsCompactOperator.smul_iff₀ hμ] at hT'
  exact FiniteDimensional.of_isCompactOperator_id hT'

omit [CompleteSpace 𝕜] in
/-- The difference operator sends generalized eigenspace stage `n + 1` to stage `n`. -/
private def genEigenspaceSuccMap (f : Module.End 𝕜 E) (μ : 𝕜) (n : ℕ) :
    genEigenspace f μ ((n + 1 : ℕ) : ℕ∞) →ₗ[𝕜] genEigenspace f μ n :=
  (f - μ • 1).restrict fun x hx => by
    have hx' : ((f - μ • 1) ^ (n + 1)) x = 0 := by
      rw [← LinearMap.mem_ker, ← mem_genEigenspace_nat]
      exact hx
    apply (mem_genEigenspace_nat (f := f) (μ := μ) (k := n)).mpr
    rw [LinearMap.mem_ker]
    simpa only [pow_succ, Module.End.mul_apply] using hx'

omit [CompleteSpace 𝕜] in
/-- One step of the generalized-eigenspace filtration preserves finite dimensionality once the
ordinary eigenspace is finite dimensional. -/
private theorem finiteDimensional_genEigenspace_succ
    (heig : FiniteDimensional 𝕜 (eigenspace T.toLinearMap μ))
    (n : ℕ) (hn : FiniteDimensional 𝕜 (genEigenspace T.toLinearMap μ n)) :
    FiniteDimensional 𝕜 (genEigenspace T.toLinearMap μ ((n + 1 : ℕ) : ℕ∞)) := by
  let A := genEigenspaceSuccMap T.toLinearMap μ n
  have heigker : FiniteDimensional 𝕜 (LinearMap.ker (T.toLinearMap - μ • 1)) := by
    rwa [← eigenspace_def]
  have hker : FiniteDimensional 𝕜 (LinearMap.ker A) := by
    have hkerA : LinearMap.ker A =
        (LinearMap.ker (T.toLinearMap - μ • 1)).comap
          (genEigenspace T.toLinearMap μ ((n + 1 : ℕ) : ℕ∞)).subtype := by
      dsimp only [A, genEigenspaceSuccMap]
      exact LinearMap.ker_restrict _
    rw [hkerA]
    let := heigker
    let _ : FiniteDimensional 𝕜
        (LinearMap.ker
          (genEigenspace T.toLinearMap μ ((n + 1 : ℕ) : ℕ∞)).subtype) := by
      rw [Submodule.ker_subtype]
      infer_instance
    infer_instance
  have hrange : FiniteDimensional 𝕜 (LinearMap.range A) := by
    let := hn
    infer_instance
  refine ⟨(⊤ : Submodule 𝕜 (genEigenspace T.toLinearMap μ ((n + 1 : ℕ) : ℕ∞)))
    |>.fg_of_fg_map_of_fg_inf_ker A ?_ ?_⟩
  · rw [Submodule.map_top]
    exact (Submodule.fg_iff_finiteDimensional _).mpr hrange
  · rw [top_inf_eq]
    exact (Submodule.fg_iff_finiteDimensional _).mpr hker

omit [CompleteSpace 𝕜] in
/-- If the ordinary `μ`-eigenspace is finite dimensional, then so is every finite stage of the
generalized `μ`-eigenspace filtration. -/
private theorem finiteDimensional_genEigenspace_nat_of_eigenspace
    (hfinite : FiniteDimensional 𝕜 (eigenspace T.toLinearMap μ)) (n : ℕ) :
    FiniteDimensional 𝕜 (genEigenspace T.toLinearMap μ n) := by
  induction n with
  | zero =>
      -- Normalize the coerced induction index to the `ℕ∞` zero used by `genEigenspace_zero`.
      change FiniteDimensional 𝕜 (genEigenspace T.toLinearMap μ (0 : ℕ∞))
      rw [genEigenspace_zero]
      infer_instance
  | succ n ih =>
      exact finiteDimensional_genEigenspace_succ hfinite n ih

/-- Every finite stage of the generalized eigenspace of a compact operator at a nonzero scalar is
finite dimensional. In particular, compact operators have no infinite-dimensional finite-order
Jordan block at a nonzero eigenvalue. -/
theorem finiteDimensional_genEigenspace_nat (hT : IsCompactOperator T) (hμ : μ ≠ 0) (n : ℕ) :
    FiniteDimensional 𝕜 (genEigenspace T.toLinearMap μ n) :=
  finiteDimensional_genEigenspace_nat_of_eigenspace (finiteDimensional_eigenspace hT hμ) n

end IsCompactOperator

end TauCeti

end
