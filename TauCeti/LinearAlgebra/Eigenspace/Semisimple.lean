/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

public section

/-!
# Diagonalizable endomorphisms are semisimple

Mathlib records that a semisimple endomorphism of a finite-dimensional vector space over an
algebraically closed field is diagonalizable
(`Module.End.IsSemisimple.iSup_eigenspace_eq_top`). This file proves the converse, which needs no
hypothesis on the field and no finiteness hypothesis on the space: an endomorphism whose
eigenspaces span is, as a `K[X]`-module, the sum of those eigenspaces, and on each of them `X` acts
by a scalar, so each is annihilated by the squarefree polynomial `X - C μ` and is semisimple.

## Main results

* `TauCeti.isSemisimple_of_iSup_eigenspace_eq_top`: an endomorphism whose eigenspaces span the
  space is semisimple.
-/

namespace TauCeti

open Module Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {f : End K V}

/-- **A diagonalizable endomorphism is semisimple.** If the eigenspaces of `f` span the space then
`f` is semisimple.

Semisimplicity of `f` is semisimplicity of `V` as a `K[X]`-module, and the eigenspaces are
`K[X]`-submodules spanning it, so it is enough that each is semisimple. On the `μ`-eigenspace `X`
acts by the scalar `μ`, so the restriction of `f` is annihilated by the squarefree polynomial
`X - C μ` and `Module.End.isSemisimple_of_squarefree_aeval_eq_zero` applies. Neither algebraic
closure nor finite dimension is needed; the converse
`Module.End.IsSemisimple.iSup_eigenspace_eq_top` is where both enter. -/
theorem isSemisimple_of_iSup_eigenspace_eq_top (hf : ⨆ μ : K, f.eigenspace μ = ⊤) :
    f.IsSemisimple := by
  -- `f` acts on its `μ`-eigenspace as multiplication by `μ`, so that eigenspace is invariant
  have hinv : ∀ μ : K, f.eigenspace μ ∈ (Algebra.lsmul K K V f).invtSubmodule := fun μ v hv ↦ by
    rw [End.mem_eigenspace_iff] at hv
    simp [hv]
  have hss : ∀ μ : K,
      IsSemisimpleModule K[X] (AEval.mapSubmodule K V f ⟨f.eigenspace μ, hinv μ⟩) := fun μ ↦ by
    -- `AEval.restrict_equiv_mapSubmodule` restricts `Algebra.lsmul K K V f`, not `f`, to the
    -- `μ`-eigenspace, and it hands `LinearMap.restrict` an invariance proof of type
    -- `p ∈ (Algebra.lsmul K K V f).invtSubmodule`, where `LinearMap.restrict` asks for
    -- `∀ x ∈ p, g x ∈ p`. Those two types are definitionally equal only at default transparency,
    -- so `LinearMap.coe_restrict_apply` cannot be instantiated against the goal below directly.
    -- Recording the composite coercion here once, with the submodules supplied explicitly, keeps
    -- the step below lemma-driven.
    have hrestrict (w : f.eigenspace μ) :
        (LinearMap.restrict (p := f.eigenspace μ) (q := f.eigenspace μ)
          (Algebra.lsmul K K V f) (hinv μ) w : V) = f w :=
      (LinearMap.coe_restrict_apply _ _).trans
        ((Algebra.lsmul_apply (R := K) (B := K) V f w).trans (Module.End.smul_def f w))
    refine (AEval.restrict_equiv_mapSubmodule f _ (hinv μ)).isSemisimpleModule_iff.mp ?_
    refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := X - C μ)
      (irreducible_X_sub_C μ).squarefree ?_
    ext v
    have hv := v.2
    rw [End.mem_eigenspace_iff] at hv
    simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, LinearMap.zero_apply,
      Module.algebraMap_end_apply, Submodule.coe_sub, Submodule.coe_smul, ZeroMemClass.coe_zero]
    -- the restriction of `f` to the `μ`-eigenspace is multiplication by `μ`
    rw [hrestrict, hv, sub_self]
  have htop : ⨆ μ : K, AEval.mapSubmodule K V f ⟨f.eigenspace μ, hinv μ⟩ = ⊤ := by
    set Q := ⨆ μ : K, AEval.mapSubmodule K V f ⟨f.eigenspace μ, hinv μ⟩
    have hle : (⊤ : Submodule K V) ≤ (Q.restrictScalars K).comap (AEval'.of f).toLinearMap := by
      rw [← hf]
      refine iSup_le fun μ v hv ↦ ?_
      -- membership in the comap of `Q` is membership of the image in `Q`
      rw [Submodule.mem_comap, Submodule.restrictScalars_mem]
      exact Submodule.mem_iSup_of_mem μ (by simpa using hv)
    refine Submodule.eq_top_iff'.2 fun m ↦ ?_
    simpa using hle (Submodule.mem_top (x := (AEval'.of f).symm m))
  exact isSemisimpleModule_of_isSemisimpleModule_submodule' hss htop

end TauCeti
