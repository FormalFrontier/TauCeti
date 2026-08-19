/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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

/-- **The `lsmul` restriction is the restriction of the endomorphism.** `Algebra.lsmul K K V f`
acts as `f`, and membership in its `invtSubmodule` is the invariance condition
`LinearMap.restrict` asks for, so the two restrictions are the same map. -/
private theorem restrict_lsmul_eq_restrict {p : Submodule K V} (f : End K V)
    (hinv : p ∈ (Algebra.lsmul K K V f).invtSubmodule) :
    LinearMap.restrict (Algebra.lsmul K K V f) hinv = f.restrict hinv := rfl

/-- **An eigenspace is semisimple as a `K[X]`-module.** Carried through `AEval` along a proof
`hinv` that it is invariant, the `μ`-eigenspace of `f` is a semisimple `K[X]`-module. -/
private theorem isSemisimpleModule_mapSubmodule_eigenspace (f : End K V) (μ : K)
    (hinv : f.eigenspace μ ∈ (Algebra.lsmul K K V f).invtSubmodule) :
    IsSemisimpleModule K[X] (AEval.mapSubmodule K V f ⟨f.eigenspace μ, hinv⟩) := by
  -- `AEval.restrict_equiv_mapSubmodule` restricts `Algebra.lsmul K K V f` rather than `f`;
  -- `restrict_lsmul_eq_restrict` is that identification, stated once
  have hres : LinearMap.restrict (p := f.eigenspace μ) (q := f.eigenspace μ)
      (Algebra.lsmul K K V f) hinv = μ • LinearMap.id :=
    (restrict_lsmul_eq_restrict f hinv).trans (Module.End.restrict_eigenspace f μ)
  refine (AEval.restrict_equiv_mapSubmodule f _ hinv).isSemisimpleModule_iff.mp ?_
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := X - C μ)
    (irreducible_X_sub_C μ).squarefree ?_
  rw [hres, map_sub, aeval_X, aeval_C, Module.algebraMap_end_eq_smul_id, sub_self]

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
      IsSemisimpleModule K[X] (AEval.mapSubmodule K V f ⟨f.eigenspace μ, hinv μ⟩) :=
    fun μ ↦ isSemisimpleModule_mapSubmodule_eigenspace f μ (hinv μ)
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
