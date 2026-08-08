/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple

public section

/-!
# Diagonalizable endomorphisms are semisimple

Mathlib records that a semisimple endomorphism of a finite-dimensional vector space over an
algebraically closed field is diagonalizable
(`Module.End.IsSemisimple.iSup_eigenspace_eq_top`). This file proves the converse, which needs no
hypothesis on the field: an endomorphism whose eigenspaces span is annihilated by the product of
`X - μ` over its finitely many eigenvalues, a squarefree polynomial, so
`Module.End.isSemisimple_of_squarefree_aeval_eq_zero` applies.

The two together characterise semisimplicity over an algebraically closed field, which is
`TauCeti.isSemisimple_iff_iSup_eigenspace_eq_top`.

## Main results

* `TauCeti.isSemisimple_of_iSup_eigenspace_eq_top`: an endomorphism of a finite-dimensional vector
  space whose eigenspaces span the space is semisimple.
* `TauCeti.isSemisimple_iff_iSup_eigenspace_eq_top`: over an algebraically closed field,
  semisimplicity is diagonalizability.
-/

namespace TauCeti

open Module Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {f : End K V}

/-- **A diagonalizable endomorphism is semisimple.** If the eigenspaces of `f` span a
finite-dimensional vector space then `f` is semisimple.

There are finitely many eigenvalues, and `f` is annihilated by the product of the `X - μ` over
them: that product is squarefree, having distinct linear factors, so
`Module.End.isSemisimple_of_squarefree_aeval_eq_zero` applies. No hypothesis on the field is
needed; the converse `Module.End.IsSemisimple.iSup_eigenspace_eq_top` is where algebraic closure
enters. -/
theorem isSemisimple_of_iSup_eigenspace_eq_top (hf : ⨆ μ : K, f.eigenspace μ = ⊤) :
    f.IsSemisimple := by
  classical
  set s : Finset K := f.finite_hasEigenvalue.toFinset with hs
  set p : K[X] := ∏ μ ∈ s, (X - C μ) with hp
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := p) ?_ ?_
  · exact (separable_prod_X_sub_C_iff'.2 (Set.injOn_id _)).squarefree
  · refine LinearMap.ker_eq_top.1 (top_le_iff.1 ?_)
    refine hf ▸ iSup_le fun μ v hv ↦ ?_
    by_cases hμ : f.HasEigenvalue μ
    · have heval : p.eval μ = 0 := by
        rw [hp, eval_prod]
        exact Finset.prod_eq_zero (by simpa [hs] using hμ) (by simp)
      have : aeval f p v = p.eval μ • v :=
        End.aeval_apply_of_mem_apply_eq_smul (End.mem_eigenspace_iff.1 hv)
      simp [LinearMap.mem_ker, this, heval]
    · rw [End.hasEigenvalue_iff, not_not] at hμ
      have hv0 : v = 0 := by simpa [hμ] using hv
      simp [hv0]

/-- **Semisimplicity is diagonalizability**, over an algebraically closed field and in finite
dimension. -/
theorem isSemisimple_iff_iSup_eigenspace_eq_top [IsAlgClosed K] :
    f.IsSemisimple ↔ ⨆ μ : K, f.eigenspace μ = ⊤ :=
  ⟨End.IsSemisimple.iSup_eigenspace_eq_top, isSemisimple_of_iSup_eigenspace_eq_top⟩

end TauCeti
