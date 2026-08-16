/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Unique finitely supported linear combinations

This file characterizes membership in the span of a linearly independent family by the existence
of a unique finitely supported linear combination.

## Main statements

* `TauCeti.LinearIndependent.mem_span_range_iff_existsUnique`: membership in the span of a
  linearly independent family is equivalent to having unique finitely supported coordinates.
-/

public section

namespace TauCeti.LinearIndependent

variable {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- An element lies in the span of a linearly independent family exactly when it has a unique
finitely supported expression in that family. -/
theorem mem_span_range_iff_existsUnique {v : ι → M} (h : LinearIndependent R v) (x : M) :
    x ∈ Submodule.span R (Set.range v) ↔
      ∃! a : ι →₀ R, a.sum (fun i r => r • v i) = x := by
  rw [Finsupp.mem_span_range_iff_exists_finsupp]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ha, fun b hb => ?_⟩
    apply h.finsuppLinearCombination_injective
    simpa only [Finsupp.linearCombination_apply] using hb.trans ha.symm
  · exact ExistsUnique.exists

end TauCeti.LinearIndependent
