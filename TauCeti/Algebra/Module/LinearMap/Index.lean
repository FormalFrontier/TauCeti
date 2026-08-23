/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Index

/-!
# Index of linear maps

This file extends Mathlib's algebraic `LinearMap.index` API with its invariance under composing
with a linear equivalence.

These composition lemmas are absent from `Mathlib.Algebra.Module.LinearMap.Index` and support the
continuous-linear-map results in `TauCeti.Analysis.Fredholm.Index`.
-/

public section

namespace LinearMap

variable {R M N P : Type*} [Ring R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- Postcomposition with a linear equivalence leaves the index unchanged. -/
@[simp]
lemma index_equiv_comp (f : M →ₗ[R] N) (e : N ≃ₗ[R] P) :
    ((e : N →ₗ[R] P).comp f).index = f.index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub]
  congr 1
  · rw [ker_comp_of_ker_eq_bot _ (ker_eq_bot.2 e.injective)]
  · rw [range_comp]
    exact_mod_cast (LinearEquiv.finrank_eq
      (Submodule.Quotient.equiv f.range (f.range.map (e : N →ₗ[R] P)) e rfl)).symm

/-- Precomposition with a linear equivalence leaves the index unchanged. -/
@[simp]
lemma index_comp_equiv (f : M →ₗ[R] N) (e : P ≃ₗ[R] M) :
    (f.comp (e : P →ₗ[R] M)).index = f.index := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub]
  congr 1
  · rw [ker_comp, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  · rw [range_comp_of_range_eq_top _ (range_eq_top.2 e.surjective)]

end LinearMap
