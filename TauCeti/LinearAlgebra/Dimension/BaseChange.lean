/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The dimension of a base change

A module specified as a base change of a finite module is finite. If the module being extended is
free and both rings satisfy the strong rank condition, then the two modules have the same rank.
Both statements are about Mathlib's `IsBaseChange` predicate rather than about the concrete tensor
product `S ⊗[R] M`, so they apply to a model of the base change that is not literally a tensor
product — the situation the `IsBaseChange` interface exists to serve.

Mathlib proves the corresponding facts for the concrete tensor product (`Module.finrank_baseChange`
and the `Module.Finite` instance on `S ⊗[R] M`); transporting them along
`IsBaseChange.equiv : S ⊗[R] M ≃ₗ[S] N` is all that is needed.
-/

public section

namespace TauCeti

open scoped TensorProduct

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
variable [IsScalarTower R S N] {f : M →ₗ[R] N}

/-- A base change of a finite module is a finite module. -/
theorem finite_of_isBaseChange (hf : IsBaseChange S f) [Module.Finite R M] : Module.Finite S N :=
  Module.Finite.equiv hf.equiv

/-- A base change of a free module has the same rank as the module it extends when the source and
target rings satisfy the strong rank condition. -/
theorem finrank_of_isBaseChange (hf : IsBaseChange S f) [StrongRankCondition R]
    [StrongRankCondition S] [Module.Free R M] :
    Module.finrank S N = Module.finrank R M := by
  rw [← hf.equiv.finrank_eq, Module.finrank_baseChange]

end TauCeti
