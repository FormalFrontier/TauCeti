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

/-- The image of a base-change map spans its target over the extending ring. -/
theorem span_range_eq_top_of_baseChange (hf : IsBaseChange S f) :
    Submodule.span S (Set.range f) = ⊤ := by
  have htop : Submodule.span S {t : S ⊗[R] M | ∃ s m, s ⊗ₜ[R] m = t} =
      (⊤ : Submodule S (S ⊗[R] M)) :=
    Submodule.span_eq_top_of_span_eq_top R S _ (TensorProduct.span_tmul_eq_top R S M)
  have htopN : Submodule.map hf.equiv.toLinearMap (⊤ : Submodule S (S ⊗[R] M)) =
      (⊤ : Submodule S N) := by
    rw [Submodule.map_top, LinearMap.range_eq_top]
    exact hf.equiv.surjective
  rw [← htopN]
  conv_rhs => rw [← htop]
  rw [Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨m, rfl⟩
    exact ⟨1 ⊗ₜ[R] m, ⟨1, m, rfl⟩, by simp [hf.equiv_tmul]⟩
  · apply Submodule.span_le.2
    rintro _ ⟨t, ⟨s, m, rfl⟩, rfl⟩
    -- Expose the pure tensor so that the base-change equation can identify its image.
    change hf.equiv (s ⊗ₜ[R] m) ∈ _
    rw [hf.equiv_tmul]
    exact Submodule.smul_mem _ s (Submodule.subset_span ⟨m, rfl⟩)

/-- A base change of a free module has the same rank as the module it extends when the source and
target rings satisfy the strong rank condition. -/
theorem finrank_of_isBaseChange (hf : IsBaseChange S f) [StrongRankCondition R]
    [StrongRankCondition S] [Module.Free R M] :
    Module.finrank S N = Module.finrank R M := by
  rw [← hf.equiv.finrank_eq, Module.finrank_baseChange]

/-- Compatible maps between two base changes commute with their scalar-extension equivalences. -/
theorem comp_equiv_eq_equiv_comp_baseChange_of_baseChange
    {M' N' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] [Module S N']
    [IsScalarTower R S N'] {f' : M' →ₗ[R] N'} (hf : IsBaseChange S f)
    (hf' : IsBaseChange S f') (u : M →ₗ[R] M') (g : N →ₗ[S] N')
    (hcompat : ∀ m, g (f m) = f' (u m)) :
    g.comp hf.equiv.toLinearMap = hf'.equiv.toLinearMap.comp (u.baseChange S) := by
  refine (TensorProduct.isBaseChange R M S).algHom_ext'
    (g.comp hf.equiv.toLinearMap)
    (hf'.equiv.toLinearMap.comp (u.baseChange S)) ?_
  ext m
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
    LinearMap.baseChange_tmul]
  -- Expose the pure tensors hidden by the scalar-extension wrappers.
  change g (hf.equiv (1 ⊗ₜ[R] m)) = hf'.equiv (1 ⊗ₜ[R] u m)
  rw [hf.equiv_tmul, hf'.equiv_tmul]
  simpa only [one_smul] using hcompat m

end TauCeti
