/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.Algebra.Lie.Weights.Basic
public import TauCeti.LinearAlgebra.Submodule.SupIndep

/-!
# Weight spaces of a tensor product of Lie modules

Let `L` be a nilpotent Lie algebra acting on two modules `M` and `N`. Then `L` acts on `M ⊗ N`, and
this file computes the generalized weight spaces of that action: the `χ`-weight space of `M ⊗ N` is
spanned by the pure tensors `m ⊗ₜ n` with `m` of weight `μ`, `n` of weight `ν` and `μ + ν = χ`.

Two facts meet. Mathlib's `LieModule.weight_vector_multiplication` already says that a pure tensor
of a generalized eigenvector of weight `μ x` and one of weight `ν x` is a generalized eigenvector of
weight `μ x + ν x`, so the *inclusion* `Mμ ⊗ Nν ≤ (M ⊗ N)_{μ+ν}` needs no hypothesis beyond
nilpotency of `L`. The reverse inclusion is not a computation but a counting argument: over a field,
in finite dimensions and with `M` and `N` triangularizable, the pure tensors of weight vectors
already span `M ⊗ N`, so the coarse family indexed by `χ` refines the independent family of weight
spaces of `M ⊗ N` and must agree with it termwise
(`TauCeti.eq_of_le_of_iSup_eq_iSup`).

The counting argument yields the exhaustion `⨆ χ, (M ⊗ N)_χ = ⊤` on the way, so `M ⊗ N` is itself
triangularizable with no algebraic closure assumed: it is triangularizable as soon as `M` and `N`
are. That instance is what lets the weight theory be applied again to the tensor product.

## Main results

* `TauCeti.tmul_mem_genWeightSpace_add`: **weights add on pure tensors.** If `m` has weight `μ` and
  `n` has weight `ν`, then `m ⊗ₜ n` has weight `μ + ν`, and
  `TauCeti.map₂_mk_genWeightSpace_le` is the submodule form.
* `TauCeti.iSup_map₂_mk_genWeightSpace_eq_top`: the pure tensors of weight vectors span `M ⊗ N`.
* `TauCeti.iSup_genWeightSpace_tensorProduct_eq_top` and
  `TauCeti.isTriangularizable_tensorProduct`: the weight spaces of `M ⊗ N` exhaust it, so the
  tensor product of two triangularizable finite-dimensional modules is triangularizable.
* `TauCeti.genWeightSpace_tensorProduct_eq_iSup`: **the weight-space decomposition of a tensor
  product.** The `χ`-weight space of `M ⊗ N` is the supremum, over the pairs `(μ, ν)` with
  `μ + ν = χ`, of the submodules spanned by `Mμ ⊗ Nν`.
* `TauCeti.exists_add_eq_of_genWeightSpace_tensorProduct_ne_bot` and
  `TauCeti.exists_weight_add_eq`: **every weight of `M ⊗ N` is a sum of a weight of `M` and a weight
  of `N`.**

## Implementation notes

The submodule spanned by the pure tensors `m ⊗ₜ n` with `m ∈ Mμ` and `n ∈ Nν` is written as
Mathlib's `Submodule.map₂ (TensorProduct.mk R M N)`, the submodule image of a bilinear map, rather
than through a new definition: the supremum and monotonicity API the proofs need
(`Submodule.map₂_iSup_left`, `Submodule.map₂_le`) is already stated for it.

The weight spaces are Mathlib's *generalized* weight spaces `LieModule.genWeightSpace`, so the
statements below are read in `Submodule R (M ⊗[R] N)` rather than in the lattice of Lie submodules;
`LieSubmodule.toSubmodule` mediates. Nothing here needs the weight spaces to be honest eigenspaces.

The multiplicity count `dim (M ⊗ N)_χ = ∑_{μ + ν = χ} dim Mμ · dim Nν`, which is what a formal
character consumes, needs in addition that the family indexed by *pairs* `(μ, ν)` is independent,
and is not proved here.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre VII, §1.1, Proposition 2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §20.
* [Highest-weight roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md),
  Layer 6, "The representation ring and the character algebra", which asks for the tensor product of
  Lie modules as the preliminary to a formal character multiplicative on tensor products
  (`formalCharacter_tensor`); this file supplies its weight-theoretic half.
-/

public section

open LieModule Module TensorProduct

namespace TauCeti

universe u v w w₁

/-! ### Weights add on pure tensors -/

section CommRing

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
  [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- **Weights add on pure tensors.** A pure tensor of a vector of generalized weight `χ` in `M` and
a vector of generalized weight `ψ` in `N` has generalized weight `χ + ψ` in `M ⊗ N`.

This is Mathlib's `LieModule.weight_vector_multiplication`, applied one element `x : L` at a time
to the identity map of `M ⊗ N`. No finiteness or triangularizability is involved. -/
theorem tmul_mem_genWeightSpace_add {χ ψ : L → R} {m : M} {n : N}
    (hm : m ∈ genWeightSpace M χ) (hn : n ∈ genWeightSpace N ψ) :
    m ⊗ₜ[R] n ∈ genWeightSpace (M ⊗[R] N) (χ + ψ) := by
  rw [mem_genWeightSpace] at hm hn ⊢
  intro x
  have key := LieModule.weight_vector_multiplication (R := R) (L := L) M N (M ⊗[R] N)
    (LieModuleHom.id : (M ⊗[R] N) →ₗ⁅R, L⁆ (M ⊗[R] N)) (χ x) (ψ x) x
  have hmem : m ⊗ₜ[R] n ∈ (toEnd R L (M ⊗[R] N) x).maxGenEigenspace (χ x + ψ x) := by
    refine key ⟨(⟨m, (Module.End.mem_maxGenEigenspace _ _ _).mpr (hm x)⟩ : _) ⊗ₜ[R]
      (⟨n, (Module.End.mem_maxGenEigenspace _ _ _).mpr (hn x)⟩ : _), ?_⟩
    simp [TensorProduct.mapIncl]
  simpa using (Module.End.mem_maxGenEigenspace _ _ _).mp hmem

variable (M N) in
/-- The submodule of `M ⊗ N` spanned by the pure tensors of a `χ`-weight vector of `M` and a
`ψ`-weight vector of `N` lies in the `(χ + ψ)`-weight space of `M ⊗ N`. This is the submodule form
of `TauCeti.tmul_mem_genWeightSpace_add`. -/
theorem map₂_mk_genWeightSpace_le (χ ψ : L → R) :
    Submodule.map₂ (TensorProduct.mk R M N) (genWeightSpace M χ).toSubmodule
        (genWeightSpace N ψ).toSubmodule ≤ (genWeightSpace (M ⊗[R] N) (χ + ψ)).toSubmodule :=
  Submodule.map₂_le.mpr fun _ hm _ hn ↦
    (LieSubmodule.mem_toSubmodule _).mpr (tmul_mem_genWeightSpace_add
      ((LieSubmodule.mem_toSubmodule _).mp hm) ((LieSubmodule.mem_toSubmodule _).mp hn))

end CommRing

/-! ### The decomposition over a field -/

section Field

variable {K : Type u} {L : Type v} {M : Type w} {N : Type w₁}
  [Field K] [LieRing L] [LieAlgebra K L] [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [FiniteDimensional K M] [FiniteDimensional K N]
  [IsTriangularizable K L M] [IsTriangularizable K L N]

variable (K L M N)

/-- **The pure tensors of weight vectors span the tensor product.** The weight spaces of `M` and of
`N` exhaust them, and `Submodule.map₂` distributes over suprema in both arguments. -/
theorem iSup_map₂_mk_genWeightSpace_eq_top :
    ⨆ (χ : L → K) (ψ : L → K), Submodule.map₂ (TensorProduct.mk K M N)
        (genWeightSpace M χ).toSubmodule (genWeightSpace N ψ).toSubmodule = ⊤ := by
  have hM : ⨆ χ : L → K, (genWeightSpace M χ).toSubmodule = ⊤ := by
    rw [← LieSubmodule.iSup_toSubmodule, iSup_genWeightSpace_eq_top K L M,
      LieSubmodule.top_toSubmodule]
  have hN : ⨆ ψ : L → K, (genWeightSpace N ψ).toSubmodule = ⊤ := by
    rw [← LieSubmodule.iSup_toSubmodule, iSup_genWeightSpace_eq_top K L N,
      LieSubmodule.top_toSubmodule]
  simp_rw [← Submodule.map₂_iSup_right]
  rw [← Submodule.map₂_iSup_left, hM, hN, TensorProduct.map₂_mk_top_top_eq_top]

/-- **The weight spaces of a tensor product exhaust it.** Every element of `M ⊗ N` is a sum of
generalized weight vectors; this needs no algebraic closure, only that `M` and `N` are themselves
triangularizable. -/
theorem iSup_genWeightSpace_tensorProduct_eq_top :
    ⨆ χ : L → K, genWeightSpace (M ⊗[K] N) χ = ⊤ := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.iSup_toSubmodule, LieSubmodule.top_toSubmodule,
    ← top_le_iff, ← iSup_map₂_mk_genWeightSpace_eq_top K L M N]
  exact iSup₂_le fun χ ψ ↦ (map₂_mk_genWeightSpace_le M N χ ψ).trans
    (le_iSup (fun ξ : L → K ↦ (genWeightSpace (M ⊗[K] N) ξ).toSubmodule) (χ + ψ))

/-- **A tensor product of triangularizable modules is triangularizable.** In finite dimensions over
a field, if every element of `L` acts on `M` and on `N` with its generalized eigenspaces spanning,
then the same holds on `M ⊗ N`. -/
instance isTriangularizable_tensorProduct : IsTriangularizable K L (M ⊗[K] N) := by
  refine ⟨fun x ↦ top_le_iff.mp ?_⟩
  calc (⊤ : Submodule K (M ⊗[K] N))
      = ⨆ χ : L → K, (genWeightSpace (M ⊗[K] N) χ).toSubmodule := by
        rw [← LieSubmodule.iSup_toSubmodule, iSup_genWeightSpace_tensorProduct_eq_top K L M N,
          LieSubmodule.top_toSubmodule]
    _ ≤ ⨆ φ : K, (toEnd K L (M ⊗[K] N) x).maxGenEigenspace φ :=
        iSup_le fun χ ↦ fun t ht ↦
          le_iSup (fun φ : K ↦ (toEnd K L (M ⊗[K] N) x).maxGenEigenspace φ) (χ x)
            ((Module.End.mem_maxGenEigenspace _ _ _).mpr
              ((mem_genWeightSpace _ _ _).mp ((LieSubmodule.mem_toSubmodule _).mp ht) x))

variable {K L M N}

/-- **The weight-space decomposition of a tensor product.** The generalized `χ`-weight space of
`M ⊗ N` is the supremum, over the pairs of weights `(μ, ν)` with `μ + ν = χ`, of the submodules
spanned by the pure tensors `m ⊗ₜ n` with `m` of weight `μ` and `n` of weight `ν`.

One inclusion is `TauCeti.map₂_mk_genWeightSpace_le`. For the other, the family on the right has
the same supremum as the family of weight spaces of `M ⊗ N`, namely `⊤`, and the latter is
independent, so the two families agree term by term. -/
theorem genWeightSpace_tensorProduct_eq_iSup (χ : L → K) :
    (genWeightSpace (M ⊗[K] N) χ).toSubmodule
      = ⨆ (μ : L → K) (ν : L → K) (_ : μ + ν = χ), Submodule.map₂ (TensorProduct.mk K M N)
          (genWeightSpace M μ).toSubmodule (genWeightSpace N ν).toSubmodule := by
  let p : (L → K) → Submodule K (M ⊗[K] N) := fun ξ ↦
    ⨆ (μ : L → K) (ν : L → K) (_ : μ + ν = ξ), Submodule.map₂ (TensorProduct.mk K M N)
      (genWeightSpace M μ).toSubmodule (genWeightSpace N ν).toSubmodule
  let q : (L → K) → Submodule K (M ⊗[K] N) := fun ξ ↦ (genWeightSpace (M ⊗[K] N) ξ).toSubmodule
  have hle : ∀ ξ, p ξ ≤ q ξ := fun ξ ↦
    iSup₂_le fun μ ν ↦ iSup_le fun hμν ↦ hμν ▸ map₂_mk_genWeightSpace_le M N μ ν
  have hptop : ⨆ ξ, p ξ = ⊤ := by
    rw [← iSup_map₂_mk_genWeightSpace_eq_top K L M N]
    change (⨆ (ξ : L → K) (μ : L → K) (ν : L → K) (_ : μ + ν = ξ), _) = _
    rw [iSup_comm]
    refine iSup_congr fun μ ↦ ?_
    rw [iSup_comm]
    exact iSup_congr fun ν ↦ iSup_iSup_eq_right
  have hindep : iSupIndep q := by
    have := iSupIndep_genWeightSpace K L (M ⊗[K] N)
    rwa [← LieSubmodule.iSupIndep_toSubmodule] at this
  have hsup : ⨆ ξ, p ξ = ⨆ ξ, q ξ :=
    hptop.trans (le_antisymm le_top (hptop ▸ iSup_mono hle)).symm
  exact (eq_of_le_of_iSup_eq_iSup hindep hle hsup χ).symm

/-- **Every weight of a tensor product is a sum of weights.** If the `χ`-weight space of `M ⊗ N` is
nonzero, then `χ = μ + ν` for a weight `μ` of `M` and a weight `ν` of `N`. -/
theorem exists_add_eq_of_genWeightSpace_tensorProduct_ne_bot {χ : L → K}
    (h : genWeightSpace (M ⊗[K] N) χ ≠ ⊥) :
    ∃ μ ν : L → K, μ + ν = χ ∧ genWeightSpace M μ ≠ ⊥ ∧ genWeightSpace N ν ≠ ⊥ := by
  by_contra hc
  push Not at hc
  refine h ?_
  rw [← LieSubmodule.toSubmodule_eq_bot, genWeightSpace_tensorProduct_eq_iSup]
  simp only [iSup_eq_bot]
  intro μ ν hμν
  by_cases hμ : genWeightSpace M μ = ⊥
  · rw [hμ]
    simp
  · rw [hc μ ν hμν hμ]
    simp

/-- **Every weight of a tensor product is a sum of weights**, phrased with `LieModule.Weight`. -/
theorem exists_weight_add_eq (χ : Weight K L (M ⊗[K] N)) :
    ∃ (μ : Weight K L M) (ν : Weight K L N), (μ : L → K) + (ν : L → K) = (χ : L → K) := by
  obtain ⟨μ, ν, hμν, hμ, hν⟩ :=
    exists_add_eq_of_genWeightSpace_tensorProduct_ne_bot χ.genWeightSpace_ne_bot
  exact ⟨⟨μ, hμ⟩, ⟨ν, hν⟩, hμν⟩

end Field

end TauCeti
