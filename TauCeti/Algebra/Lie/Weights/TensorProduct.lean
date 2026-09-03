/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.Algebra.Lie.Weights.Linear
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Weight spaces of a tensor product of Lie modules

Let `L` be a nilpotent Lie algebra acting on two modules `M` and `N`. Then `L` acts on `M ⊗ N`, and
this file computes the generalized weight spaces of that action: the `χ`-weight space of `M ⊗ N` is
spanned by the pure tensors `m ⊗ₜ n` with `m` of weight `μ`, `n` of weight `ν` and `μ + ν = χ`.

Two facts meet. Mathlib's `LieModule.weight_vector_multiplication` already says that a pure tensor
of a generalized eigenvector of eigenvalue `φ` and one of eigenvalue `ψ` is a generalized
eigenvector of eigenvalue `φ + ψ`, so the *inclusion* `Mμ ⊗ Nν ≤ (M ⊗ N)_{μ+ν}` needs no hypothesis
beyond nilpotency of `L`, and the tensor product of two triangularizable modules is triangularizable
over any commutative ring. The reverse inclusion is not a computation but a counting argument: over
a field, in finite dimensions and with `M` and `N` triangularizable, the pure tensors of weight
vectors already span `M ⊗ N`, so the coarse family indexed by `χ` refines the independent family of
weight spaces of `M ⊗ N` and must agree with it termwise
(`iSupIndep.le_iff_eq_of_iSup_eq_top`).

## Main results

* `TauCeti.tmul_mem_maxGenEigenspace_add`: **generalized eigenvalues add on pure tensors**, the
  elementwise form of `LieModule.weight_vector_multiplication`.
* `TauCeti.isTriangularizable_tensorProduct`: a tensor product of triangularizable modules is
  triangularizable, over any commutative ring and with no finiteness assumption.
* `TauCeti.tmul_mem_genWeightSpace_add`: **weights add on pure tensors.** If `m` has weight `μ` and
  `n` has weight `ν`, then `m ⊗ₜ n` has weight `μ + ν`, and
  `TauCeti.map₂_mk_genWeightSpace_le` is the submodule form.
* `TauCeti.iSup_map₂_mk_genWeightSpace_eq_top`: the pure tensors of weight vectors span `M ⊗ N`.
* `TauCeti.genWeightSpace_tensorProduct_eq_iSup`: **the weight-space decomposition of a tensor
  product.** The `χ`-weight space of `M ⊗ N` is the supremum, over the pairs `(μ, ν)` with
  `μ + ν = χ`, of the submodules spanned by `Mμ ⊗ Nν`.
* `TauCeti.genWeightSpace_tensorProduct_ne_bot` and `TauCeti.exists_weight_add_eq`: **the weights of
  `M ⊗ N` are exactly the sums of a weight of `M` and a weight of `N`.**
* `TauCeti.instLinearWeightsTensorProduct`: tensor products inherit linear weights from their
  finite-dimensional triangularizable factors.

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

section CommRing

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
  [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-! ### Generalized eigenvalues add on pure tensors -/

/-- **Generalized eigenvalues add on pure tensors.** A pure tensor of a generalized eigenvector of
`x` of eigenvalue `φ` in `M` and one of eigenvalue `ψ` in `N` is a generalized eigenvector of `x` of
eigenvalue `φ + ψ` in `M ⊗ N`.

This is the elementwise form of Mathlib's `LieModule.weight_vector_multiplication`, applied to the
identity map of `M ⊗ N`. Neither nilpotency of `L` nor any finiteness is involved. -/
theorem tmul_mem_maxGenEigenspace_add {φ ψ : R} {x : L} {m : M} {n : N}
    (hm : m ∈ (toEnd R L M x).maxGenEigenspace φ)
    (hn : n ∈ (toEnd R L N x).maxGenEigenspace ψ) :
    m ⊗ₜ[R] n ∈ (toEnd R L (M ⊗[R] N) x).maxGenEigenspace (φ + ψ) := by
  refine LieModule.weight_vector_multiplication (R := R) (L := L) M N (M ⊗[R] N)
    (LieModuleHom.id : (M ⊗[R] N) →ₗ⁅R, L⁆ (M ⊗[R] N)) φ ψ x
    ⟨(⟨m, hm⟩ : _) ⊗ₜ[R] (⟨n, hn⟩ : _), ?_⟩
  simp [TensorProduct.mapIncl]

/-- **A tensor product of triangularizable modules is triangularizable.** If every element of `L`
acts on `M` and on `N` with its generalized eigenspaces spanning, then the same holds on `M ⊗ N`:
the pure tensors of generalized eigenvectors span `M ⊗ N`, and they are generalized eigenvectors by
`TauCeti.tmul_mem_maxGenEigenspace_add`. -/
instance isTriangularizable_tensorProduct [IsTriangularizable R L M] [IsTriangularizable R L N] :
    IsTriangularizable R L (M ⊗[R] N) := by
  refine ⟨fun x ↦ top_le_iff.mp ?_⟩
  calc (⊤ : Submodule R (M ⊗[R] N))
      = Submodule.map₂ (TensorProduct.mk R M N) (⨆ φ : R, (toEnd R L M x).maxGenEigenspace φ)
          (⨆ ψ : R, (toEnd R L N x).maxGenEigenspace ψ) := by
        rw [IsTriangularizable.maxGenEigenspace_eq_top (R := R) (M := M) x,
          IsTriangularizable.maxGenEigenspace_eq_top (R := R) (M := N) x,
          TensorProduct.map₂_mk_top_top_eq_top]
    _ ≤ ⨆ θ : R, (toEnd R L (M ⊗[R] N) x).maxGenEigenspace θ := by
        rw [Submodule.map₂_iSup_left]
        refine iSup_le fun φ ↦ ?_
        rw [Submodule.map₂_iSup_right]
        refine iSup_le fun ψ ↦ ?_
        exact (Submodule.map₂_le.mpr fun _ hm _ hn ↦ tmul_mem_maxGenEigenspace_add hm hn).trans
          (le_iSup (fun θ : R ↦ (toEnd R L (M ⊗[R] N) x).maxGenEigenspace θ) (φ + ψ))

/-! ### Weights add on pure tensors -/

section IsNilpotent

variable [LieRing.IsNilpotent L]

/-- **Weights add on pure tensors.** A pure tensor of a vector of generalized weight `χ` in `M` and
a vector of generalized weight `ψ` in `N` has generalized weight `χ + ψ` in `M ⊗ N`.

This is `TauCeti.tmul_mem_maxGenEigenspace_add`, applied one element `x : L` at a time. No
finiteness or triangularizability is involved. -/
theorem tmul_mem_genWeightSpace_add {χ ψ : L → R} {m : M} {n : N}
    (hm : m ∈ genWeightSpace M χ) (hn : n ∈ genWeightSpace N ψ) :
    m ⊗ₜ[R] n ∈ genWeightSpace (M ⊗[R] N) (χ + ψ) := by
  rw [mem_genWeightSpace] at hm hn ⊢
  intro x
  have := tmul_mem_maxGenEigenspace_add (R := R) (x := x) (m := m) (n := n)
    ((Module.End.mem_maxGenEigenspace _ _ _).mpr (hm x))
    ((Module.End.mem_maxGenEigenspace _ _ _).mpr (hn x))
  simpa using (Module.End.mem_maxGenEigenspace _ _ _).mp this

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

end IsNilpotent

end CommRing

/-! ### The weights of a tensor product over a field -/

section Field

variable {K : Type u} {L : Type v} {M : Type w} {N : Type w₁}
  [Field K] [LieRing L] [LieAlgebra K L] [LieRing.IsNilpotent L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

/-- **A sum of weights is a weight of the tensor product.** If the `μ`-weight space of `M` and the
`ν`-weight space of `N` are both nonzero, then so is the `(μ + ν)`-weight space of `M ⊗ N`: a pure
tensor of two nonzero vectors is nonzero over a field. This is the converse of
`TauCeti.exists_weight_add_eq`. -/
theorem genWeightSpace_tensorProduct_ne_bot {μ ν : L → K} (hμ : genWeightSpace M μ ≠ ⊥)
    (hν : genWeightSpace N ν ≠ ⊥) : genWeightSpace (M ⊗[K] N) (μ + ν) ≠ ⊥ := by
  rw [ne_eq, ← LieSubmodule.toSubmodule_eq_bot] at hμ hν ⊢
  obtain ⟨m, hm, hm0⟩ := (Submodule.ne_bot_iff _).mp hμ
  obtain ⟨n, hn, hn0⟩ := (Submodule.ne_bot_iff _).mp hν
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero K hm0
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero K hn0
  refine (Submodule.ne_bot_iff _).mpr ⟨m ⊗ₜ[K] n, (LieSubmodule.mem_toSubmodule _).mpr
    (tmul_mem_genWeightSpace_add ((LieSubmodule.mem_toSubmodule _).mp hm)
      ((LieSubmodule.mem_toSubmodule _).mp hn)), fun h ↦ mul_ne_zero hf hg ?_⟩
  simpa using congrArg (TensorProduct.lift (LinearMap.smulRight f g)) h

variable [FiniteDimensional K M] [FiniteDimensional K N]
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

variable {K L M N}

/-- **The weight-space decomposition of a tensor product.** The generalized `χ`-weight space of
`M ⊗ N` is the supremum, over the pairs of weights `(μ, ν)` with `μ + ν = χ`, of the submodules
spanned by the pure tensors `m ⊗ₜ n` with `m` of weight `μ` and `n` of weight `ν`.

One inclusion is `TauCeti.map₂_mk_genWeightSpace_le`. For the other, the family on the right has
supremum `⊤`, and it lies inside the independent family of weight spaces of `M ⊗ N`, so
`iSupIndep.le_iff_eq_of_iSup_eq_top` makes the two families agree term by term. -/
theorem genWeightSpace_tensorProduct_eq_iSup (χ : L → K) :
    (genWeightSpace (M ⊗[K] N) χ).toSubmodule
      = ⨆ (μ : L → K) (ν : L → K) (_ : μ + ν = χ), Submodule.map₂ (TensorProduct.mk K M N)
          (genWeightSpace M μ).toSubmodule (genWeightSpace N ν).toSubmodule := by
  let p : (L → K) → Submodule K (M ⊗[K] N) := fun ξ ↦
    ⨆ (μ : L → K) (ν : L → K) (_ : μ + ν = ξ), Submodule.map₂ (TensorProduct.mk K M N)
      (genWeightSpace M μ).toSubmodule (genWeightSpace N ν).toSubmodule
  let q : (L → K) → Submodule K (M ⊗[K] N) := fun ξ ↦ (genWeightSpace (M ⊗[K] N) ξ).toSubmodule
  have hle : p ≤ q := fun ξ ↦
    iSup₂_le fun μ ν ↦ iSup_le fun hμν ↦ hμν ▸ map₂_mk_genWeightSpace_le M N μ ν
  have hptop : ⨆ ξ, p ξ = ⊤ := by
    rw [← iSup_map₂_mk_genWeightSpace_eq_top K L M N]
    simp only [p]
    rw [iSup_comm]
    refine iSup_congr fun μ ↦ ?_
    rw [iSup_comm]
    exact iSup_congr fun ν ↦ iSup_iSup_eq_right
  have hindep : iSupIndep q := by
    have := iSupIndep_genWeightSpace K L (M ⊗[K] N)
    rwa [← LieSubmodule.iSupIndep_toSubmodule] at this
  exact (congr_fun ((hindep.le_iff_eq_of_iSup_eq_top hptop).mp hle) χ).symm

/-- **Every weight of a tensor product is a sum of weights.** If `χ` is a weight of `M ⊗ N`, then
`χ = μ + ν` for a weight `μ` of `M` and a weight `ν` of `N`. This is the converse of
`TauCeti.genWeightSpace_tensorProduct_ne_bot`.

If no such pair existed then every term of the decomposition
`TauCeti.genWeightSpace_tensorProduct_eq_iSup` of the `χ`-weight space would have a zero factor, so
that weight space would be zero. -/
theorem exists_weight_add_eq (χ : Weight K L (M ⊗[K] N)) :
    ∃ (μ : Weight K L M) (ν : Weight K L N), (μ : L → K) + (ν : L → K) = (χ : L → K) := by
  by_contra hc
  push Not at hc
  have hbot : genWeightSpace (M ⊗[K] N) (χ : L → K) = ⊥ := by
    rw [← LieSubmodule.toSubmodule_eq_bot, genWeightSpace_tensorProduct_eq_iSup]
    simp only [iSup_eq_bot]
    intro μ ν hμν
    by_cases hμ : genWeightSpace M μ = ⊥
    · rw [hμ]
      simp
    by_cases hν : genWeightSpace N ν = ⊥
    · rw [hν]
      simp
    exact absurd hμν (hc ⟨μ, hμ⟩ ⟨ν, hν⟩)
  exact absurd hbot χ.genWeightSpace_ne_bot

/-- A tensor product of finite-dimensional triangularizable modules with linear weights again has
linear weights. Every weight of the tensor product is a sum of weights of the two factors. -/
instance instLinearWeightsTensorProduct [LinearWeights K L M] [LinearWeights K L N] :
    LinearWeights K L (M ⊗[K] N) where
  map_add χ hχ x y := by
    obtain ⟨μ, ν, hμν⟩ := exists_weight_add_eq (⟨χ, hχ⟩ : Weight K L (M ⊗[K] N))
    have hχ_eq : χ = (μ : L → K) + (ν : L → K) := by
      simpa using hμν.symm
    rw [hχ_eq]
    simp only [Pi.add_apply, map_add]
    ac_rfl
  map_smul χ hχ t x := by
    obtain ⟨μ, ν, hμν⟩ := exists_weight_add_eq (⟨χ, hχ⟩ : Weight K L (M ⊗[K] N))
    have hχ_eq : χ = (μ : L → K) + (ν : L → K) := by
      simpa using hμν.symm
    rw [hχ_eq]
    simp only [Pi.add_apply, map_smul, smul_eq_mul, mul_add]
  map_lie χ hχ x y := by
    obtain ⟨μ, ν, hμν⟩ := exists_weight_add_eq (⟨χ, hχ⟩ : Weight K L (M ⊗[K] N))
    have hχ_eq : χ = (μ : L → K) + (ν : L → K) := by
      simpa using hμν.symm
    rw [hχ_eq]
    simp only [Pi.add_apply, Weight.apply_lie, add_zero]

end Field

end TauCeti
