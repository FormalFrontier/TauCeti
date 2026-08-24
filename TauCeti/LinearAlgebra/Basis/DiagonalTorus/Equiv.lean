/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic

/-!
# Symmetries of weighted-basis tori

A permutation of the coordinates of a split torus acts contragrediently on its points. If a
linear automorphism permutes a weighted basis and the corresponding weights through that
coordinate permutation, then it intertwines the original torus action with the reindexed one.
Equivalently, it normalizes the represented split torus.

This is the representation-theoretic toral half of a pinned diagram symmetry: the same symmetry
must also permute the root subgroups, while the theorems here describe its action on the
represented weight torus. Nothing constrains the weight function, so that torus need not act
faithfully and need not be maximal; in the intended Chevalley-group application the weights are
those of a pinned lattice basis, and it is.

## Main declarations

* `TauCeti.torusCharacter_arrowCongr`: evaluation after reindexing a point.
* `TauCeti.basisWeightTorus_intertwine_of_map_basis`: a weighted-basis symmetry intertwines the
  represented torus actions.
* `TauCeti.basisWeightTorus_conj_of_map_basis`: the corresponding conjugation formula.
* `TauCeti.map_basisWeightTorus_range_conj_of_map_basis`: such a symmetry normalizes the
  represented torus.
-/

public section

namespace TauCeti

universe u v w

variable {ι : Type u} {κ : Type v} {R : Type w} {M : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M]

/-! ## Reindexing points and characters -/

variable [Fintype κ]

/-- Evaluating a character at a reindexed point is the same as permuting the character by the
original coordinate permutation. -/
theorem torusCharacter_arrowCongr (σ : Equiv.Perm κ) (s : κ → Rˣ) (μ : κ → ℤ) :
    torusCharacter (MulEquiv.arrowCongr σ (MulEquiv.refl Rˣ) s) μ =
      torusCharacter s (μ ∘ σ) := by
  rw [torusCharacter_def, torusCharacter_def]
  exact (Fintype.prod_equiv σ (fun j => s j ^ μ (σ j))
    (fun j => s (σ.symm j) ^ μ j) fun j => by simp).symm

/-! ## Normalizing a represented weight torus -/

/-- A linear automorphism that permutes a weighted basis compatibly with a permutation of the
torus coordinates intertwines the original weight-torus action with the reindexed action.

The hypothesis says that the weight of the image basis vector, evaluated at the permuted
coordinate, is the original weight. The basis-index map need not be supplied as an equivalence:
bijectivity already follows whenever such a map is induced by an automorphism and a basis. -/
theorem basisWeightTorus_intertwine_of_map_basis (b : Module.Basis ι R M) (wt : ι → κ → ℤ)
    (τ : ι → ι) (σ : Equiv.Perm κ) (θ : M ≃ₗ[R] M)
    (hθ : ∀ i, θ (b i) = b (τ i))
    (hwt : ∀ i j, wt (τ i) (σ j) = wt i j) (s : κ → Rˣ) :
    (basisWeightTorus b wt s).trans θ =
      θ.trans (basisWeightTorus b wt (MulEquiv.arrowCongr σ (MulEquiv.refl Rˣ) s)) := by
  refine LinearEquiv.toLinearMap_injective (Module.Basis.ext b fun i => ?_)
  have hcomp : wt (τ i) ∘ σ = wt i := funext fun j => hwt i j
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, basisWeightTorus_basis, map_smul, hθ,
    torusCharacter_arrowCongr, hcomp]

/-- Conjugating a weighted-basis torus point by a compatible basis symmetry reindexes that torus
point. This is the normalizer form of `basisWeightTorus_intertwine_of_map_basis`. -/
theorem basisWeightTorus_conj_of_map_basis (b : Module.Basis ι R M) (wt : ι → κ → ℤ)
    (τ : ι → ι) (σ : Equiv.Perm κ) (θ : M ≃ₗ[R] M)
    (hθ : ∀ i, θ (b i) = b (τ i))
    (hwt : ∀ i j, wt (τ i) (σ j) = wt i j) (s : κ → Rˣ) :
    θ * basisWeightTorus b wt s * θ⁻¹ =
      basisWeightTorus b wt (MulEquiv.arrowCongr σ (MulEquiv.refl Rˣ) s) := by
  have hintertwine := basisWeightTorus_intertwine_of_map_basis b wt τ σ θ hθ hwt s
  apply LinearEquiv.ext
  intro x
  simpa only [LinearEquiv.mul_apply, LinearEquiv.trans_apply, LinearEquiv.coe_inv,
    LinearEquiv.apply_symm_apply]
    using congrArg (fun f : M ≃ₗ[R] M => f (θ.symm x)) hintertwine

/-- **A compatible basis symmetry normalizes the represented weight torus.** Conjugation by `θ`
carries each torus point to the point reindexed through `σ`, so it maps the range of the
torus homomorphism onto itself. -/
theorem map_basisWeightTorus_range_conj_of_map_basis (b : Module.Basis ι R M) (wt : ι → κ → ℤ)
    (τ : ι → ι) (σ : Equiv.Perm κ) (θ : M ≃ₗ[R] M)
    (hθ : ∀ i, θ (b i) = b (τ i))
    (hwt : ∀ i j, wt (τ i) (σ j) = wt i j) :
    Subgroup.map (MulAut.conj θ).toMonoidHom (basisWeightTorus b wt).range =
      (basisWeightTorus b wt).range := by
  have hcomp : (MulAut.conj θ).toMonoidHom.comp (basisWeightTorus b wt) =
      (basisWeightTorus b wt).comp
        (MulEquiv.arrowCongr σ (MulEquiv.refl Rˣ)).toMonoidHom :=
    MonoidHom.ext fun s => basisWeightTorus_conj_of_map_basis b wt τ σ θ hθ hwt s
  rw [MonoidHom.map_range, hcomp, MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _ (MulEquiv.surjective _), ← MonoidHom.range_eq_map]

end TauCeti
