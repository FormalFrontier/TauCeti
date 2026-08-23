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
must also permute the root subgroups, while the theorem here handles its action on the maximal
torus.

## Main declarations

* `TauCeti.reindexTorusPoint`: contragredient reindexing of split-torus points.
* `TauCeti.torusCharacter_reindexTorusPoint`: evaluation after reindexing a point.
* `TauCeti.basisWeightTorus_intertwine_of_map_basis`: a weighted-basis symmetry intertwines the
  represented torus actions.
* `TauCeti.basisWeightTorus_conj_of_map_basis`: the corresponding conjugation formula.
-/

public section

namespace TauCeti

universe u v w

variable {ι : Type u} {κ : Type v} {R : Type w} {M : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M]

/-! ## Reindexing points and characters -/

/-- The contragredient action of a coordinate permutation on the points of a split torus.
The coordinate at `j` after reindexing is the old coordinate at `σ.symm j`. -/
def reindexTorusPoint (σ : Equiv.Perm κ) : (κ → Rˣ) ≃* (κ → Rˣ) where
  toFun s j := s (σ.symm j)
  invFun s j := s (σ j)
  left_inv s := funext fun j => by simp
  right_inv s := funext fun j => by simp
  map_mul' _ _ := rfl

private theorem reindexTorusPoint_apply_def (σ : Equiv.Perm κ) (s : κ → Rˣ) (j : κ) :
    reindexTorusPoint (R := R) σ s j = s (σ.symm j) :=
  rfl

private theorem reindexTorusPoint_symm_apply_def (σ : Equiv.Perm κ) (s : κ → Rˣ) (j : κ) :
    (reindexTorusPoint (R := R) σ).symm s j = s (σ j) :=
  rfl

/-- Reindexing a torus point reads the coordinate through the inverse permutation. -/
@[simp]
theorem reindexTorusPoint_apply (σ : Equiv.Perm κ) (s : κ → Rˣ) (j : κ) :
    reindexTorusPoint (R := R) σ s j = s (σ.symm j) :=
  reindexTorusPoint_apply_def σ s j

/-- The inverse reindexing reads the coordinate through the original permutation. -/
@[simp]
theorem reindexTorusPoint_symm_apply (σ : Equiv.Perm κ) (s : κ → Rˣ) (j : κ) :
    (reindexTorusPoint (R := R) σ).symm s j = s (σ j) :=
  reindexTorusPoint_symm_apply_def σ s j

variable [Fintype κ]

/-- Evaluating a character at a reindexed point is the same as permuting the character by the
original coordinate permutation. -/
theorem torusCharacter_reindexTorusPoint (σ : Equiv.Perm κ) (s : κ → Rˣ) (μ : κ → ℤ) :
    torusCharacter (reindexTorusPoint σ s) μ = torusCharacter s (μ ∘ σ) := by
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
      θ.trans (basisWeightTorus b wt (reindexTorusPoint σ s)) := by
  apply LinearEquiv.toLinearMap_injective
  apply Module.Basis.ext b
  intro i
  change θ (basisWeightTorus b wt s (b i)) =
    basisWeightTorus b wt (reindexTorusPoint σ s) (θ (b i))
  rw [basisWeightTorus_basis, map_smul, hθ, basisWeightTorus_basis]
  rw [torusCharacter_reindexTorusPoint]
  rw [show wt (τ i) ∘ σ = wt i by funext j; exact hwt i j]

/-- Conjugating a weighted-basis torus point by a compatible basis symmetry reindexes that torus
point. This is the normalizer form of `basisWeightTorus_intertwine_of_map_basis`. -/
theorem basisWeightTorus_conj_of_map_basis (b : Module.Basis ι R M) (wt : ι → κ → ℤ)
    (τ : ι → ι) (σ : Equiv.Perm κ) (θ : M ≃ₗ[R] M)
    (hθ : ∀ i, θ (b i) = b (τ i))
    (hwt : ∀ i j, wt (τ i) (σ j) = wt i j) (s : κ → Rˣ) :
    θ * basisWeightTorus b wt s * θ⁻¹ =
      basisWeightTorus b wt (reindexTorusPoint σ s) := by
  have hintertwine := basisWeightTorus_intertwine_of_map_basis b wt τ σ θ hθ hwt s
  apply LinearEquiv.ext
  intro x
  simpa only [LinearEquiv.mul_apply, LinearEquiv.trans_apply, LinearEquiv.coe_inv,
    LinearEquiv.apply_symm_apply]
    using congrArg (fun f : M ≃ₗ[R] M => f (θ.symm x)) hintertwine

end TauCeti
