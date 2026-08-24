/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Equiv
public import TauCeti.LinearAlgebra.GeneralLinearGroup.InvariantRestrict

/-!
# Numbered symmetries of a Kostant torus

Suppose an additive automorphism of a rational representation preserves a Kostant lattice and
permutes a chosen integral weight basis. If the induced permutation of the weights is compatible
with a permutation of the torus coordinates, then the scalar extension of that automorphism
normalizes the Kostant torus over every commutative ring.

The result is uniform in the value ring and does not require the basis vectors to have been
identified as Cartan eigenvectors: all representation-theoretic information needed by the proof
is recorded in the weight-compatibility equation. In the pinned Geck construction, that equation
is supplied by the compatibility of the pinned lattice basis with a diagram symmetry.

Together with the corresponding permutation formula for numbered root subgroups, this supplies
the two carrier calculations needed to extend a diagram symmetry to the root-and-torus-generated
group.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.baseChangeInvariantRestrictUnit_mul_kostantTorusPoints`:
  the scalar-extended symmetry intertwines a torus point with its reindexing.
* `TauCeti.UniversalEnvelopingAlgebra.baseChangeInvariantRestrictUnit_conj_kostantTorusPoints`:
  the corresponding conjugation formula.
* `map_kostantTorusSubgroup_conj_baseChangeInvariantRestrictUnit`:
  the scalar-extended symmetry normalizes the entire Kostant torus subgroup.
-/

public section

open TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {V : Type u} [AddCommGroup V]
variable (M : AddSubgroup V)
variable {η : Type v} {κ : Type*} [Fintype κ]
variable (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

section Pointwise

variable {A : Type w} [CommRing A] [Algebra ℤ A]

/-- The restriction of a lattice-preserving symmetry that permutes the chosen basis continues to
permute that basis after scalar extension. -/
private theorem baseChange_invariantRestrict_map_baseChange_basis
    (θ : V ≃+ V) (hθM : ∀ v, θ v ∈ M ↔ v ∈ M) (τ : η → η)
    (hθb : ∀ i, θ ((b i : M) : V) = ((b (τ i) : M) : V)) (i : η) :
    (AddEquiv.invariantRestrict θ M hθM).baseChange ℤ A M M ((b.baseChange A) i) =
      (b.baseChange A) (τ i) := by
  rw [Module.Basis.baseChange_apply, LinearEquiv.baseChange_tmul,
    Module.Basis.baseChange_apply]
  congr 1
  apply Subtype.ext
  rw [AddEquiv.coe_invariantRestrict_apply]
  exact hθb i

/-- **A numbered symmetry intertwines the Kostant torus.** If the symmetry sends the basis vector
indexed by `i` to the one indexed by `τ i`, and their weights satisfy
`wt (τ i) (σ j) = wt i j`, then the scalar-extended symmetry carries the torus point `s` past
itself as the point obtained by contragredient reindexing through `σ`. -/
theorem baseChangeInvariantRestrictUnit_mul_kostantTorusPoints
    (θ : V ≃+ V) (hθM : ∀ v, θ v ∈ M ↔ v ∈ M) (τ : η → η) (σ : Equiv.Perm κ)
    (hθb : ∀ i, θ ((b i : M) : V) = ((b (τ i) : M) : V))
    (hwt : ∀ i j, wt (τ i) (σ j) = wt i j) (s : κ → Aˣ) :
    AddEquiv.baseChangeInvariantRestrictUnit (R := A) θ M hθM *
        kostantTorusPoints M b wt A s =
      kostantTorusPoints M b wt A (MulEquiv.arrowCongr σ (MulEquiv.refl Aˣ) s) *
        AddEquiv.baseChangeInvariantRestrictUnit (R := A) θ M hθM := by
  apply Units.ext
  apply LinearMap.ext
  intro z
  simp only [Units.val_mul, Module.End.mul_apply]
  rw [AddEquiv.val_baseChangeInvariantRestrictUnit_apply,
    AddEquiv.val_baseChangeInvariantRestrictUnit_apply, kostantTorusPoints_apply,
    kostantTorusPoints_apply]
  have hintertwine := basisWeightTorus_intertwine_of_map_basis (b.baseChange A) wt τ σ
    ((AddEquiv.invariantRestrict θ M hθM).baseChange ℤ A M M)
    (baseChange_invariantRestrict_map_baseChange_basis M b θ hθM τ hθb) hwt s
  exact congrArg (fun f : (A ⊗[ℤ] M) ≃ₗ[A] (A ⊗[ℤ] M) => f z) hintertwine

/-- **A numbered symmetry conjugates each Kostant torus point by reindexing its coordinates.** -/
theorem baseChangeInvariantRestrictUnit_conj_kostantTorusPoints
    (θ : V ≃+ V) (hθM : ∀ v, θ v ∈ M ↔ v ∈ M) (τ : η → η) (σ : Equiv.Perm κ)
    (hθb : ∀ i, θ ((b i : M) : V) = ((b (τ i) : M) : V))
    (hwt : ∀ i j, wt (τ i) (σ j) = wt i j) (s : κ → Aˣ) :
    AddEquiv.baseChangeInvariantRestrictUnit (R := A) θ M hθM *
          kostantTorusPoints M b wt A s *
        (AddEquiv.baseChangeInvariantRestrictUnit (R := A) θ M hθM)⁻¹ =
      kostantTorusPoints M b wt A (MulEquiv.arrowCongr σ (MulEquiv.refl Aˣ) s) := by
  rw [baseChangeInvariantRestrictUnit_mul_kostantTorusPoints M b wt θ hθM τ σ hθb hwt s,
    mul_assoc, mul_inv_cancel, mul_one]

end Pointwise

section Subgroup

variable (A : Type w) [CommRing A] [Algebra ℤ A]

/-- **A numbered symmetry normalizes the Kostant torus subgroup.** Conjugation by the
scalar-extended lattice symmetry permutes all torus points through the coordinate permutation
`σ`, hence maps the range of the torus-points homomorphism onto itself. -/
theorem map_kostantTorusSubgroup_conj_baseChangeInvariantRestrictUnit
    (θ : V ≃+ V) (hθM : ∀ v, θ v ∈ M ↔ v ∈ M) (τ : η → η) (σ : Equiv.Perm κ)
    (hθb : ∀ i, θ ((b i : M) : V) = ((b (τ i) : M) : V))
    (hwt : ∀ i j, wt (τ i) (σ j) = wt i j) :
    Subgroup.map
        (MulAut.conj (AddEquiv.baseChangeInvariantRestrictUnit (R := A) θ M hθM)).toMonoidHom
        (kostantTorusSubgroup M b wt A) =
      kostantTorusSubgroup M b wt A := by
  set Φ := LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M) with hΦ
  set U := AddEquiv.baseChangeInvariantRestrictUnit (R := A) θ M hθM with hU
  -- The torus points are the generic weight-torus automorphisms read in the general linear group.
  have hpoints : Φ.symm.toMonoidHom.comp (basisWeightTorus (b.baseChange A) wt) =
      kostantTorusPoints M b wt A :=
    MonoidHom.ext fun s =>
      Φ.symm_apply_eq.mpr (kostantTorusPoints_toLinearEquiv M b wt s).symm
  -- Conjugation by `U` is conjugation by the underlying automorphism, read through `Φ`.
  have hconj : (MulAut.conj U).toMonoidHom.comp Φ.symm.toMonoidHom =
      Φ.symm.toMonoidHom.comp (MulAut.conj (Φ U)).toMonoidHom :=
    MonoidHom.ext fun f => by simp [MulAut.conj_apply]
  -- That underlying automorphism permutes the base-changed basis, as the generic result needs.
  have hbasis : ∀ i, Φ U ((b.baseChange A) i) = (b.baseChange A) (τ i) := fun i => by
    rw [hΦ, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, hU,
      AddEquiv.val_baseChangeInvariantRestrictUnit_apply]
    exact baseChange_invariantRestrict_map_baseChange_basis M b θ hθM τ hθb i
  rw [kostantTorusSubgroup_eq_range, ← hpoints, ← MonoidHom.map_range, Subgroup.map_map, hconj,
    ← Subgroup.map_map,
    map_basisWeightTorus_range_conj_of_map_basis (b.baseChange A) wt τ σ (Φ U) hbasis hwt]

end Subgroup

end TauCeti.UniversalEnvelopingAlgebra
