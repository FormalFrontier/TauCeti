/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.LinearAlgebra.GeneralLinearGroup.InvariantRestrict

/-!
# Lattice symmetries of a Kostant torus

Suppose an additive automorphism of an abelian group preserves a subgroup with a chosen integral
basis and acts monomially on that basis. If the induced basis-index map is compatible with a
permutation of the torus coordinates through the supplied weight function, then the scalar
extension of that automorphism normalizes the corresponding Kostant torus over every commutative
ring.

The result is uniform in the value ring and does not require the basis vectors to have been
identified as Cartan eigenvectors: all representation-theoretic information needed by the proof
is recorded in the weight-compatibility equation. The intended application is a rational
representation with a Kostant lattice; there, a numbered diagram symmetry supplies the monomial
basis action and its compatibility with the weights of the pinned Geck construction.

Together with the corresponding permutation formula for numbered root subgroups, this supplies
the two carrier calculations needed to extend a diagram symmetry to the root-and-torus-generated
group.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.baseChangeInvariantRestrictUnit_mul_kostantTorusPoints`:
  the scalar-extended symmetry intertwines a torus point with its reindexing.
* `TauCeti.UniversalEnvelopingAlgebra.conj_kostantTorusPoints_of_baseChangeInvariantRestrictUnit`:
  the corresponding conjugation formula.
* `map_kostantTorusSubgroup_conj_baseChangeInvariantRestrictUnit`:
  the scalar-extended symmetry normalizes the entire Kostant torus subgroup.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15.
-/

public section

open TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {V : Type u} [AddCommGroup V]
variable (M : AddSubgroup V)
variable {η : Type v} {κ : Type*} [Fintype κ]
variable (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)

-- Match tensor products to the module structure carried by the explicit `ℤ`-algebra.
attribute [local instance high] Algebra.toModule

section Pointwise

variable {A : Type w} [CommRing A] [Algebra ℤ A]

/-- **A monomial lattice symmetry intertwines the Kostant torus.** If the symmetry sends the basis
vector indexed by `i` to a scalar multiple of the one indexed by `τ i`, and their weights satisfy
`wt (τ i) (σ j) = wt i j`, then the scalar-extended symmetry carries the torus point `s` past
itself as the point obtained by contragredient reindexing through `σ`. In the intended pinned
application this data comes from a numbered diagram symmetry. -/
theorem baseChangeInvariantRestrictUnit_mul_kostantTorusPoints
    (θ : V ≃+ V) (hθM : ∀ v, θ v ∈ M ↔ v ∈ M) (τ : η → η) (σ : Equiv.Perm κ)
    (c : η → ℤ)
    (hθb : ∀ i, AddEquiv.invariantRestrict θ M hθM (b i) = c i • b (τ i))
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
  let Θ : (A ⊗[ℤ] M) ≃ₗ[A] (A ⊗[ℤ] M) :=
    (AddEquiv.invariantRestrict θ M hθM).baseChange ℤ A M M
  let cA : η → A := fun i => algebraMap ℤ A (c i)
  have hbase : ∀ i, Θ ((b.baseChange A) i) = cA i • (b.baseChange A) (τ i) :=
    AddEquiv.baseChange_invariantRestrict_map_baseChange_basis M b θ hθM τ c hθb
  have hintertwine :
      Θ * basisWeightTorus (b.baseChange A) wt s =
        basisWeightTorus (b.baseChange A) wt
            (MulEquiv.arrowCongr σ (MulEquiv.refl Aˣ) s) * Θ :=
    basisWeightTorus_intertwine_of_map_basis (b.baseChange A) wt τ σ Θ cA hbase hwt s
  simpa only [LinearEquiv.mul_apply] using
    congrArg (fun f : (A ⊗[ℤ] M) ≃ₗ[A] (A ⊗[ℤ] M) => f z) hintertwine

/-- **A compatible monomial lattice symmetry conjugates each Kostant torus point by reindexing
its coordinates.** In the pinned application the lattice symmetry is induced by a numbered
diagram symmetry. -/
theorem conj_kostantTorusPoints_of_baseChangeInvariantRestrictUnit
    (θ : V ≃+ V) (hθM : ∀ v, θ v ∈ M ↔ v ∈ M) (τ : η → η) (σ : Equiv.Perm κ)
    (c : η → ℤ)
    (hθb : ∀ i, AddEquiv.invariantRestrict θ M hθM (b i) = c i • b (τ i))
    (hwt : ∀ i j, wt (τ i) (σ j) = wt i j) (s : κ → Aˣ) :
    AddEquiv.baseChangeInvariantRestrictUnit (R := A) θ M hθM *
          kostantTorusPoints M b wt A s *
        (AddEquiv.baseChangeInvariantRestrictUnit (R := A) θ M hθM)⁻¹ =
      kostantTorusPoints M b wt A (MulEquiv.arrowCongr σ (MulEquiv.refl Aˣ) s) := by
  rw [baseChangeInvariantRestrictUnit_mul_kostantTorusPoints M b wt θ hθM τ σ c hθb hwt s,
    mul_assoc, mul_inv_cancel, mul_one]

end Pointwise

section Subgroup

variable (A : Type w) [CommRing A] [Algebra ℤ A]

/-- **A compatible monomial lattice symmetry normalizes the Kostant torus subgroup.** Conjugation
by the scalar-extended symmetry permutes all torus points through `σ`, hence maps the range of the
torus-points homomorphism onto itself. A numbered diagram symmetry supplies this data in the
intended pinned application. -/
theorem map_kostantTorusSubgroup_conj_baseChangeInvariantRestrictUnit
    (θ : V ≃+ V) (hθM : ∀ v, θ v ∈ M ↔ v ∈ M) (τ : η → η) (σ : Equiv.Perm κ)
    (c : η → ℤ)
    (hθb : ∀ i, AddEquiv.invariantRestrict θ M hθM (b i) = c i • b (τ i))
    (hwt : ∀ i j, wt (τ i) (σ j) = wt i j) :
    Subgroup.map
        (MulAut.conj (AddEquiv.baseChangeInvariantRestrictUnit (R := A) θ M hθM)).toMonoidHom
        (kostantTorusSubgroup M b wt A) =
      kostantTorusSubgroup M b wt A := by
  set U := AddEquiv.baseChangeInvariantRestrictUnit (R := A) θ M hθM with hU
  have hcomp : (MulAut.conj U).toMonoidHom.comp (kostantTorusPoints M b wt A) =
      (kostantTorusPoints M b wt A).comp
        (MulEquiv.arrowCongr σ (MulEquiv.refl Aˣ)).toMonoidHom :=
    MonoidHom.ext fun s => by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hU]
      exact conj_kostantTorusPoints_of_baseChangeInvariantRestrictUnit
        M b wt θ hθM τ σ c hθb hwt s
  rw [kostantTorusSubgroup_eq_range, MonoidHom.map_range, hcomp, MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _ (MulEquiv.surjective _), ← MonoidHom.range_eq_map]

end Subgroup

end TauCeti.UniversalEnvelopingAlgebra
