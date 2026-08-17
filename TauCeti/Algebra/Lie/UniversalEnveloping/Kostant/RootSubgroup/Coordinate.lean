/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Matrix coordinates for Kostant root subgroups

Let `M` be a Kostant-stable integral lattice in a rational representation. A finite basis
`b : Basis η ℤ M` gives every scalar extension `A ⊗[ℤ] M` the base-changed basis
`b.baseChange A`. This file expresses the divided-power root subgroup action in that basis,
as an invertible matrix over `A` indexed by `η`.

The resulting matrices are natural in the commutative value ring. They are the finite-coordinate
input for the natural transformation whose representing morphism is the root subgroup
`𝔾ₐ → GLₙ`.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix`: the matrix-valued root
  subgroup attached to a finite integral basis.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_apply`: its entries are the
  coordinates of the divided-power exponential on basis vectors.
* `TauCeti.UniversalEnvelopingAlgebra.map_kostantRootSubgroupMatrix`: matrix coordinates commute
  with maps of value rings.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type w} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable (i : ι)
variable (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {η : Type*} [Fintype η] [DecidableEq η] (b : Module.Basis η ℤ M)

section Pointwise

variable {A : Type*} [CommRing A]

/-- The Kostant root subgroup in matrix coordinates: the monoid homomorphism sending an `A`-point
to the matrix of its action on `A ⊗[ℤ] M` in the base-changed basis `b.baseChange A`. -/
noncomputable def kostantRootSubgroupMatrix :
    WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A) →*
      Matrix.GeneralLinearGroup η A :=
  (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom).comp
    (kostantRootSubgroupPoints e h ρ M hM i hnil)

/-- The public unfolding equation for the matrix-valued root subgroup, exposing across the module
boundary the divided-power action followed by the change to the coordinates of `b.baseChange A`. -/
theorem kostantRootSubgroupMatrix_def :
    kostantRootSubgroupMatrix e h ρ M hM i hnil b =
      (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom).comp
        (kostantRootSubgroupPoints e h ρ M hM i hnil) := by
  rw [kostantRootSubgroupMatrix]

/-- An entry of the root-subgroup matrix is the corresponding coordinate of the exponential
action on a base-changed basis vector. -/
@[simp] theorem kostantRootSubgroupMatrix_apply
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) (r s : η) :
    kostantRootSubgroupMatrix e h ρ M hM i hnil b f r s =
      (b.baseChange A).repr
        ((kostantRootSubgroupPoints e h ρ M hM i hnil f).val
          (b.baseChange A s)) r := by
  rw [kostantRootSubgroupMatrix, MonoidHom.comp_apply, Units.coe_map]
  exact LinearMap.toMatrixAlgEquiv_apply (b.baseChange A)
    (kostantRootSubgroupPoints e h ρ M hM i hnil f).val r s

end Pointwise

section Naturality

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The matrix-valued Kostant root subgroup is natural in the value ring. -/
theorem map_kostantRootSubgroupMatrix (φ : A →+* B)
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    Matrix.GeneralLinearGroup.map φ
        (kostantRootSubgroupMatrix e h ρ M hM i hnil b f) =
      kostantRootSubgroupMatrix e h ρ M hM i hnil b
        (AlgHom.mapValue (H := SymmetricAlgebra ℤ ℤ) φ.toIntAlgHom f) := by
  apply Matrix.GeneralLinearGroup.ext
  intro r s
  rw [Matrix.GeneralLinearGroup.map_apply,
    kostantRootSubgroupMatrix_apply, kostantRootSubgroupMatrix_apply]
  have hmatrix := Module.Basis.map_toMatrixAlgEquiv_baseChange b φ.toIntAlgHom
    (kostantRootSubgroupPoints e h ρ M hM i hnil f).val
    (kostantRootSubgroupPoints e h ρ M hM i hnil
      (AlgHom.mapValue (H := SymmetricAlgebra ℤ ℤ) φ.toIntAlgHom f)).val
    (map_kostantRootSubgroupPoints e h ρ M hM i hnil φ f)
  simpa only [Matrix.map_apply, LinearMap.toMatrixAlgEquiv_apply,
    RingHom.toIntAlgHom_apply] using congrFun (congrFun hmatrix r) s

end Naturality

end TauCeti.UniversalEnvelopingAlgebra
