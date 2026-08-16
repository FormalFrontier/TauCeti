/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Points
public import TauCeti.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Matrix coordinates for Kostant root subgroups

Let `M` be a Kostant-stable integral lattice in a rational representation. A finite basis
`b : Basis (Fin n) ℤ M` gives every scalar extension `A ⊗[ℤ] M` the base-changed basis
`b.baseChange A`. This file expresses the divided-power root subgroup action in that basis,
as an element of `GLₙ(A)`.

The resulting matrices are natural in the commutative value ring. They are the finite-coordinate
input for the natural transformation whose representing morphism is the root subgroup
`𝔾ₐ → GLₙ`.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix`: the matrix-valued root
  subgroup attached to a finite integral basis.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrixParam`: the same homomorphism,
  parametrized directly by the additive element of the value ring.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_apply`: its entries are the
  coordinates of the divided-power exponential on basis vectors.
* `TauCeti.UniversalEnvelopingAlgebra.map_kostantRootSubgroupMatrix` and
  `TauCeti.UniversalEnvelopingAlgebra.map_kostantRootSubgroupMatrixParam`: matrix coordinates
  commute with maps of value rings.

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
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)

section Pointwise

variable {A : Type*} [CommRing A]

/-- The matrix of a Kostant root-subgroup point in the scalar extension of a fixed integral
basis. -/
noncomputable def kostantRootSubgroupMatrix :
    WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A) →*
      Matrix.GeneralLinearGroup (Fin n) A :=
  (Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMonoidHom).comp
    (kostantRootSubgroupPoints e h ρ M hM i hnil)

/-- The matrix-valued Kostant root subgroup parametrized directly by the additive element of the
value ring. -/
noncomputable def kostantRootSubgroupMatrixParam :
    Multiplicative A →* Matrix.GeneralLinearGroup (Fin n) A :=
  (kostantRootSubgroupMatrix e h ρ M hM i hnil b).comp
    (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm.toMonoidHom

/-- An entry of the root-subgroup matrix is the corresponding coordinate of the exponential
action on a base-changed basis vector. -/
theorem kostantRootSubgroupMatrix_apply
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) (r s : Fin n) :
    kostantRootSubgroupMatrix e h ρ M hM i hnil b f r s =
      (b.baseChange A).repr
        ((kostantRootSubgroupPoints e h ρ M hM i hnil f).val
          (b.baseChange A s)) r := by
  rw [kostantRootSubgroupMatrix]
  exact LinearMap.toMatrixAlgEquiv_apply (b.baseChange A)
    (kostantRootSubgroupPoints e h ρ M hM i hnil f).val r s

/-- The directly parametrized matrix agrees with evaluation on the additive-group point having
that parameter. -/
theorem kostantRootSubgroupMatrixParam_apply (t : Multiplicative A) :
    kostantRootSubgroupMatrixParam e h ρ M hM i hnil b t =
      kostantRootSubgroupMatrix e h ρ M hM i hnil b
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t) := by
  rw [kostantRootSubgroupMatrixParam]
  rfl

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
  change φ.toIntAlgHom
      ((b.baseChange A).repr
        ((kostantRootSubgroupPoints e h ρ M hM i hnil f).val
          (b.baseChange A s)) r) = _
  rw [Module.Basis.map_baseChange_repr b φ.toIntAlgHom]
  apply congrArg (fun z => (b.baseChange B).repr z r)
  simpa only [Module.Basis.baseChange_apply, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply, LinearMap.id_apply, map_one] using
    map_kostantRootSubgroupPoints e h ρ M hM i hnil φ f (b.baseChange A s)

/-- The directly parametrized root-subgroup matrices commute with maps of value rings. -/
theorem map_kostantRootSubgroupMatrixParam (φ : A →+* B) (t : Multiplicative A) :
    Matrix.GeneralLinearGroup.map φ
        (kostantRootSubgroupMatrixParam e h ρ M hM i hnil b t) =
      kostantRootSubgroupMatrixParam e h ρ M hM i hnil b
        (Multiplicative.ofAdd (φ (Multiplicative.toAdd t))) := by
  rw [kostantRootSubgroupMatrixParam_apply, map_kostantRootSubgroupMatrix,
    kostantRootSubgroupMatrixParam_apply,
    AdditiveGroup.mapValue_gaPointsMulEquiv_symm_apply]
  rfl

end Naturality

end TauCeti.UniversalEnvelopingAlgebra
