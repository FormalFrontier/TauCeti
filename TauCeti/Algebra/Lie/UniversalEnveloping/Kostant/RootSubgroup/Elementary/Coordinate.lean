/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Coordinate
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Elementary.Basic

/-!
# Matrix coordinates of the parametrized Kostant root subgroups

The root subgroup map `x_α` with its parameter read in the value ring, `kostantRootSubgroupParam`,
takes values in the automorphisms of a scalar extension `A ⊗[ℤ] M`. A finite basis
`b : Basis η ℤ M` turns those automorphisms into invertible matrices, and
`kostantRootSubgroupMatrix` is the resulting matrix-valued root subgroup. This file compares the
two: in the coordinates of `b.baseChange A`, a parametrized root-subgroup element is exactly its
represented root-subgroup matrix.

The comparison involves neither the represented `GLₙ` presentation nor any group scheme, so it is
stated for an arbitrary finite basis index and lives below the scheme layer.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.basisMatrix_kostantRootSubgroupParam`: in basis coordinates,
  a parametrized Kostant root-subgroup element is its represented root-subgroup matrix.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
-/

public section

open CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type*} {κ : Type*}
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)
variable (i : ι)
variable (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {η : Type*} [Fintype η] [DecidableEq η] (b : Module.Basis η ℤ M)

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

/-- In basis coordinates, a parametrized Kostant root-subgroup element is its represented
root-subgroup matrix. -/
@[simp]
theorem basisMatrix_kostantRootSubgroupParam (A : Type v) [CommRing A] (t : Multiplicative A) :
    Units.map (LinearMap.toMatrixAlgEquiv (b.baseChange A)).toMulEquiv
        (kostantRootSubgroupParam e h ρ M hM i hnil (CommAlgCat.of ℤ A) t) =
      kostantRootSubgroupMatrix e h ρ M hM i hnil b
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t) := by
  rw [kostantRootSubgroupMatrix_def, MonoidHom.comp_apply,
    kostantRootSubgroupParam_apply, MulEquiv.toMonoidHom_eq_coe]

end TauCeti.UniversalEnvelopingAlgebra
