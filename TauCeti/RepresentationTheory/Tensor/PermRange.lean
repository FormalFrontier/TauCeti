/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic
public import TauCeti.RepresentationTheory.Tensor.Power

/-!
# The image of a group-algebra element acting on a tensor power

Permuting the tensor factors of `⨂[R]^d M` commutes with the diagonal action of a representation
`ρ` on `M`, so an element `a` of the group algebra `R[S_d]` acts on the tensor power by an
intertwining map of `ρ.tensorPower d` with itself.  Its image is therefore a subrepresentation of
the tensor power.  This file records that image and the elementary ways it depends on `a`: the
identity cuts out the whole tensor power, the zero cuts out `⊥`, multiplying on the right shrinks
the image, and conjugating by a permutation moves the image by that permutation of the factors.

Nothing here is specific to Young symmetrizers; taking `a` to be one is the Weyl construction.

## Main definitions

* `TauCeti.tensorPowerPermMap`: acting on `⨂[R]^d M` by an element of `R[S_d]`, as an
  intertwining map of the tensor power with itself.
* `TauCeti.tensorPowerRange`: the image of that map, as a subrepresentation.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 2, "Young symmetrizers and the Schur functor", whose Weyl-module target consumes this
  construction.
-/

public section

open scoped TensorProduct

universe u v w

namespace TauCeti

variable {R : Type u} {G : Type v} {M : Type w}
variable [CommSemiring R] [Monoid G] [AddCommMonoid M] [Module R M]
variable (ρ : Representation R G M) (d : ℕ) (a b : MonoidAlgebra R (Equiv.Perm (Fin d)))

/-- Acting on `⨂[R]^d M` by an element of `R[S_d]`, permuting tensor factors, is an intertwining
map of the diagonal action of `ρ` on the tensor power with itself: the two actions commute. -/
noncomputable def tensorPowerPermMap :
    Representation.IntertwiningMap (ρ.tensorPower d) (ρ.tensorPower d) where
  toLinearMap := (PiTensorProduct.reindexRepresentation R M (Fin d)).asAlgebraHom a
  isIntertwining' g := by
    rw [Representation.tensorPower_apply]
    exact PiTensorProduct.commute_reindexRepresentation_asAlgebraHom_map R M (Fin d) a (ρ g)

/-- The linear map underlying the tensor-power action of a group-algebra element. -/
@[simp]
theorem tensorPowerPermMap_toLinearMap :
    (tensorPowerPermMap ρ d a).toLinearMap =
      (PiTensorProduct.reindexRepresentation R M (Fin d)).asAlgebraHom a :=
  (rfl)

/-- The image of `a ∈ R[S_d]`, acting on `⨂[R]^d M` by permuting tensor factors, as a
subrepresentation of the `d`-th tensor power of `ρ`. -/
noncomputable def tensorPowerRange : Subrepresentation (ρ.tensorPower d) :=
  (tensorPowerPermMap ρ d a).range

/-- The submodule underlying `tensorPowerRange` is the range of the group-algebra action. -/
@[simp]
theorem tensorPowerRange_toSubmodule :
    (tensorPowerRange ρ d a).toSubmodule =
      LinearMap.range ((PiTensorProduct.reindexRepresentation R M (Fin d)).asAlgebraHom a) :=
  (rfl)

/-- The identity of the group algebra cuts out the whole tensor power. -/
@[simp]
theorem tensorPowerRange_one : tensorPowerRange ρ d 1 = ⊤ :=
  Subrepresentation.toSubmodule_injective <| by
    rw [tensorPowerRange_toSubmodule, map_one]
    exact LinearMap.range_eq_top.mpr fun x => ⟨x, rfl⟩

/-- The zero of the group algebra cuts out the zero subrepresentation. -/
@[simp]
theorem tensorPowerRange_zero : tensorPowerRange ρ d 0 = ⊥ :=
  Subrepresentation.toSubmodule_injective <| by
    rw [tensorPowerRange_toSubmodule, map_zero, LinearMap.range_zero]
    -- the submodule underlying the zero subrepresentation is `⊥`
    rfl

/-- Multiplying on the right shrinks the image: `⨂^d M · a b ⊆ ⨂^d M · a`. -/
theorem tensorPowerRange_mul_le : tensorPowerRange ρ d (a * b) ≤ tensorPowerRange ρ d a := by
  have h : (tensorPowerRange ρ d (a * b)).toSubmodule ≤ (tensorPowerRange ρ d a).toSubmodule := by
    rw [tensorPowerRange_toSubmodule, tensorPowerRange_toSubmodule, map_mul]
    exact LinearMap.range_comp_le_range _ _
  -- the order on subrepresentations is inclusion of the underlying submodules
  exact fun x hx => h hx

/-- Conjugating the group-algebra element by a permutation moves the image by the corresponding
permutation of the tensor factors. -/
theorem tensorPowerRange_conj (σ : Equiv.Perm (Fin d)) :
    (tensorPowerRange ρ d
        (MonoidAlgebra.single σ 1 * a * MonoidAlgebra.single σ⁻¹ 1)).toSubmodule =
      (tensorPowerRange ρ d a).toSubmodule.map
        (PiTensorProduct.reindex R (fun _ : Fin d => M) σ : (⨂[R]^d M) →ₗ[R] (⨂[R]^d M)) := by
  have hsurj :
      LinearMap.range (PiTensorProduct.reindexRepresentation R M (Fin d) σ⁻¹) = ⊤ := by
    rw [PiTensorProduct.reindexRepresentation_apply]
    exact LinearEquiv.range _
  rw [tensorPowerRange_toSubmodule, tensorPowerRange_toSubmodule, map_mul, map_mul,
    Representation.asAlgebraHom_single_one, Representation.asAlgebraHom_single_one,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    LinearMap.range_comp_of_range_eq_top _ hsurj, LinearMap.range_comp,
    PiTensorProduct.reindexRepresentation_apply]

end TauCeti
