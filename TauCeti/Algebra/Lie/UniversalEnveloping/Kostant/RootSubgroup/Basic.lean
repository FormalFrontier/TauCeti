/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.BaseChangeAction
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Root subgroups from Kostant-stable integral modules

Let `U_ℤ = kostantForm e h` be a Kostant integral form acting on a rational vector space `V`,
and let `M ≤ V` be an additive subgroup preserved by `U_ℤ`. If a designated root vector `eᵢ`
acts nilpotently, its integral divided powers define, over every commutative ring `A`, an
additive one-parameter subgroup

```text
A⁺ → Aut_A(A ⊗[ℤ] M),    t ↦ ∑ₙ tⁿ ρ(eᵢ)⁽ⁿ⁾.
```

This file proves that these homomorphisms are natural in `A`, turning the ring-by-ring exponential
actions from `TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.BaseChangeAction` into a natural
root-subgroup map on points. Its realization in a finite base-changed basis is provided by
`TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Coordinate`. Integral PBW must still
supply a finite free admissible lattice, after which the existing full-faithfulness theorem for the
functor of points can recover the scheme morphism `𝔾ₐ → GLₙ`.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupPoints`: the root subgroup on
  algebra-valued points.
* `TauCeti.UniversalEnvelopingAlgebra.map_kostantRootSubgroupPoints`: naturality under a
  homomorphism of value rings.

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

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

section Points

variable {A : Type*} [CommRing A] [Algebra ℤ A]

/-- The root subgroup attached to a nilpotent root-vector action, on points valued in a
commutative ring `A`.

Under the usual equivalence `𝔾ₐ(A) ≃ A⁺`, the parameter `t` acts on `A ⊗[ℤ] M` by the finite
divided-power exponential of `ρ(eᵢ)`. -/
noncomputable def kostantRootSubgroupPoints :
    WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A) →*
      LinearMap.GeneralLinearGroup A (A ⊗[ℤ] M) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).symm.toMonoidHom.comp <|
    (baseChangeKostantExpHom e h ρ M hM i hnil).comp
      (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).toMonoidHom

/-- The linear equivalence underlying a Kostant root-subgroup point is the integral
divided-power exponential with the corresponding `𝔾ₐ` parameter. -/
@[simp] theorem kostantRootSubgroupPoints_toLinearEquiv
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    (kostantRootSubgroupPoints e h ρ M hM i hnil f).toLinearEquiv =
      baseChangeKostantExpHom e h ρ M hM i hnil
        (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f) := by
  rw [kostantRootSubgroupPoints]
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[ℤ] M)).apply_symm_apply _

/-- The invertible linear map underlying a Kostant root-subgroup point is the base-changed
divided-power exponential at the corresponding parameter. -/
theorem kostantRootSubgroupPoints_val (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    (kostantRootSubgroupPoints e h ρ M hM i hnil f).val =
      baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M
        (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i n hv)
        (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) f)) := by
  refine LinearMap.ext fun z => ?_
  rw [← LinearMap.GeneralLinearGroup.coe_toLinearEquiv, kostantRootSubgroupPoints_toLinearEquiv,
    coe_baseChangeKostantExpHom]

/-- On an elementary tensor, a Kostant root-subgroup point acts by the expected finite
divided-power formula. -/
@[simp] theorem kostantRootSubgroupPoints_tmul
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) (a : A) (m : M) :
    (kostantRootSubgroupPoints e h ρ M hM i hnil f).val (a ⊗ₜ[ℤ] m) =
      ∑ n ∈ Finset.range
          (nilpotencyClass (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))),
        ((Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f)) ^ n * a) ⊗ₜ[ℤ]
          integralDividedPower
            (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M n
            (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem
              e h ρ hM i n hv) m := by
  rw [kostantRootSubgroupPoints_val]
  exact baseChangeExp_tmul
    (R := A) (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M
      (fun n _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem
        e h ρ hM i n hv)
      (Multiplicative.toAdd (AdditiveGroup.gaPointsMulEquiv f)) a m

end Points

section Naturality

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B]

/-- Kostant root-subgroup points are natural between value rings carrying explicit `ℤ`-algebra
structures. -/
theorem map_kostantRootSubgroupPoints_algHom
    (φ : A →ₐ[ℤ] B)
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ∀ z : A ⊗[ℤ] M,
      TensorProduct.map φ.toLinearMap LinearMap.id
          ((kostantRootSubgroupPoints e h ρ M hM i hnil f).val z) =
        (kostantRootSubgroupPoints e h ρ M hM i hnil
            (AlgHom.mapValue (H := SymmetricAlgebra ℤ ℤ) φ f)).val
          (TensorProduct.map φ.toLinearMap LinearMap.id z) := by
  intro z
  rw [kostantRootSubgroupPoints_val, kostantRootSubgroupPoints_val,
    AdditiveGroup.toAdd_gaPointsMulEquiv_mapValue]
  exact map_baseChangeExp_algHom φ _ _ _ _ z

end Naturality

section CanonicalNaturality

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Kostant root-subgroup points are natural in the value ring. Applying `φ` to the scalar
coordinate of every tensor intertwines the automorphism attached to `t : A` with the
automorphism attached to `φ(t) : B`. -/
theorem map_kostantRootSubgroupPoints
    (φ : A →+* B)
    (f : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    ∀ z : A ⊗[ℤ] M,
      TensorProduct.map φ.toIntAlgHom.toLinearMap LinearMap.id
          ((kostantRootSubgroupPoints e h ρ M hM i hnil f).val z) =
        (kostantRootSubgroupPoints e h ρ M hM i hnil
            (AlgHom.mapValue (H := SymmetricAlgebra ℤ ℤ) φ.toIntAlgHom f)).val
          (TensorProduct.map φ.toIntAlgHom.toLinearMap LinearMap.id z) := by
  exact map_kostantRootSubgroupPoints_algHom e h ρ M hM i hnil φ.toIntAlgHom f

end CanonicalNaturality

end TauCeti.UniversalEnvelopingAlgebra
