/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Domain
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor squares of subrings

This file defines the canonical map from the integral tensor square of a subring of an algebra
to the tensor square of the ambient algebra, together with its range and basic membership lemmas.

## Main definitions and results

* `TauCeti.Subring.tensorSquareMap`: the canonical map from the integral tensor square.
* `TauCeti.Subring.tensorSquareMap_injective`: over a rational algebra, the canonical map is
  injective.
* `TauCeti.Subring.tensorSquareRange`: the range of the canonical map.
* `TauCeti.Subring.tensorSquareEquivRange`: over a rational algebra, the canonical equivalence
  onto that range.
* `TauCeti.Subring.mem_tensorSquareRange_iff`: membership in the range in terms of a preimage.
* `TauCeti.Subring.tmul_mem_tensorSquareRange`: pure tensors of subring elements lie in the range.
-/

public section

open scoped TensorProduct

namespace TauCeti.Subring

universe u v

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- The canonical map from the integral tensor square of a subring to the tensor square of the
ambient algebra. On pure tensors, it applies the subring inclusion in both factors. -/
noncomputable def tensorSquareMap (S : Subring A) : S ⊗[ℤ] S →ₐ[ℤ] A ⊗[R] A :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).restrictScalars ℤ |>.comp
      S.subtype.toIntAlgHom)
    ((Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).restrictScalars ℤ |>.comp
      S.subtype.toIntAlgHom)
    fun x y => by
      simp only [AlgHom.comp_apply, RingHom.toIntAlgHom_apply, Subring.coe_subtype]
      exact (Commute.one_right _).tmul (Commute.one_left _)

/-- The canonical tensor-square map sends a pure tensor to the pure tensor of the underlying
ambient elements. -/
@[simp]
theorem tensorSquareMap_tmul (S : Subring A) (x y : S) :
    tensorSquareMap R S (x ⊗ₜ[ℤ] y) = (x : A) ⊗ₜ[R] (y : A) := by
  simp [tensorSquareMap]

section Rational

variable {A : Type v} [Ring A] [Algebra ℚ A]

-- Since the two factors are rational vector spaces, imposing rational balancing on their integer
-- tensor product adds no relations. Mathlib proves this as the compatibility of the two scalar
-- actions; naming the resulting equivalence keeps that implementation out of the injectivity
-- argument below.
private noncomputable def intTensorToRatTensor : A ⊗[ℤ] A ≃ₐ[ℚ] A ⊗[ℚ] A :=
  (Algebra.TensorProduct.equivOfCompatibleSMul ℤ ℚ ℚ A A).symm

@[simp]
private theorem intTensorToRatTensor_tmul (x y : A) :
    intTensorToRatTensor (A := A) (x ⊗ₜ[ℤ] y) = x ⊗ₜ[ℚ] y := by
  rw [intTensorToRatTensor, AlgEquiv.symm_apply_eq]
  exact (Algebra.TensorProduct.mapOfCompatibleSMul_tmul
    (R := ℤ) (S := ℚ) (T := ℚ) (A := A) (B := A) x y).symm

private theorem tensorSquareMap_eq_intTensorToRatTensor (S : Subring A) :
    tensorSquareMap ℚ S =
      ((intTensorToRatTensor (A := A)).toAlgHom.restrictScalars ℤ).comp
        (Algebra.TensorProduct.map (R := ℤ) (S := ℤ)
          S.subtype.toIntAlgHom S.subtype.toIntAlgHom) := by
  ext x <;> simp

/-- The canonical map from the integer tensor square of a subring of a rational algebra to the
rational tensor square of the ambient algebra is injective. -/
-- The subring is torsion-free as an abelian group because it embeds in a rational vector space,
-- hence flat over `ℤ`. Therefore tensoring its inclusion with itself is injective. The target
-- of that map is initially `A ⊗[ℤ] A`; the canonical equivalence `A ⊗[ℤ] A ≃ A ⊗[ℚ] A` then
-- gives the stated map.
theorem tensorSquareMap_injective (S : Subring A) :
    Function.Injective (tensorSquareMap ℚ S) := by
  let : IsAddTorsionFree A := .of_module_rat A
  let : IsAddTorsionFree S :=
    Function.Injective.isAddTorsionFree S.subtype.toAddMonoidHom S.subtype_injective
  let : Module.Flat ℤ S := inferInstance
  let f : S →ₗ[ℤ] A := S.subtype.toIntAlgHom.toLinearMap
  have hinjective : Function.Injective (TensorProduct.map f f) :=
    TensorProduct.map_injective_of_flat_flat_of_isDomain
      (R := ℤ) f f S.subtype_injective S.subtype_injective
  intro x y hxy
  apply hinjective
  have hmap :
      Algebra.TensorProduct.map (R := ℤ) (S := ℤ)
        S.subtype.toIntAlgHom S.subtype.toIntAlgHom x =
      Algebra.TensorProduct.map (R := ℤ) (S := ℤ)
        S.subtype.toIntAlgHom S.subtype.toIntAlgHom y := by
    apply (intTensorToRatTensor (A := A)).injective
    rw [tensorSquareMap_eq_intTensorToRatTensor] at hxy
    exact hxy
  rw [← AlgHom.toLinearMap_apply, ← AlgHom.toLinearMap_apply,
      Algebra.TensorProduct.toLinearMap_map,
      TensorProduct.AlgebraTensorModule.map_eq] at hmap
  exact hmap

end Rational

/-- The range of the canonical map from the integral tensor square of a subring to the tensor
square of the ambient algebra. -/
noncomputable def tensorSquareRange (S : Subring A) : Subring (A ⊗[R] A) :=
  (tensorSquareMap R S).toRingHom.range

/-- Membership in the tensor-square range is equivalent to having an integral tensor preimage. -/
@[simp]
theorem mem_tensorSquareRange_iff (S : Subring A) (z : A ⊗[R] A) :
    z ∈ tensorSquareRange R S ↔ ∃ t : S ⊗[ℤ] S, tensorSquareMap R S t = z := by
  rfl

/-- A pure tensor whose two factors lie in a subring belongs to its tensor-square range. -/
theorem tmul_mem_tensorSquareRange (S : Subring A) {x y : A} (hx : x ∈ S) (hy : y ∈ S) :
    x ⊗ₜ[R] y ∈ tensorSquareRange R S := by
  rw [mem_tensorSquareRange_iff]
  exact ⟨(⟨x, hx⟩ : S) ⊗ₜ[ℤ] (⟨y, hy⟩ : S), tensorSquareMap_tmul R S _ _⟩

section RationalRange

variable {A : Type v} [Ring A] [Algebra ℚ A]

/-- The canonical equivalence from the integer tensor square of a subring of a rational algebra
onto its range in the rational tensor square. -/
noncomputable def tensorSquareEquivRange (S : Subring A) :
    S ⊗[ℤ] S ≃ₐ[ℤ] tensorSquareRange ℚ S :=
  AlgEquiv.ofInjective (tensorSquareMap ℚ S) (tensorSquareMap_injective S)

/-- The equivalence onto the tensor-square range acts by the canonical tensor-square map. -/
@[simp]
theorem coe_tensorSquareEquivRange_apply (S : Subring A) (t : S ⊗[ℤ] S) :
    (tensorSquareEquivRange S t : A ⊗[ℚ] A) = tensorSquareMap ℚ S t :=
  AlgEquiv.ofInjective_apply (tensorSquareMap ℚ S) (tensorSquareMap_injective S) t

end RationalRange

end TauCeti.Subring
