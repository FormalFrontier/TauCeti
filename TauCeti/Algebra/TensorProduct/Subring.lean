/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor squares of subrings

This file defines the canonical map from the integral tensor square of a subring of an algebra
to the tensor square of the ambient algebra, together with its range and basic membership lemmas.

## Main definitions and results

* `TauCeti.Subring.tensorSquareMap`: the canonical map from the integral tensor square.
* `TauCeti.Subring.tensorSquareRange`: the range of the canonical map.
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

end TauCeti.Subring
