/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Basic operations on tensor powers

Mathlib's `TensorPower.mulEquiv` identifies `⨂[R]^k M ⊗[R] ⨂[R]^m M` with `⨂[R]^(k + m) M`.  This
file records the inverse operation: `TensorPower.splitAt` cuts a tensor power of length `n` after
its first `k` factors, landing in `⨂[R]^k M ⊗[R] ⨂[R]^(n - k) M`, together with its value on pure
tensors and the fact that it is injective. It also identifies the first tensor power with the
underlying module.

## Main definitions

* `TensorPower.splitAt`: split a tensor power at a specified position.
* `TauCeti.TensorPower.oneEquiv`: identify the first tensor power with the underlying module.
-/

public section

open scoped TensorProduct

universe uR uM

variable (R : Type uR) (M : Type uM) [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace TauCeti.TensorPower

/-- A tensor word of length one is a single letter. -/
noncomputable def oneEquiv : TensorPower R 1 M ≃ₗ[R] M :=
  PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 ↦ M) 0

/-- The length-one tensor-power equivalence evaluates a pure tensor at its unique index. -/
@[simp]
theorem oneEquiv_tprod (f : Fin 1 → M) :
    oneEquiv R M (PiTensorProduct.tprod R f) = f 0 :=
  PiTensorProduct.subsingletonEquiv_apply_tprod 0 f

/-- The inverse length-one tensor-power equivalence sends a letter to the corresponding pure
tensor. -/
@[simp]
theorem oneEquiv_symm_apply (a : M) :
    (oneEquiv R M).symm a = PiTensorProduct.tprod R (fun _ ↦ a) :=
  PiTensorProduct.subsingletonEquiv_symm_apply' 0 a

end TauCeti.TensorPower

namespace TensorPower

/-- Split a tensor power after its first `k` factors. -/
noncomputable def splitAt (n k : ℕ) (hk : k ≤ n) :
    TensorPower R n M →ₗ[R] TensorPower R k M ⊗[R] TensorPower R (n - k) M :=
  (TensorPower.mulEquiv (R := R) (M := M)).symm.toLinearMap ∘ₗ
    (TensorPower.cast R M (Nat.add_sub_of_le hk).symm).toLinearMap

@[simp]
theorem mulEquiv_splitAt (n k : ℕ) (hk : k ≤ n) (x : TensorPower R n M) :
    TensorPower.mulEquiv (splitAt R M n k hk x) =
      TensorPower.cast R M (Nat.add_sub_of_le hk).symm x := by
  simp [splitAt]

/-- Splitting a tensor power at a fixed position loses no information: it is the composite of two
linear equivalences. -/
theorem splitAt_injective (n k : ℕ) (hk : k ≤ n) :
    Function.Injective (splitAt R M n k hk) := by
  intro x y hxy
  have := congrArg (TensorPower.mulEquiv (R := R) (M := M)) hxy
  rw [mulEquiv_splitAt, mulEquiv_splitAt] at this
  exact (TensorPower.cast R M (Nat.add_sub_of_le hk).symm).injective this

/-- Splitting a pure tensor separates its first `k` entries from the remaining entries. -/
@[simp]
theorem splitAt_tprod (n k : ℕ) (hk : k ≤ n) (x : Fin n → M) :
    splitAt R M n k hk (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun i : Fin k ↦ x (Fin.castLE hk i)) ⊗ₜ[R]
        PiTensorProduct.tprod R (fun j : Fin (n - k) ↦ x ⟨k + j.1, by omega⟩) := by
  apply TensorPower.mulEquiv.injective
  rw [mulEquiv_splitAt, TensorPower.cast_tprod, ← TensorPower.gMul_def,
    TensorPower.tprod_mul_tprod]
  congr 1
  funext i
  simp only [Function.comp_apply]
  by_cases hi : i.1 < k
  · let j : Fin k := ⟨i.1, hi⟩
    have hij : Fin.castAdd (n - k) j = i := by ext; rfl
    rw [← hij, Fin.append_left]
    congr 1
  · let j : Fin (n - k) := ⟨i.1 - k, by omega⟩
    have hij : Fin.natAdd k j = i := by ext; simp [j]; omega
    rw [← hij, Fin.append_right]
    congr 1

end TensorPower
