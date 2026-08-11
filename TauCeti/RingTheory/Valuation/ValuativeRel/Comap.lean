/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Comap for valuative relations

We define the pullback (comap) of a `ValuativeRel` along a ring homomorphism.

## Main definitions

* `TauCeti.ValuativeRel.comap φ v` : Given `φ : A →+* B` and a valuative relation `v` on `B`,
  the induced `ValuativeRel A` defined by `a₁ ≤ᵥ a₂ ↔ φ(a₁) ≤ᵥ φ(a₂)`.

## References

Ported from the open Mathlib pull request
[leanprover-community/mathlib4#38009](https://github.com/leanprover-community/mathlib4/pull/38009);
this copy is deleted in favour of the Mathlib declarations once that pull request reaches the
pinned Mathlib.
-/

public section

namespace TauCeti.ValuativeRel

variable {A B : Type*} [Semiring A] [Semiring B]

/-- The pullback of a `ValuativeRel` along `φ : A →+* B`:
`a₁ ≤ᵥ a₂ ↔ φ(a₁) ≤ᵥ φ(a₂)`. Use `comap_vle` and `comap_vlt` to compute with it. -/
-- `instance_reducible` is the minimum reducibility the `classDefReducibility` check accepts
-- for a definition of class type; the body is deliberately not exposed.
@[instance_reducible]
def comap (φ : A →+* B) (v : ValuativeRel B) : ValuativeRel A where
  vle a₁ a₂ := (φ a₁) ≤ᵥ (φ a₂)
  vle_total a₁ a₂ := v.vle_total (φ a₁) (φ a₂)
  vle_trans h₁ h₂ := v.vle_trans h₁ h₂
  vle_add h₁ h₂ := by simpa [map_add] using v.vle_add h₁ h₂
  mul_vle_mul_left h z := by simpa [map_mul] using v.mul_vle_mul_left h (φ z)
  vle_mul_cancel h₀ h := by
    rw [map_zero] at h₀
    simpa [map_mul] using v.vle_mul_cancel h₀ (by simpa [map_mul] using h)
  not_vle_one_zero := by simp [v.not_vle_one_zero]
  vle_mul_comm := by simp only [map_mul]; exact v.vle_mul_comm

/-- The relation pulled back along `φ` compares images under `φ`. -/
@[simp]
theorem comap_vle (φ : A →+* B) (v : ValuativeRel B) (a₁ a₂ : A) :
    (comap φ v).vle a₁ a₂ ↔ v.vle (φ a₁) (φ a₂) := Iff.rfl

/-- The strict relation pulled back along `φ` compares images under `φ`. -/
@[simp]
theorem comap_vlt (φ : A →+* B) (v : ValuativeRel B) (a₁ a₂ : A) :
    (comap φ v).vlt a₁ a₂ ↔ v.vlt (φ a₁) (φ a₂) := Iff.rfl

/-- Pulling back along the identity homomorphism is the identity. -/
@[simp]
theorem comap_id (v : ValuativeRel A) : comap (RingHom.id A) v = v := by
  ext a₁ a₂; rfl

/-- Pulling back along a composite is the composite of the pullbacks. -/
@[simp]
theorem comap_comp {C : Type*} [Semiring C] (φ : A →+* B) (ψ : B →+* C) (v : ValuativeRel C) :
    comap (ψ.comp φ) v = comap φ (comap ψ v) := by
  ext a₁ a₂; rfl

end TauCeti.ValuativeRel
