/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Subalgebra

/-!
# Restricting an automorphism to an invariant Lie subalgebra

An automorphism `σ` of a Lie algebra `L` *normalises* a Lie subalgebra `H` when `H.map σ = H`. This
file records the elementary consequences of that hypothesis: `σ` and `σ⁻¹` both map `H` into
itself, an element landing in `H` under `σ` was already in `H`, and `σ⁻¹` normalises `H` too. They
package into an automorphism `σ|H` of `H`.

Nothing here involves weights, nilpotence, or any hypothesis on the base ring beyond
commutativity. What `σ` does to the root spaces of `H` is in
`TauCeti/Algebra/Lie/Weights/Automorphism.lean`.

## Main definitions

* `TauCeti.restrictAut`: the automorphism `σ|H` of `H` obtained by restricting a normalising
  automorphism `σ` of `L`.

## Main results

* `LieSubalgebra.map_symm_eq_self_of_map_eq_self`: the inverse of a normalising automorphism
  normalises the subalgebra as well.
* `TauCeti.restrictAut_symm`: restricting the inverse gives the inverse of the restriction.
-/

public section

universe u v

section Restrict

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
  {H : LieSubalgebra R L}

variable (σ : L ≃ₗ⁅R⁆ L) (hσ : H.map (σ : L →ₗ⁅R⁆ L) = H)

include hσ

namespace LieSubalgebra

/-- An automorphism normalising `H` maps `H` into itself. -/
theorem apply_mem_of_map_eq_self {y : L} (hy : y ∈ H) : σ y ∈ H := by
  rw [← hσ, LieSubalgebra.mem_map]
  exact ⟨y, hy, rfl⟩

/-- If a normalising automorphism moves `y` into `H`, then `y` was already in `H`. -/
theorem mem_of_apply_mem_of_map_eq_self {y : L} (hy : σ y ∈ H) : y ∈ H := by
  rw [← hσ, LieSubalgebra.mem_map] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  exact σ.injective hzy ▸ hz

/-- The inverse of a normalising automorphism maps `H` into itself. -/
theorem symm_apply_mem_of_map_eq_self {y : L} (hy : y ∈ H) : σ.symm y ∈ H :=
  mem_of_apply_mem_of_map_eq_self σ hσ (by simpa using hy)

/-- The inverse of a normalising automorphism normalises `H` as well. -/
theorem map_symm_eq_self_of_map_eq_self : H.map (σ.symm : L →ₗ⁅R⁆ L) = H := by
  ext y
  rw [LieSubalgebra.mem_map]
  refine ⟨?_, fun hy => ⟨σ y, apply_mem_of_map_eq_self σ hσ hy, by simp⟩⟩
  rintro ⟨z, hz, rfl⟩
  exact symm_apply_mem_of_map_eq_self σ hσ hz

end LieSubalgebra

namespace TauCeti

/-- The restriction to `H` of an automorphism of `L` normalising `H`. -/
def restrictAut : H ≃ₗ⁅R⁆ H where
  toFun y := ⟨σ y, LieSubalgebra.apply_mem_of_map_eq_self σ hσ y.2⟩
  invFun y := ⟨σ.symm y, LieSubalgebra.symm_apply_mem_of_map_eq_self σ hσ y.2⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  map_lie' := by intro x y; ext; exact σ.map_lie x y
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

@[simp]
theorem coe_restrictAut_apply (y : H) : (restrictAut σ hσ y : L) = σ y := (rfl)

@[simp]
theorem coe_restrictAut_symm_apply (y : H) :
    ((restrictAut σ hσ).symm y : L) = σ.symm y := (rfl)

/-- The inverse of the restriction of a normalising automorphism is the restriction of the inverse
automorphism. -/
theorem restrictAut_symm :
    (restrictAut σ hσ).symm =
      restrictAut σ.symm (LieSubalgebra.map_symm_eq_self_of_map_eq_self σ hσ) :=
  LieEquiv.ext fun _ => rfl

end TauCeti

end Restrict
