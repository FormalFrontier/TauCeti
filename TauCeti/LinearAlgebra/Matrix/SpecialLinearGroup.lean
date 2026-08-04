/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.ZMod.Units

/-!
# Surjectivity of the reduction map `SL₂(ℤ) → SL₂(ℤ/dℤ)`

The natural reduction map `SL₂(ℤ) → SL₂(ℤ/dℤ)` is surjective (strong approximation for
`SL₂`; Shimura §1.6, Serre Ch. VII).

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GLn/SL2Surjection.lean`, Chris Birkbeck). Prerequisite for the
diamond operators of the ModularForms roadmap (Layer 0), where it realizes every unit of
`ZMod N` as the lower-right entry of a matrix in `Γ₀(N)`.

## Main results

* `Matrix.SpecialLinearGroup.map_intCast_zmod_surjective`: strong approximation for `SL₂`.

## References

* Shimura, *Introduction to the arithmetic theory of automorphic functions*, §1.6
* Serre, *A course in arithmetic*, Ch. VII
-/

public section

open Matrix

variable {d : ℕ}

namespace Matrix.SpecialLinearGroup

variable {R : Type*} [CommRing R]

/-- The `(1,0)` coordinate of the inverse of an `SL₂` element, from `SL2_inv_expl`. -/
private lemma inv_apply_one_zero (M : SpecialLinearGroup (Fin 2) R) :
    (M⁻¹ : SpecialLinearGroup (Fin 2) R) 1 0 = -(M 1 0) := by
  rw [SL2_inv_expl]
  rfl

/-- The `(1,1)` coordinate of the inverse of an `SL₂` element, from `SL2_inv_expl`. -/
private lemma inv_apply_one_one (M : SpecialLinearGroup (Fin 2) R) :
    (M⁻¹ : SpecialLinearGroup (Fin 2) R) 1 1 = M 0 0 := by
  rw [SL2_inv_expl]
  rfl

/-- The `(0,0)` coordinate of the inverse of an `SL₂` element, from `SL2_inv_expl`. -/
private lemma inv_apply_zero_zero (M : SpecialLinearGroup (Fin 2) R) :
    (M⁻¹ : SpecialLinearGroup (Fin 2) R) 0 0 = M 1 1 := by
  rw [SL2_inv_expl]
  rfl

/-- The `(0,1)` coordinate of the inverse of an `SL₂` element, from `SL2_inv_expl`. -/
private lemma inv_apply_zero_one (M : SpecialLinearGroup (Fin 2) R) :
    (M⁻¹ : SpecialLinearGroup (Fin 2) R) 0 1 = -(M 0 1) := by
  rw [SL2_inv_expl]
  rfl

private lemma mul_apply_one_zero (M g : SpecialLinearGroup (Fin 2) R) :
    (M * g) 1 0 = M 1 0 * g 0 0 + M 1 1 * g 1 0 := by
  simp [coe_mul, mul_apply, Fin.sum_univ_two]

private lemma mul_apply_zero_zero (M g : SpecialLinearGroup (Fin 2) R) :
    (M * g) 0 0 = M 0 0 * g 0 0 + M 0 1 * g 1 0 := by
  simp [coe_mul, mul_apply, Fin.sum_univ_two]

private lemma inv_mul_one_zero_eq_zero
    (M g : SpecialLinearGroup (Fin 2) R)
    (h0 : M 0 0 = g 0 0) (h1 : M 1 0 = g 1 0) : (M⁻¹ * g) 1 0 = 0 := by
  rw [mul_apply_one_zero, inv_apply_one_zero, inv_apply_one_one, ← h0, ← h1]
  ring

private lemma inv_mul_zero_zero_eq_one
    (M g : SpecialLinearGroup (Fin 2) R)
    (h0 : M 0 0 = g 0 0) (h1 : M 1 0 = g 1 0) : (M⁻¹ * g) 0 0 = 1 := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have h := M.det_coe
    rwa [det_fin_two] at h
  rw [mul_apply_zero_zero, inv_apply_zero_zero, inv_apply_zero_one, ← h0, ← h1]
  linear_combination hdet

/-- An element of `SL₂(ℤ/dℤ)` with first column `(1, 0)` is upper unitriangular, and lifts
to `SL₂(ℤ)` as a transvection, by lifting its upper-right entry. -/
private lemma exists_map_eq_of_col_eq (h : SpecialLinearGroup (Fin 2) (ZMod d))
    (h00 : h 0 0 = 1) (h10 : h 1 0 = 0) :
    ∃ τ : SpecialLinearGroup (Fin 2) ℤ,
      SpecialLinearGroup.map (Int.castRingHom (ZMod d)) τ = h := by
  obtain ⟨t₀, ht₀⟩ := ZMod.intCast_surjective (h 0 1)
  have h11 : h 1 1 = 1 := by
    have hdet := h.det_coe
    rw [det_fin_two] at hdet
    rw [h00, h10] at hdet
    linear_combination hdet
  refine ⟨transvection (by decide : (0 : Fin 2) ≠ 1) t₀, ?_⟩
  ext i j
  simp only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom,
    transvection_coe]
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h11, ht₀]

/-- **Strong approximation for `SL₂` over `ℤ`**: the reduction map `SL₂(ℤ) → SL₂(ℤ/dℤ)` is
surjective. -/
theorem map_intCast_zmod_surjective :
    Function.Surjective (SpecialLinearGroup.map (Int.castRingHom (ZMod d)) :
      SpecialLinearGroup (Fin 2) ℤ →* SpecialLinearGroup (Fin 2) (ZMod d)) := by
  intro g
  obtain ⟨a₀, c₀, ha₀, hc₀, hcop⟩ := (g.isCoprime_col 0).exists_int_lifts
  obtain ⟨σ, hσ0, hσ1⟩ := hcop.exists_SL2_col (0 : Fin 2)
  set M := SpecialLinearGroup.map (Int.castRingHom (ZMod d)) σ with hMdef
  have hentry : ∀ i j, M i j = ((σ i j : ℤ) : ZMod d) := fun i j => by
    rw [hMdef]
    simp only [map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, Int.coe_castRingHom]
  have hcol0 : M 0 0 = g 0 0 := by rw [hentry, hσ0, ha₀]
  have hcol1 : M 1 0 = g 1 0 := by rw [hentry, hσ1, hc₀]
  obtain ⟨τ, hτ⟩ := exists_map_eq_of_col_eq (M⁻¹ * g)
    (inv_mul_zero_zero_eq_one M g hcol0 hcol1) (inv_mul_one_zero_eq_zero M g hcol0 hcol1)
  exact ⟨σ * τ, by rw [map_mul, ← hMdef, hτ, mul_inv_cancel_left]⟩

end Matrix.SpecialLinearGroup
