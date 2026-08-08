/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# Modular forms of non-positive weight

The two base cases of the dimension formulas. For an arithmetic group `𝒢`, Mathlib's norm map
gives that a modular form of negative weight vanishes
(`ModularForm.isZero_of_neg_weight`) and that one of weight `0` is constant
(`ModularForm.eq_const_of_weight_zero`). This file draws the linear-algebra consequences:
`M_k(𝒢)` is the zero space for `k < 0`, and evaluation at any point identifies `M_0(𝒢)` with
`ℂ`, so it is one-dimensional.

These are the cases the weight induction in the dimension formulas bottoms out at.

## Main results

* `ModularForm.subsingleton_of_neg_weight`, `ModularForm.finiteDimensional_of_neg_weight`:
  `M_k(𝒢) = 0` for `k < 0`.
* `ModularForm.evalEquiv`: evaluation at a point, as a linear equivalence `M_0(𝒢) ≃ₗ[ℂ] ℂ`.
* `ModularForm.finrank_weight_zero`: `dim M_0(𝒢) = 1`.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/Modularforms/DimGenCongLevels/Basic.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), stated for an
arithmetic subgroup of `GL(2, ℝ)` rather than a finite-index subgroup of `SL(2, ℤ)` — the
generality Mathlib's `NormTrace` results are already in — and with the weight-zero
identification exposed as an equivalence instead of being used only inside the proof.
-/

public section

open UpperHalfPlane

open scoped MatrixGroups

namespace ModularForm

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)}

/-- There are no nonzero modular forms of negative weight. -/
theorem subsingleton_of_neg_weight [𝒢.IsArithmetic] {k : ℤ} (hk : k < 0) :
    Subsingleton (ModularForm 𝒢 k) :=
  ⟨fun f g ↦ by rw [isZero_of_neg_weight hk f, isZero_of_neg_weight hk g]⟩

/-- Modular forms of negative weight form a finite-dimensional space — the zero space. -/
theorem finiteDimensional_of_neg_weight [𝒢.IsArithmetic] [𝒢.HasDetOne] {k : ℤ} (hk : k < 0) :
    FiniteDimensional ℂ (ModularForm 𝒢 k) :=
  have := subsingleton_of_neg_weight (𝒢 := 𝒢) hk
  inferInstance

/-- A weight-zero modular form is determined by its value at any single point, since it is
constant. -/
theorem eq_of_apply_eq [𝒢.IsArithmetic] {f g : ModularForm 𝒢 0} {τ : ℍ} (h : f τ = g τ) :
    f = g := by
  obtain ⟨c, hc⟩ := eq_const_of_weight_zero f
  obtain ⟨d, hd⟩ := eq_const_of_weight_zero g
  have : c = d := by
    simpa [hc, hd] using h
  ext z
  simp [hc, hd, this]

/-- **Evaluation at a point identifies the weight-zero forms with `ℂ`**: a weight-zero modular
form is constant, so evaluating it anywhere loses nothing, and every scalar is attained by the
corresponding constant form. -/
noncomputable def evalEquiv [𝒢.IsArithmetic] [𝒢.HasDetOne] (τ : ℍ) :
    ModularForm 𝒢 0 ≃ₗ[ℂ] ℂ where
  toFun f := f τ
  invFun c := const (Γ := 𝒢) c
  left_inv f := eq_of_apply_eq (τ := τ) (by simp)
  right_inv _ := by simp
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- The equivalence evaluates a form at the chosen point. -/
@[simp]
theorem evalEquiv_apply [𝒢.IsArithmetic] [𝒢.HasDetOne] (τ : ℍ) (f : ModularForm 𝒢 0) :
    evalEquiv (𝒢 := 𝒢) τ f = f τ := (rfl)

/-- The inverse of the equivalence is the constant form. -/
@[simp]
theorem evalEquiv_symm_apply [𝒢.IsArithmetic] [𝒢.HasDetOne] (τ : ℍ) (c : ℂ) :
    (evalEquiv (𝒢 := 𝒢) τ).symm c = const c := (rfl)

/-- Modular forms of weight `0` form a finite-dimensional space. -/
theorem finiteDimensional_weight_zero [𝒢.IsArithmetic] [𝒢.HasDetOne] :
    FiniteDimensional ℂ (ModularForm 𝒢 (0 : ℤ)) :=
  (evalEquiv (𝒢 := 𝒢) I).symm.finiteDimensional

/-- The weight-zero modular forms are one-dimensional: they are exactly the constants. -/
theorem finrank_weight_zero [𝒢.IsArithmetic] [𝒢.HasDetOne] :
    Module.finrank ℂ (ModularForm 𝒢 (0 : ℤ)) = 1 := by
  rw [(evalEquiv (𝒢 := 𝒢) I).finrank_eq, Module.finrank_self]

end ModularForm
