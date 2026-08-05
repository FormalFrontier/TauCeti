/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Modular-forms basics: extensions of Mathlib's API

Small generic lemmas extending `Mathlib/NumberTheory/ModularForms/Basic.lean` and its slash
actions: the conjugation `σ` is trivial on `SL(2, ℤ)`-matrices, the `CuspForm`
translation equations Mathlib does not yet provide (`CuspForm.mcast_apply` and the
`GL(2, ℝ)`-level `CuspForm.coe_translate_gl`), and the weight-`k` slash action of `-I`
(`ModularForm.slash_neg_one`), the source of every parity constraint on weights and
nebentypus characters.

Split out of the diamond-operator development ported from the AINTLIB `LeanModularForms`
project (<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>).
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane

open scoped MatrixGroups ModularForm

/-- The slash-action conjugation `σ` is the identity for matrices coming from
`SL₂(ℤ)`: their determinant is `1 > 0`, so the `σ` branch picks `ContinuousAlgEquiv.refl ℝ ℂ`. -/
@[simp]
lemma σ_mapGL_real_eq_refl (s : SL(2, ℤ)) :
    UpperHalfPlane.σ (mapGL ℝ s) = ContinuousAlgEquiv.refl ℝ ℂ := by
  simp [UpperHalfPlane.σ, SpecialLinearGroup.mapGL]

/-- `CuspForm.mcast` does not change the pointwise values of a cusp form: the `CuspForm`
analogue of Mathlib's `ModularForm.mcast_apply`, which Mathlib does not yet provide. -/
lemma _root_.CuspForm.mcast_apply {a b : ℤ} {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : a = b)
    (f : CuspForm Γ a) (hΓ : Γ' = Γ := by rfl) (z : ℍ) : CuspForm.mcast h f hΓ z = f z := (rfl)

/-- `GL(2, ℝ)`-level coercion lemma for `CuspForm.translate`; Mathlib's
`CuspForm.coe_translate` is specialized to `SL(2, ℤ)` arguments. -/
@[simp]
lemma _root_.CuspForm.coe_translate_gl {F : Type*} [FunLike F UpperHalfPlane ℂ] {k : ℤ}
    {Γ : Subgroup (GL (Fin 2) ℝ)} [CuspFormClass F Γ k] (f : F) (g : GL (Fin 2) ℝ) :
    ⇑(CuspForm.translate f g) = ⇑f ∣[k] g := (rfl)

/-- The weight-`k` slash action of `-I` is multiplication by `(-1) ^ k`: `-I` acts trivially
on `ℍ` and has determinant `1`, so the only surviving factor is its automorphy factor
`denom (-I) z ^ (-k) = (-1) ^ (-k) = (-1) ^ k`.

This is the source of every parity constraint on weights and nebentypus characters. -/
@[simp]
theorem _root_.ModularForm.slash_neg_one (k : ℤ) (f : ℍ → ℂ) :
    f ∣[k] (-1 : GL (Fin 2) ℝ) = (-1 : ℂ) ^ k • f := by
  have hzpow : (-1 : ℂ) ^ (-k) = (-1 : ℂ) ^ k := by
    rw [zpow_neg, ← inv_zpow]
    norm_num
  have hdet : (-1 : GL (Fin 2) ℝ).det = 1 := by
    ext
    simp [Matrix.det_neg]
  funext z
  rw [ModularForm.slash_apply]
  simp [UpperHalfPlane.σ, hzpow, hdet, mul_comm]

