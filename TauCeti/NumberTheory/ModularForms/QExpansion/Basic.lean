/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The `q`-expansion as a linear map

The `q`-expansion of modular forms for a determinant-one subgroup of `GL(2, ℝ)`, bundled as
a `ℂ`-linear map into power series, refining Mathlib's additive `ModularForm.qExpansionAddHom`.

## Main declarations

* `TauCeti.ModularForm.qExpansionLinearMap`.

## References

* [Mathlib PR #39000](https://github.com/leanprover-community/mathlib4/pull/39000)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public noncomputable section

open UpperHalfPlane

namespace TauCeti

variable {h : ℝ}

/-- The `q`-expansion map as a `ℂ`-linear map to power series over `ℂ`, refining the additive
`ModularForm.qExpansionAddHom`. -/
def ModularForm.qExpansionLinearMap {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (k : ℤ) :
    ModularForm Γ k →ₗ[ℂ] PowerSeries ℂ where
  toAddHom := (_root_.ModularForm.qExpansionAddHom hh hΓ k).toAddHom
  map_smul' a f := _root_.ModularForm.qExpansion_smul hh hΓ a f

@[simp]
lemma ModularForm.qExpansionLinearMap_apply {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) {k : ℤ} (f : ModularForm Γ k) :
    ModularForm.qExpansionLinearMap hh hΓ k f = qExpansion h f := by
  unfold ModularForm.qExpansionLinearMap
  rfl

end TauCeti

end
