/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms

/-!
# The `S`-transformation of the complex extension of a slash-invariant form

For a weight-`k` slash-invariant form `f` whose group contains `S = !![0, -1; 1, 0]`, the
transformation law `f (S • τ) = τ ^ k * f τ` transports through `ofComplex` to the
identity `(⇑f ∘ ofComplex) (-1 / w) = w ^ k * (⇑f ∘ ofComplex) w` on the open upper
half-plane. Differentiability of the extension transports across the `S`-orbit through
the same identity, and differentiating it expresses the logarithmic derivative at `w`
through the logarithmic derivative at `-1 / w` up to the weight term `k / w` — the
integrand identity behind the arc self-pairing of the valence-formula contour integral.

## Main declarations

* `TauCeti.ModularForm.comp_ofComplex_S_transform`: the `S`-transformation law of
  `⇑f ∘ ofComplex`.
* `TauCeti.ModularForm.differentiableAt_comp_ofComplex_S_transform`: differentiability
  transports across the `S`-orbit.
* `TauCeti.ModularForm.logDeriv_comp_ofComplex_S_transform`: the `S`-transformation law
  of the logarithmic derivative.
-/

public section

open Complex UpperHalfPlane

open scoped MatrixGroups

namespace TauCeti

namespace ModularForm

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

/-- The `S`-transformation law of the complex extension of a slash-invariant form, at the
points of the open upper half-plane. -/
theorem comp_ofComplex_S_transform [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {w : ℂ} (hw : 0 < w.im) :
    (⇑f ∘ ofComplex) (-1 / w) = w ^ k * (⇑f ∘ ofComplex) w := by
  have him : 0 < (-1 / w).im := by
    simpa [neg_div, one_div, inv_neg] using (⟨w, hw⟩ : ℍ).im_inv_neg_coe_pos
  have hSw : ModularGroup.S • (⟨w, hw⟩ : ℍ) = (⟨-1 / w, him⟩ : ℍ) := by
    rw [modular_S_smul]
    exact UpperHalfPlane.ext (by simp [neg_div, inv_neg])
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos him,
    ofComplex_apply_of_im_pos hw]
  rw [← hSw, SlashInvariantForm.slash_action_eqn_SL'' f hS, ModularGroup.denom_S]

/-- Differentiability of the complex extension of a slash-invariant form transports
across the `S`-orbit. -/
theorem differentiableAt_comp_ofComplex_S_transform [SlashInvariantFormClass F Γ k]
    (f : F) (hS : ModularGroup.S ∈ Γ) {w : ℂ} (hw : 0 < w.im)
    (hd : DifferentiableAt ℂ (⇑f ∘ ofComplex) w) :
    DifferentiableAt ℂ (⇑f ∘ ofComplex) (-1 / w) := by
  have him : 0 < (-1 / w).im := by
    simpa [neg_div, one_div, inv_neg] using (⟨w, hw⟩ : ℍ).im_inv_neg_coe_pos
  have hiw0 : (-1 : ℂ) / w ≠ 0 := fun h ↦ absurd him (by simp [h])
  have hrw : (-1 : ℂ) / (-1 / w) = w := by
    field_simp
  have hcomp : DifferentiableAt ℂ (fun v : ℂ ↦ (⇑f ∘ ofComplex) (-1 / v)) (-1 / w) :=
    (hrw ▸ hd).comp _ ((differentiableAt_const _).div differentiableAt_id hiw0)
  have heq : (⇑f ∘ ofComplex) =ᶠ[nhds (-1 / w)]
      fun v ↦ (⇑f ∘ ofComplex) (-1 / v) / v ^ k := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds him] with v hv
    have hv0 : v ≠ 0 := fun h ↦ absurd hv (by simp [h])
    rw [comp_ofComplex_S_transform f hS hv,
      mul_div_cancel_left₀ _ (zpow_ne_zero k hv0)]
  exact ((hcomp.div (differentiableAt_zpow.mpr (.inl hiw0))
    (zpow_ne_zero k hiw0))).congr_of_eventuallyEq heq

/-- The `S`-transformation law of the logarithmic derivative of the complex extension of
a slash-invariant form, at points of the open upper half-plane where the extension is
differentiable and does not vanish. -/
theorem logDeriv_comp_ofComplex_S_transform [SlashInvariantFormClass F Γ k] (f : F)
    (hS : ModularGroup.S ∈ Γ) {w : ℂ} (hw : 0 < w.im)
    (hd : DifferentiableAt ℂ (⇑f ∘ ofComplex) w) (hfw : (⇑f ∘ ofComplex) w ≠ 0) :
    logDeriv (⇑f ∘ ofComplex) w =
      logDeriv (⇑f ∘ ofComplex) (-1 / w) / w ^ 2 - k / w := by
  have hw0 : w ≠ 0 := fun h ↦ absurd hw (by simp [h])
  have him : 0 < (-1 / w).im := by
    simpa [neg_div, one_div, inv_neg] using (⟨w, hw⟩ : ℍ).im_inv_neg_coe_pos
  have h_eq_nhd : (fun v ↦ (⇑f ∘ ofComplex) (-1 / v)) =ᶠ[nhds w]
      fun v ↦ v ^ k * (⇑f ∘ ofComplex) v := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with v hv
    exact comp_ofComplex_S_transform f hS hv
  have h_comp : logDeriv (fun v ↦ (⇑f ∘ ofComplex) (-1 / v)) w =
      logDeriv (⇑f ∘ ofComplex) (-1 / w) * deriv (fun v ↦ -1 / v) w :=
    logDeriv_comp (differentiableAt_comp_ofComplex_S_transform f hS hw hd)
      ((differentiableAt_const _).div differentiableAt_id hw0)
  have h_deriv_S : deriv (fun v : ℂ ↦ -1 / v) w = 1 / w ^ 2 := by
    simp only [div_eq_mul_inv]
    rw [deriv_const_mul_field, deriv_inv]
    ring
  have h_mul : logDeriv (fun v ↦ v ^ k * (⇑f ∘ ofComplex) v) w =
      logDeriv (· ^ k) w + logDeriv (⇑f ∘ ofComplex) w :=
    logDeriv_mul w (zpow_ne_zero k hw0) hfw
      (differentiableAt_zpow.mpr (.inl hw0)) hd
  have h_eq : logDeriv (fun v ↦ (⇑f ∘ ofComplex) (-1 / v)) w =
      logDeriv (fun v ↦ v ^ k * (⇑f ∘ ofComplex) v) w := by
    simp only [logDeriv_apply]
    rw [h_eq_nhd.eq_of_nhds, h_eq_nhd.deriv.eq_of_nhds]
  rw [h_eq, h_mul, logDeriv_zpow w k, h_deriv_S] at h_comp
  linear_combination h_comp

end ModularForm

end TauCeti

end
