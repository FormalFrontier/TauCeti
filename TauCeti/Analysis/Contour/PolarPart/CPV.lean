/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Contour.PolarPart.Decomposition
public import TauCeti.Analysis.Contour.PwC1ImmersionOn
public import TauCeti.Analysis.Contour.RegularityConditions
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import TauCeti.Analysis.Contour.HigherOrder.CPV
import TauCeti.Analysis.Contour.InvSubCPVExistence

/-!
# The principal value of a polar part is the winding-weighted residue

For a piecewise-`C¹` immersed **closed** curve whose crossings of a pole `s ∈ S` are interior
and, at every surviving higher-order coefficient, flat and sector-compatible, the single-point
Cauchy principal value of the polar part of `f` at `s` along the curve is
`2πi · n_s(γ) · Res_s f` — the term `s` contributes
to the Hungerbühler–Wasem sum. The simple-pole coefficient contributes its winding-weighted
residue by the definitional identity `windingNumber = (2πi)⁻¹ · cauchyPVAt` together with the
existence theorem (`Contour.IsPwC1ImmersionOn.cauchyPVExistsAt_inv_sub`); every order-`k ≥ 2`
coefficient contributes zero around a closed curve
(`Contour.IsPwC1ImmersionOn.hasCauchyPVAt_pow_inv`); the finite Laurent sum assembles by
`ℂ`-linearity, and the leading coefficient is the residue
(`Contour.PolarPartDecomposition.residue_eq`).

## Main results

* `Contour.PolarPartDecomposition.hasCauchyPVAt_polarPart` — the single-point principal value
  of the polar part at `s` along a closed immersion is `2πi · windingNumber · residue`.

## Provenance

Migrated from `cpv_polarPart_at_multiCrossed_pole_under_condB_corner` of
`MultiCrossingCPV.lean` in the AINTLIB `LeanModularForms` development, restated for a raw
curve: the simple-pole principal value is derived from the immersion rather than assumed, and
the sector hypothesis quantifies over the one-sided derivative limits (which are unique)
instead of chosen tangent functions. See N. Hungerbühler, M. Wasem, *Non-integer valued
winding numbers and a generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

namespace PolarPartDecomposition

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}

/-- One Laurent term of the polar part: the simple-pole term carries the value
`coeff · cauchyPVAt` of the winding kernel, and every higher-order term carries zero around a
closed curve. -/
private theorem hasCauchyPVAt_polarPart_term (decomp : PolarPartDecomposition f S U) (s : S)
    {γ : ℝ → ℂ} {a b : ℝ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b)
    (hclosed : γ a = γ b)
    (h_interior : ∀ t ∈ Icc a b, γ t = (s : ℂ) → t ∈ Ioo a b)
    (h_flat : ∀ k : Fin (decomp.order s), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∀ t ∈ Icc a b, γ t = (s : ℂ) → FlatOfOrder γ t (k.val + 1))
    (h_B : ∀ k : Fin (decomp.order s), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∀ t ∈ Icc a b, γ t = (s : ℂ) → ∀ L_R L_L : ℂ,
        Tendsto (deriv γ) (𝓝[>] t) (𝓝 L_R) → Tendsto (deriv γ) (𝓝[<] t) (𝓝 L_L) →
        (L_R / (‖L_R‖ : ℂ)) ^ k.val = ((-L_L) / (‖L_L‖ : ℂ)) ^ k.val)
    (k : Fin (decomp.order s)) :
    HasCauchyPVAt γ a b (fun z => decomp.coeff s k / (z - (s : ℂ)) ^ (k.val + 1)) (s : ℂ)
      (if k.val = 0 then
        decomp.coeff s k * cauchyPVAt γ a b (fun z => (z - (s : ℂ))⁻¹) (s : ℂ) else 0) := by
  rcases Nat.eq_zero_or_pos k.val with hk0 | hk_pos
  · rw [if_pos hk0]
    refine (((h_imm.cauchyPVExistsAt_inv_sub hab
      h_interior).hasCauchyPVAt_cauchyPVAt).const_mul
        (decomp.coeff s k)).congr_along_curve fun t _ => ?_
    rw [hk0, zero_add, pow_one, div_eq_mul_inv]
  · rw [if_neg (Nat.pos_iff_ne_zero.mp hk_pos)]
    by_cases hc : decomp.coeff s k = 0
    · exact HasCauchyPVAt.zero.congr_along_curve fun t _ => by rw [hc, zero_div]
    · have h_vanish := h_imm.hasCauchyPVAt_pow_inv hab h_interior
        (Nat.succ_le_succ hk_pos) le_rfl (h_flat k hk_pos hc)
        (fun t ht h_eq => h_B k hk_pos hc t ht h_eq) (decomp.coeff s k)
      rwa [hclosed, sub_self] at h_vanish

/-- **The principal value of a polar part is the winding-weighted residue**: along a closed
piecewise-`C¹` immersion whose crossings of `s` are interior and, at every surviving
higher-order coefficient, flat and sector-compatible, the single-point Cauchy
principal value of `decomp.polarPart s` at `s` is `2πi · n_s(γ) · Res_s f`. The higher-order
coefficients contribute nothing — this is the term the Hungerbühler–Wasem sum attributes to
`s`. -/
theorem hasCauchyPVAt_polarPart (decomp : PolarPartDecomposition f S U) (s : S)
    {γ : ℝ → ℂ} {a b : ℝ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b)
    (hclosed : γ a = γ b)
    (h_interior : ∀ t ∈ Icc a b, γ t = (s : ℂ) → t ∈ Ioo a b)
    (h_flat : ∀ k : Fin (decomp.order s), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∀ t ∈ Icc a b, γ t = (s : ℂ) → FlatOfOrder γ t (k.val + 1))
    (h_B : ∀ k : Fin (decomp.order s), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∀ t ∈ Icc a b, γ t = (s : ℂ) → ∀ L_R L_L : ℂ,
        Tendsto (deriv γ) (𝓝[>] t) (𝓝 L_R) → Tendsto (deriv γ) (𝓝[<] t) (𝓝 L_L) →
        (L_R / (‖L_R‖ : ℂ)) ^ k.val = ((-L_L) / (‖L_L‖ : ℂ)) ^ k.val) :
    HasCauchyPVAt γ a b (decomp.polarPart s) (s : ℂ)
      (2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b s * residue f s) := by
  classical
  have h_sum := HasCauchyPVAt.sum (s := (Finset.univ : Finset (Fin (decomp.order s))))
    fun k _ =>
      hasCauchyPVAt_polarPart_term decomp s h_imm hab hclosed h_interior h_flat h_B k
  have h_pv := h_sum.congr_along_curve fun t _ => (decomp.polarPart_eq s (γ t)).symm
  have h_val : (∑ k : Fin (decomp.order s), if k.val = 0 then
        decomp.coeff s k * cauchyPVAt γ a b (fun z => (z - (s : ℂ))⁻¹) (s : ℂ) else 0)
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b s * residue f s := by
    rw [decomp.sum_ite_coeff_eq_residue_mul s, windingNumber_eq_cauchyPVAt, ← mul_assoc,
      mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
    ring
  rw [← h_val]
  exact h_pv

end PolarPartDecomposition

end TauCeti.Contour

end
