/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.On
public import TauCeti.Analysis.Contour.PolarPart.Decomposition
public import TauCeti.Analysis.Contour.PwC1ImmersionOn
public import TauCeti.Analysis.Contour.RegularityConditions
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import TauCeti.Analysis.Contour.PolarPart.CPV

/-!
# Assembling the generalized residue sum

The engine of the Hungerbühler–Wasem generalized residue theorem, over an explicit polar
decomposition: along a **closed, null-homologous** piecewise-`C¹` immersion in `U` whose
crossings of each pole are interior and (at every surviving higher-order coefficient) flat and
sector-compatible, the set-level Cauchy principal value of `f` exists and equals
`2πi · Σ_{s ∈ S} n_s(γ) · Res_s f`. The analytic remainder integrates to zero around the
null-homologous cycle (the homology Cauchy theorem through the decomposition), each polar part
contributes its winding-weighted residue, the contributions add across the singular set, and
`f` is identified with the assembled sum along the curve away from the poles — which is all
the excised principal value sees.

## Main results

* `Contour.PolarPartDecomposition.hasCauchyPV_residue_sum` — the set-level principal value of
  `f` along the cycle is `2πi · Σ_{s ∈ S} n_s(γ) · Res_s f`.

## Provenance

Migrated from `residueTheorem_crossing_compositional` of `Crossing.lean` in the AINTLIB
`LeanModularForms` development (there taking the per-pole principal values as data; here they
are produced by the polar-part theorem). See N. Hungerbühler, M. Wasem, *Non-integer valued
winding numbers and a generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

namespace PolarPartDecomposition

open Filter Set Topology

/-- **The generalized residue sum over a polar decomposition**: along a closed,
null-homologous piecewise-`C¹` immersion in `U` whose crossings of each pole are interior and
gated-flat and gated-sector-compatible, the set-level principal value of `f` is
`2πi · Σ_{s ∈ S} n_s(γ) · Res_s f`. -/
theorem hasCauchyPV_residue_sum {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}
    (decomp : PolarPartDecomposition f S U) (hU : IsOpen U)
    {γ : ℝ → ℂ} {a b : ℝ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b)
    (hclosed : γ a = γ b) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hnull : IsNullHomologous γ a b U)
    (h_interior : ∀ s : S, ∀ t ∈ Icc a b, γ t = (s : ℂ) → t ∈ Ioo a b)
    (h_flat : ∀ s : S, ∀ k : Fin (decomp.order s), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∀ t ∈ Icc a b, γ t = (s : ℂ) → FlatOfOrder γ t (k.val + 1))
    (h_B : ∀ s : S, ∀ k : Fin (decomp.order s), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∀ t ∈ Icc a b, γ t = (s : ℂ) → ∀ L_R L_L : ℂ,
        Tendsto (deriv γ) (𝓝[>] t) (𝓝 L_R) → Tendsto (deriv γ) (𝓝[<] t) (𝓝 L_L) →
        (L_R / (‖L_R‖ : ℂ)) ^ k.val = ((-L_L) / (‖L_L‖ : ℂ)) ^ k.val) :
    HasCauchyPV γ a b f
      (2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber γ a b s * residue f s) := by
  classical
  have h_rem_int : IntervalIntegrable
      (fun t => decomp.analyticRemainder (γ t) * deriv γ t) MeasureTheory.volume a b :=
    h_imm.isPiecewiseC1On.intervalIntegrable_deriv.continuousOn_mul
      (decomp.analyticRemainder_differentiableOn.continuousOn.comp h_imm.continuousOn hγU)
  have h_rem : HasCauchyPV γ a b decomp.analyticRemainder 0 := by
    have h0 := HasCauchyPV.of_integrable h_rem_int
    rwa [show (∫ t in a..b, decomp.analyticRemainder (γ t) * deriv γ t) = 0 from by
      rw [← decomp.intervalIntegral_deriv_smul_analyticRemainder_eq_zero hU
        h_imm.isPiecewiseC1On hγU hclosed hnull]
      exact intervalIntegral.integral_congr fun t _ => by rw [smul_eq_mul, mul_comm]] at h0
  have h_polar : ∀ s ∈ S.attach, HasCauchyPV γ a b (decomp.polarPart s)
      (2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b ↑s * residue f ↑s) := fun s _ =>
    (decomp.hasCauchyPVAt_polarPart s h_imm hab hclosed (h_interior s) (h_flat s)
      (h_B s)).hasCauchyPV
  have h_sum := h_rem.add h_imm.continuousOn (HasCauchyPV.sum h_imm.continuousOn h_polar)
  have h_total := h_sum.congr_along_curve_off h_imm.continuousOn S fun t ht h_off =>
    (decomp.f_eq (γ t) ⟨hγU t (uIoo_subset_uIcc_self ht), h_off⟩).symm
  have h_val : (0 : ℂ) + ∑ s ∈ S.attach,
      2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b ↑s * residue f ↑s
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber γ a b s * residue f s := by
    rw [zero_add, Finset.mul_sum, ← Finset.sum_attach S
      fun s => 2 * (Real.pi : ℂ) * Complex.I * (windingNumber γ a b s * residue f s)]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [← h_val]
  exact h_total

end PolarPartDecomposition

end TauCeti.Contour

end
