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
decomposition: along a **closed** piecewise-`C¹` immersion in `U` whose crossings of each pole
are interior and (at every surviving higher-order coefficient) flat and sector-compatible, the
set-level Cauchy principal value of `f` exists and equals the ordinary contour integral of the
analytic remainder plus `2πi · Σ_{s ∈ S} n_s(γ) · Res_s f`. Each polar part contributes its
winding-weighted residue, the contributions add across the singular set, and `f` is identified
with the assembled sum along the curve away from the poles — which is all the excised principal
value sees.

Null-homology enters only at the last step, where it makes the analytic remainder integrate to
zero (the homology Cauchy theorem through the decomposition). Keeping that step separate is
what lets a caller add several curves up before any of them bounds, as the cycle form of the
generalized residue theorem must.

## Main results

* `Contour.PolarPartDecomposition.hasCauchyPV_analyticRemainder_add_residue_sum` — the
  null-homology-free splitting: the principal value is the contour integral of the analytic
  remainder plus `2πi · Σ_{s ∈ S} n_s(γ) · Res_s f`.
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

/-- **The residue sum splits off the principal value over a polar decomposition**: along a
closed piecewise-`C¹` immersion in `U` whose crossings of each pole are interior and gated-flat
and gated-sector-compatible, the set-level principal value of `f` is the ordinary contour
integral of the analytic remainder plus `2πi · Σ_{s ∈ S} n_s(γ) · Res_s f`.

Nothing is assumed about null-homology, so the identity holds for a single immersion however it
winds around the holes of `U`. That is what makes it usable one rung lower down, where the
remainder is discharged only after the contributions of several curves have been added up: over
a formal cycle whose generators need not individually bound
(`TauCeti.Contour.Cycle.hungerbuhlerWasem_residueTheorem`). -/
theorem hasCauchyPV_analyticRemainder_add_residue_sum {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}
    (decomp : PolarPartDecomposition f S U)
    {γ : ℝ → ℂ} {a b : ℝ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b)
    (hclosed : γ a = γ b) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (h_interior : ∀ s : S, ∀ t ∈ Icc a b, γ t = (s : ℂ) → t ∈ Ioo a b)
    (h_flat : ∀ s : S, ∀ k : Fin (decomp.order s), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∀ t ∈ Icc a b, γ t = (s : ℂ) → FlatOfOrder γ t (k.val + 1))
    (h_B : ∀ s : S, ∀ k : Fin (decomp.order s), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∀ t ∈ Icc a b, γ t = (s : ℂ) → ∀ L_R L_L : ℂ,
        Tendsto (deriv γ) (𝓝[>] t) (𝓝 L_R) → Tendsto (deriv γ) (𝓝[<] t) (𝓝 L_L) →
        (L_R / (‖L_R‖ : ℂ)) ^ k.val = ((-L_L) / (‖L_L‖ : ℂ)) ^ k.val) :
    HasCauchyPV γ a b f
      ((∫ t in a..b, deriv γ t • decomp.analyticRemainder (γ t))
        + 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber γ a b s * residue f s) := by
  classical
  have h_rem_int : IntervalIntegrable
      (fun t => decomp.analyticRemainder (γ t) * deriv γ t) MeasureTheory.volume a b :=
    h_imm.isPiecewiseC1On.intervalIntegrable_deriv.continuousOn_mul
      (decomp.analyticRemainder_differentiableOn.continuousOn.comp h_imm.continuousOn hγU)
  have h_rem : HasCauchyPV γ a b decomp.analyticRemainder
      (∫ t in a..b, deriv γ t • decomp.analyticRemainder (γ t)) := by
    have h0 := HasCauchyPV.of_integrable h_rem_int
    convert h0 using 1
    exact intervalIntegral.integral_congr fun t _ => by rw [smul_eq_mul, mul_comm]
  have h_polar : ∀ s ∈ S.attach, HasCauchyPV γ a b (decomp.polarPart s)
      (2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b ↑s * residue f ↑s) := fun s _ =>
    (decomp.hasCauchyPVAt_polarPart s h_imm hab hclosed (h_interior s) (h_flat s)
      (h_B s)).hasCauchyPV
  have h_sum := h_rem.add h_imm.continuousOn (HasCauchyPV.sum h_imm.continuousOn h_polar)
  have h_total := h_sum.congr_along_curve_off h_imm.continuousOn S fun t ht h_off =>
    (decomp.f_eq (γ t) ⟨hγU t (uIoo_subset_uIcc_self ht), h_off⟩).symm
  have h_val : (∫ t in a..b, deriv γ t • decomp.analyticRemainder (γ t)) + ∑ s ∈ S.attach,
      2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b ↑s * residue f ↑s
      = (∫ t in a..b, deriv γ t • decomp.analyticRemainder (γ t))
        + 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber γ a b s * residue f s := by
    rw [Finset.mul_sum, ← Finset.sum_attach S
      fun s => 2 * (Real.pi : ℂ) * Complex.I * (windingNumber γ a b s * residue f s)]
    exact congrArg _ (Finset.sum_congr rfl fun s _ => by ring)
  rw [← h_val]
  exact h_total

/-- **The generalized residue sum over a polar decomposition**: along a closed,
null-homologous piecewise-`C¹` immersion in `U` whose crossings of each pole are interior and
gated-flat and gated-sector-compatible, the set-level principal value of `f` is
`2πi · Σ_{s ∈ S} n_s(γ) · Res_s f`.

The null-homology-free splitting
(`Contour.PolarPartDecomposition.hasCauchyPV_analyticRemainder_add_residue_sum`) with the
analytic remainder discharged by the homology Cauchy theorem. -/
theorem hasCauchyPV_residue_sum {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}
    (decomp : PolarPartDecomposition f S U) (hU : IsOpen U)
    {γ : ℝ → ℂ} {a b : ℝ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b)
    (hclosed : γ a = γ b) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hnull : IsNullHomologous γ a b U)
    (h_interior : ∀ s : S, ∀ t ∈ Icc a b, γ t = (s : ℂ) → t ∈ Ioo a b)
    (h_flat : ∀ s : S, ∀ k : Fin (decomp.order s), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∀ t ∈ Icc a b, γ t = (s : ℂ) → FlatOfOrder γ t (k.val + 1))
    (h_B : ∀ s : S, ∀ k : Fin (decomp.order s), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∀ t ∈ Icc a b, γ t = (s : ℂ) → ∀ L_R L_L : ℂ,
        Tendsto (deriv γ) (𝓝[>] t) (𝓝 L_R) → Tendsto (deriv γ) (𝓝[<] t) (𝓝 L_L) →
        (L_R / (‖L_R‖ : ℂ)) ^ k.val = ((-L_L) / (‖L_L‖ : ℂ)) ^ k.val) :
    HasCauchyPV γ a b f
      (2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber γ a b s * residue f s) := by
  have h := decomp.hasCauchyPV_analyticRemainder_add_residue_sum h_imm hab hclosed hγU
    h_interior h_flat h_B
  rwa [decomp.intervalIntegral_deriv_smul_analyticRemainder_eq_zero hU h_imm.isPiecewiseC1On
    hγU hclosed hnull, zero_add] at h

end PolarPartDecomposition

end TauCeti.Contour

end
