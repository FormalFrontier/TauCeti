/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Affine
import Mathlib.Analysis.Calculus.Deriv.Linear
import TauCeti.MeasureTheory.Integral.OddSymmetric

/-!
# The generalized winding number of a straight segment through the point

A straight segment traversed symmetrically **through** its reference point contributes nothing to
the generalized winding number about that point. The mechanism is oddness: for the real inclusion
`γ t = t` on `[-R, R]`, the index integrand `γ̇ t / (γ t - 0) = 1 / t` is odd, so every
`ε`-truncated integral over the symmetric interval vanishes *identically* — not merely in the
limit — and the principal value is `0` with no limiting argument at all. The general segment
`γ t = v · t + z₀` about `z₀` then follows by transporting along the affine change of coordinates
of `Winding/Number/Affine.lean`; the degenerate direction `v = 0` (the constant curve at `z₀`) is
included, since there every positive-radius truncation is identically zero.

This is the on-curve counterpart of the arc computations in `Winding/Number/Circle.lean`,
which compute the winding of an
arc about its *centre*, a point off the curve. Together they supply the two pieces of an indented
contour: a diameter through the singularity contributes `0`, and the semicircular arc about it
contributes `½` (`windingNumber_at_i`) — the `windingNumber = 1/2` input of the
Hungerbühler–Wasem half-residue theorem `hasCauchyPV_half_residue`.

## Main results

* `TauCeti.Contour.hasCauchyPVAt_inv_sub_segment`,
  `TauCeti.Contour.cauchyPVExistsAt_inv_sub_segment` and
  `TauCeti.Contour.windingNumber_eq_zero_segment` — an arbitrary straight segment `v · t + z₀`
  traversed symmetrically through `z₀` has index principal value and winding number `0` about
  `z₀`. The real-axis case through the origin is the private base case from which the general
  one is transported.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Complex Filter Topology MeasureTheory

namespace TauCeti.Contour

/-- The `ε`-truncated index integrand of the real segment through the origin is odd. -/
private theorem truncated_inv_ofReal_odd (ε : ℝ) :
    Function.Odd (fun t : ℝ =>
      if ‖((t : ℝ) : ℂ) - 0‖ > ε then ((((t : ℝ) : ℂ) - 0)⁻¹ * (1 : ℂ)) else 0) := by
  intro t
  have hnorm : ‖((-t : ℝ) : ℂ) - 0‖ = ‖((t : ℝ) : ℂ) - 0‖ := by
    simp [Complex.norm_real]
  simp only [hnorm]
  split_ifs <;> simp

/-- Every `ε`-truncated index integral of the real segment through the origin vanishes. -/
private theorem integral_truncated_inv_ofReal (R ε : ℝ) :
    ∫ t in (-R)..R, (if ‖(Complex.ofRealCLM t) - 0‖ > ε then
      ((Complex.ofRealCLM t) - 0)⁻¹ * deriv (⇑Complex.ofRealCLM) t else 0) = 0 := by
  refine intervalIntegral.integral_eq_zero_of_odd (fun t => ?_) R
  simpa [Complex.ofRealCLM.deriv, Complex.ofRealCLM_apply]
    using truncated_inv_ofReal_odd ε t

/-- **The real segment through the origin has vanishing index principal value.** The index
integrand `1 / t` is odd, so every truncated integral over `[-R, R]` is `0`, and the principal
value of `∫_γ dz / z` along the segment exists with value `0`. -/
private theorem hasCauchyPVAt_inv_sub_ofReal (R : ℝ) :
    HasCauchyPVAt (⇑Complex.ofRealCLM) (-R) R (fun z => (z - 0)⁻¹) 0 0 := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine intervalIntegrable_truncated_mul_deriv (γ := ⇑Complex.ofRealCLM)
      (f := fun z : ℂ => (z - 0)⁻¹) (z₀ := 0) (M := ε⁻¹) ?_ ?_ ?_
    · simp [Complex.ofRealCLM.deriv, Complex.ofRealCLM_apply]
    · simp only [Complex.ofRealCLM.deriv, Complex.ofRealCLM_apply]
      refine (Measurable.ite ?_ ?_ measurable_const).aestronglyMeasurable
      · exact measurableSet_lt measurable_const (by fun_prop)
      · fun_prop
    · intro t ht
      rw [norm_inv]
      gcongr
  · simp_rw [integral_truncated_inv_ofReal R]
    exact tendsto_const_nhds

/-- **A straight segment through its reference point has vanishing index principal value.** The
segment `γ t = v · t + z₀` traversed over the symmetric interval `[-R, R]` passes through `z₀` at
`t = 0`, and the principal value of `∫_γ dz / (z - z₀)` along it is `0`. For `v ≠ 0` this is the
real-axis case transported by the affine change of coordinates; for `v = 0` the curve is constant
at `z₀`, so every positive-radius truncation is identically zero. -/
theorem hasCauchyPVAt_inv_sub_segment (v z₀ : ℂ) (R : ℝ) :
    HasCauchyPVAt (fun t : ℝ => v * (t : ℂ) + z₀) (-R) R (fun z => (z - z₀)⁻¹) z₀ 0 := by
  rcases eq_or_ne v 0 with rfl | hv
  · refine HasCauchyPVAt.intro ?_ ?_ <;> simp
  · simpa using hasCauchyPVAt_inv_sub_affine (d := z₀) (hasCauchyPVAt_inv_sub_ofReal R) hv

/-- Existence form of `hasCauchyPVAt_inv_sub_segment`, matching the existence-form API of the
adjacent scaling and affine coordinate changes. -/
theorem cauchyPVExistsAt_inv_sub_segment (v z₀ : ℂ) (R : ℝ) :
    CauchyPVExistsAt (fun t : ℝ => v * (t : ℂ) + z₀) (-R) R (fun z => (z - z₀)⁻¹) z₀ :=
  CauchyPVExistsAt.intro (hasCauchyPVAt_inv_sub_segment v z₀ R)

/-- **The winding number of a straight segment through its reference point vanishes.** -/
@[simp]
theorem windingNumber_eq_zero_segment (v z₀ : ℂ) (R : ℝ) :
    windingNumber (fun t : ℝ => v * (t : ℂ) + z₀) (-R) R z₀ = 0 := by
  rw [windingNumber_eq_of_hasCauchyPVAt (hasCauchyPVAt_inv_sub_segment v z₀ R)]
  ring

end TauCeti.Contour

end

end
