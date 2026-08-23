/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Modular
public import TauCeti.Analysis.Contour.Residue.Assembly
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import TauCeti.Analysis.Contour.NullHomologous
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Immersion
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Interior
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.Basic

/-!
# The residue sum along the boundary contour

The Hungerbühler–Wasem residue sum, instantiated on the boundary contour of the truncated
fundamental domain: for a function with a polar-part decomposition whose poles all lie in
the open truncated domain, the principal value of the contour integral is `-2πi` times the
sum of the residues — the contour winds `-1` about every interior point, and the corner
conditions of the general theorem hold vacuously because the contour avoids the poles.

This is the contour side of the valence formula: applied to the logarithmic derivative of
a modular form, the residues become the orders of its zeros.

## Main declarations

* `TauCeti.ModularForm.hasCauchyPV_fdBoundary_residue_sum`.

## References

The truncated-contour strategy follows the fundamental-domain boundary development of
AINTLIB's `LeanModularForms` (`ForMathlib/FDBoundary.lean`, `FDBoundaryH.lean`,
`FDBoundaryPath.lean`); the residue machinery is Tau Ceti's Hungerbühler–Wasem
development.
-/

public section

open Set TauCeti.Contour UpperHalfPlane

namespace TauCeti

namespace ModularForm

variable {H : ℝ}

/-- The truncation height dominates the corner row. -/
private lemma sqrt_three_div_two_lt_of_one_lt (hH : 1 < H) : Real.sqrt 3 / 2 < H :=
  sqrt_three_div_two_lt_one.trans hH

/-- **The residue sum along the boundary contour.** For a function with a polar-part
decomposition on an open set containing the closed truncated fundamental domain, all of
whose poles lie in the open truncated domain, the principal value of the contour integral
is `-2πi` times the sum of the residues: the contour winds `-1` about every pole. -/
theorem hasCauchyPV_fdBoundary_residue_sum (hH : 1 < H) {f : ℂ → ℂ} {S : Finset ℂ}
    {U : Set ℂ} (decomp : PolarPartDecomposition f S U) (hU : IsOpen U)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hS : ∀ s ∈ S, 1 < ‖s‖ ∧ |s.re| < 1 / 2 ∧ 0 < s.im ∧ s.im < H) :
    HasCauchyPV (fdBoundary H) 0 5 f
      (-(2 * (Real.pi : ℂ) * Complex.I) * ∑ s ∈ S, residue f s) := by
  have hne : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary H t ≠ s := fun s hs =>
    fdBoundary_ne_of_abs_re_lt_half_of_one_lt_norm_of_im_lt (hS s hs).2.1 (hS s hs).1
      (hS s hs).2.2.2
  have key := decomp.hasCauchyPV_residue_sum hU
    (isPwC1ImmersionOn_fdBoundary (ne_of_gt (sqrt_three_div_two_lt_of_one_lt hH)))
    (by norm_num : (0 : ℝ) ≤ 5) (fdBoundary_closed H).symm
    (fun t ht => hUdom (fdBoundary_mem_coe_truncatedFundamentalDomain hH.le
      (by rwa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at ht)))
    ((isNullHomologous_fdBoundary hH.le).mono hUdom)
    (fun s t ht heq => absurd heq (hne s s.2 t ht))
    (fun s k _ _ t ht heq => absurd heq (hne s s.2 t ht))
    (fun s k _ _ t ht heq => absurd heq (hne s s.2 t ht))
  have hsum : ∑ s ∈ S, windingNumber (fdBoundary H) 0 5 s * residue f s =
      -∑ s ∈ S, residue f s := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [windingNumber_fdBoundary_eq_neg_one_of_interior hH (hS s hs).1 (hS s hs).2.1
      (hS s hs).2.2.1 (hS s hs).2.2.2]
    ring
  rw [hsum] at key
  convert key using 1
  ring

end ModularForm

end TauCeti

end
