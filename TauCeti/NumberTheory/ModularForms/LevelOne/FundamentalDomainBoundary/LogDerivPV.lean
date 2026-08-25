/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Modular
public import TauCeti.Analysis.Contour.Argument.CyclePV
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Immersion

import TauCeti.Analysis.Contour.NullHomologous
import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Winding.Basic

/-!
# The logarithmic integral along the boundary contour

The argument principle read on the boundary of the truncated fundamental domain. For a function
analytic and non-vanishing off a finite set `S`, the Cauchy principal value of its logarithmic
integral along `fdBoundary H` is `2πi` times the winding-weighted sum of its orders.

This is the on-contour counterpart of
`TauCeti.ModularForm.hasCauchyPV_fdBoundary_residue_sum`, which takes the poles to lie strictly
inside the truncated domain and so meets the contour nowhere. Here `S` may contain points of the
contour itself — as it must for the valence formula, whose elliptic points `i` and `ρ` lie on the
boundary — and the weights are then the generalized, non-integer winding numbers.

The contour hypotheses of the general theorem are discharged from the merged geometry of
`fdBoundary`: it is a closed piecewise-`C¹` immersion, null-homologous in any open set containing
the truncated domain, and its basepoint `fdBoundary H 0 = 1/2 + H·i` is a ceiling point.

## Main declarations

* `TauCeti.ModularForm.hasCauchyPV_fdBoundary_logDeriv`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development this file ports onto the current Mathlib pin.
-/

public section

open Complex Set TauCeti.Contour

namespace TauCeti

namespace ModularForm

variable {H : ℝ}

/-- **The logarithmic integral along the boundary contour.** For `f` analytic and non-vanishing on
an open `U` off a finite `S`, meromorphic of order `ord` at each point of `S` lying in `U`, with
`U` containing the truncated fundamental domain and the contour's basepoint off `S`, the Cauchy
principal value of the logarithmic integral along `fdBoundary H` is
`2πi · Σ_{z ∈ S} n_z(fdBoundary H) · ord z`.

Unlike `TauCeti.ModularForm.hasCauchyPV_fdBoundary_residue_sum`, the set `S` is free to meet the
contour; the winding numbers then need not be integers. -/
theorem hasCauchyPV_fdBoundary_logDeriv (hH : 1 ≤ H) {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}
    {ord : ℂ → ℤ} (hU : IsOpen U)
    (hUdom : UpperHalfPlane.coe '' ModularGroup.truncatedFundamentalDomain H ⊆ U)
    (hoff : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt f s)
    (hord : ∀ s ∈ S, s ∈ U → meromorphicOrderAt f s = (ord s : WithTop ℤ))
    (hbase : fdBoundary H 0 ∉ (S : Set ℂ)) :
    HasCauchyPV (fdBoundary H) 0 5 (logDeriv f)
      (2 * (Real.pi : ℂ) * Complex.I *
        ∑ z ∈ S, windingNumber (fdBoundary H) 0 5 z * (ord z : ℂ)) := by
  have hne : H ≠ Real.sqrt 3 / 2 := ne_of_gt (sqrt_three_div_two_lt_one.trans_le hH)
  exact hasCauchyPV_logDeriv_nullHomologous hU hoff hmero hord
    (isPwC1ImmersionOn_fdBoundary hne)
    (fun t ht => hUdom (fdBoundary_mem_coe_truncatedFundamentalDomain hH
      (by rwa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] at ht)))
    (fdBoundary_closed H).symm hbase ((isNullHomologous_fdBoundary hH).mono hUdom)

end ModularForm

end TauCeti

end
