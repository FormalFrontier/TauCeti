/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic

/-!
# Finite partitions of contour winding numbers

This file upgrades the two-interval additivity of `Contour.windingNumber` to a finite partition
`t 0, ..., t n` of the parameter interval.  No monotonicity of `t` is needed: oriented interval
integrals, and hence their Cauchy principal values, telescope over arbitrary adjacent endpoints.

The finite form is the bookkeeping prerequisite for the winding decomposition in
Hungerbühler--Wasem Proposition 2.2.  There a closed immersed curve is replaced by a part avoiding
the distinguished point and finitely many model sectors, one for each crossing.  Once those pieces
are assembled on adjacent parameter intervals, the results here identify the winding number of the
whole curve with the sum of their winding numbers.  The geometric construction of those pieces is
separate; this file only proves the finite additivity it consumes.

As in `Winding.Number.Concat`, every statement carries principal-value existence.  Without it the
`limUnder`-based `windingNumber` is a junk value, so unconditional finite additivity would be false
as an API statement even though it looked formally convenient.

## Main results

* `Contour.windingNumber_eq_sum_range_of_hasCauchyPVAt` proves finite additivity from explicit
  principal-value witnesses on every adjacent interval.
* `Contour.windingNumber_eq_sum_range` uses the generic finite principal-value concatenation API
  to write a winding number as a sum over a finite partition.
* `Contour.windingNumber_eq_sum_range_of_ae` allows each piece to be computed using a different
  curve under the principal-value API's almost-everywhere curve and derivative hypotheses.
* `Contour.windingNumber_eq_sum_range_of_eqOn` allows each piece to be computed using a different
  curve that agrees with the assembled curve on that open subinterval.

## Provenance

This is routine finite-partition infrastructure around the generalized winding number; no formal
source is vendored.  Its role is prescribed by N. Hungerbühler and M. Wasem, *Non-integer valued
winding numbers and a generalized Residue Theorem*, arXiv:1808.00997, Proposition 2.2.
-/

public section

noncomputable section

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {z₀ : ℂ}

/-- The Cauchy kernel about `z₀`, used throughout the winding-number API. -/
local notation "κ[" z "]" => (fun w : ℂ => (w - z)⁻¹)

/-- **Finite-partition additivity from explicit principal-value witnesses.** If the Cauchy-kernel
principal value on every adjacent interval is `L k`, the winding number from `t 0` to `t n` is the
sum of the winding numbers of those pieces. -/
theorem windingNumber_eq_sum_range_of_hasCauchyPVAt {n : ℕ} {t : ℕ → ℝ} {L : ℕ → ℂ}
    (h : ∀ k < n, HasCauchyPVAt γ (t k) (t (k + 1)) κ[z₀] z₀ (L k)) :
    windingNumber γ (t 0) (t n) z₀ =
      ∑ k ∈ Finset.range n, windingNumber γ (t k) (t (k + 1)) z₀ := by
  rw [windingNumber_eq_of_hasCauchyPVAt (HasCauchyPVAt.concat_range h), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [windingNumber_eq_of_hasCauchyPVAt (h k (Finset.mem_range.mp hk))]

/-- **Finite-partition additivity of the generalized winding number.**  If the Cauchy-kernel
principal value exists on every adjacent interval, the winding number from `t 0` to `t n` is the
sum of the winding numbers of those pieces. -/
theorem windingNumber_eq_sum_range {n : ℕ} {t : ℕ → ℝ}
    (h : ∀ k < n, CauchyPVExistsAt γ (t k) (t (k + 1)) κ[z₀] z₀) :
    windingNumber γ (t 0) (t n) z₀ =
      ∑ k ∈ Finset.range n, windingNumber γ (t k) (t (k + 1)) z₀ := by
  exact windingNumber_eq_sum_range_of_hasCauchyPVAt
    fun k hk => (h k hk).hasCauchyPVAt_cauchyPVAt

/-- **Finite winding decomposition using a.e.-equal, separately computed pieces.** Suppose that
on each adjacent interval the model curve and assembled curve, and their derivatives off `z₀`,
agree almost everywhere. If the Cauchy-kernel principal value exists along every model curve, the
winding number of the assembled curve is the sum of the model-curve winding numbers. -/
theorem windingNumber_eq_sum_range_of_ae {n : ℕ} {t : ℕ → ℝ} (piece : ℕ → ℝ → ℂ)
    (heq : ∀ k < n, piece k =ᵐ[MeasureTheory.volume.restrict (Set.uIoc (t k) (t (k + 1)))] γ)
    (hderiv : ∀ k < n, ∀ᵐ s ∂MeasureTheory.volume.restrict (Set.uIoc (t k) (t (k + 1))),
      piece k s ≠ z₀ → deriv (piece k) s = deriv γ s)
    (hpv : ∀ k < n, CauchyPVExistsAt (piece k) (t k) (t (k + 1)) κ[z₀] z₀) :
    windingNumber γ (t 0) (t n) z₀ =
      ∑ k ∈ Finset.range n, windingNumber (piece k) (t k) (t (k + 1)) z₀ := by
  have hpvγ : ∀ k < n, CauchyPVExistsAt γ (t k) (t (k + 1)) κ[z₀] z₀ :=
    fun k hk => (hpv k hk).congr_curve_ae (heq k hk) (hderiv k hk)
  calc
    windingNumber γ (t 0) (t n) z₀ =
        ∑ k ∈ Finset.range n, windingNumber γ (t k) (t (k + 1)) z₀ :=
      windingNumber_eq_sum_range hpvγ
    _ = ∑ k ∈ Finset.range n, windingNumber (piece k) (t k) (t (k + 1)) z₀ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (windingNumber_congr_curve_ae (heq k (Finset.mem_range.mp hk))
        (hderiv k (Finset.mem_range.mp hk))).symm

/-- **Finite winding decomposition using separately computed pieces.**  Suppose that on the open
subinterval between `t k` and `t (k + 1)`, the assembled curve `γ` agrees with a model curve
`piece k`, and the Cauchy-kernel principal value exists along that model curve.  Then the winding
number of `γ` over the whole partition is the sum of the winding numbers of the model curves.

This convenient pointwise form follows from `windingNumber_eq_sum_range_of_ae`: interval integrals
ignore endpoints, and local equality on an open interval also identifies derivatives there. In
Proposition 2.2 the model curves are the point-avoiding remainder and the finitely many model
sectors. -/
theorem windingNumber_eq_sum_range_of_eqOn {n : ℕ} {t : ℕ → ℝ} (piece : ℕ → ℝ → ℂ)
    (heq : ∀ k < n, Set.EqOn (piece k) γ (Set.uIoo (t k) (t (k + 1))))
    (hpv : ∀ k < n, CauchyPVExistsAt (piece k) (t k) (t (k + 1)) κ[z₀] z₀) :
    windingNumber γ (t 0) (t n) z₀ =
      ∑ k ∈ Finset.range n, windingNumber (piece k) (t k) (t (k + 1)) z₀ := by
  have hpvγ : ∀ k < n, CauchyPVExistsAt γ (t k) (t (k + 1)) κ[z₀] z₀ :=
    fun k hk => (hpv k hk).congr_curve (heq k hk)
  calc
    windingNumber γ (t 0) (t n) z₀ =
        ∑ k ∈ Finset.range n, windingNumber γ (t k) (t (k + 1)) z₀ :=
      windingNumber_eq_sum_range hpvγ
    _ = ∑ k ∈ Finset.range n, windingNumber (piece k) (t k) (t (k + 1)) z₀ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (windingNumber_congr_curve (heq k (Finset.mem_range.mp hk))).symm

end TauCeti.Contour

end
