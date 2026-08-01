/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import TauCeti.Analysis.Contour.Winding.SegmentSum
import TauCeti.Analysis.Contour.Argument.Lift

/-!
# The winding number of a closed curve is an integer

For a curve `γ` on an interval that returns to its start (`γ a = γ b`), avoids a point `w`, and is
regular enough — continuous, differentiable off a countable set, with an interval-integrable index
integrand — its generalized winding number about `w` is an integer (see
`exists_int_windingNumber_of_closed` for the exact hypotheses). This is the integrality step on the
Hungerbühler–Wasem path (HW Thm 3.3): combined with continuity of the winding number in the point,
it makes the winding number locally constant on the complement of the curve — the input to the
homology form of Cauchy's theorem.

## Main results

* `TauCeti.Contour.exists_int_windingNumber_of_closed` — the generalized winding number of a closed
  curve is an integer.

## Provenance

Adapted from `hasGeneralizedWindingNumber_integer_of_closed` in `WindingInteger.lean` of the AINTLIB
`LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on an oriented interval.
-/

public section

open Complex MeasureTheory Set intervalIntegral

open scoped Interval

namespace TauCeti.Contour

/-- The lifted argument sum at the left endpoint `a` is `0`: every partition node satisfies
`a ≤ s j`, so each segment ratio at `a` is `1` and its logarithm's imaginary part is `0`. -/
private lemma sum_im_log_segRatio_left_eq_zero {γ : ℝ → ℂ} {w : ℂ} {a : ℝ} {N : ℕ} {s : ℕ → ℝ}
    (hs_zero : s 0 = a) (hs_mono : Monotone s) (hs_avoid : ∀ j < N, γ (s j) - w ≠ 0) :
    (∑ j ∈ Finset.range N, (Complex.log (segRatio γ w (s j) (s (j + 1)) a)).im) = 0 := by
  refine Finset.sum_eq_zero fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  have ha_le : a ≤ s j := by rw [← hs_zero]; exact hs_mono (Nat.zero_le j)
  rw [segRatio_eq_one_of_le ha_le (hs_avoid j hj), Complex.log_one, Complex.zero_im]

/-- At the right endpoint `b` the lifted argument sum equals the endpoint-ratio sum: every partition
segment lies to the left of `b`, so each segment ratio evaluated at `b` is the full endpoint ratio
`(γ (s (j + 1)) - w) / (γ (s j) - w)`. -/
private lemma sum_im_log_segRatio_right_eq_sum_im_log_endpoint_div {γ : ℝ → ℂ} {w : ℂ} {b : ℝ}
    {N : ℕ} {s : ℕ → ℝ} (hs_N : s N = b) (hs_mono : Monotone s) :
    (∑ j ∈ Finset.range N, (Complex.log (segRatio γ w (s j) (s (j + 1)) b)).im)
      = ∑ j ∈ Finset.range N, (Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w))).im := by
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Finset.mem_range] at hj
  have hb_ge : s (j + 1) ≤ b := by rw [← hs_N]; exact hs_mono hj
  rw [segRatio_eq_endpoint_div_of_le (hs_mono (Nat.le_succ j)) hb_ge]

/-- Two polar forms of the same nonzero point `u`, with real arguments `Ea` and `Eb`, force
`exp (I · (Eb - Ea)) = 1`. -/
private lemma exp_I_mul_ofReal_sub_eq_one_of_polar_eq {u : ℂ} {Ea Eb : ℝ} (hu : u ≠ 0)
    (hla : u = (‖u‖ : ℂ) * Complex.exp (Complex.I * (Ea : ℂ)))
    (hlb : u = (‖u‖ : ℂ) * Complex.exp (Complex.I * (Eb : ℂ))) :
    Complex.exp (Complex.I * ((Eb - Ea : ℝ) : ℂ)) = 1 := by
  -- Cancel the common modulus `‖u‖ ≠ 0` from the two polar forms, then use `exp` periodicity.
  have hnorm_ne : (‖u‖ : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]; exact hu
  have hEab : Complex.exp (Complex.I * (Ea : ℂ)) = Complex.exp (Complex.I * (Eb : ℂ)) :=
    mul_left_cancel₀ hnorm_ne (hla.symm.trans hlb)
  rw [Complex.ofReal_sub, mul_sub]
  exact Complex.exp_eq_exp_iff_exp_sub_eq_one.mp hEab.symm

/-- The nonnegative-orientation (`a ≤ b`) case of `exists_int_windingNumber_of_closed`: under the
same continuity, differentiability-off-a-countable-set, avoidance, and interval-integrability
assumptions on `[a, b]`, the winding number of the closed curve `γ` about `w` is an integer. The
general oriented-interval statement reduces to this case by orientation reversal. -/
private theorem exists_int_windingNumber_of_closed_of_le {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    (hab : a ≤ b) (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b \ P, DifferentiableAt ℝ γ t) (h_avoid : ∀ t ∈ Icc a b, γ t ≠ w)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    ∃ n : ℤ, windingNumber γ a b w = n := by
  -- The argument lift gives a monotone partition `s` and a polar form of `γ t - w` at each `t`.
  obtain ⟨N, s, _, hs_zero, hs_N, hs_mono, _, hs_avoid, h_slit, _, h_lift⟩ :=
    exists_continuousOn_arg_lift_with_partition hab hγ_cont h_avoid
  -- Split the index integral into a modulus increment plus `I` times the endpoint-ratio arg-sum.
  have hint := integral_inv_sub_mul_deriv_eq_log_norm_add_I_mul_sum_log_im hP hs_zero hs_N hs_mono
    hγ_cont hγ_diff h_slit h_int
  -- Closedness `γ a = γ b` makes the two lifted endpoints polar forms of the same point `γ a - w`.
  have hla := h_lift a (left_mem_Icc.mpr hab)
  have hlb := h_lift b (right_mem_Icc.mpr hab)
  rw [← hclosed] at hlb
  set Sa : ℝ := ∑ j ∈ Finset.range N,
    (Complex.log (segRatio γ w (s j) (s (j + 1)) a)).im with hSa_def
  set Sb : ℝ := ∑ j ∈ Finset.range N,
    (Complex.log (segRatio γ w (s j) (s (j + 1)) b)).im with hSb_def
  set Se : ℝ := ∑ j ∈ Finset.range N,
    (Complex.log ((γ (s (j + 1)) - w) / (γ (s j) - w))).im with hSe_def
  -- The lifted argument increment collapses to `Se`: zero at `a` (left), full sum at `b` (right).
  have hEdiff : (Complex.arg (γ a - w) + Sb) - (Complex.arg (γ a - w) + Sa) = Se := by
    rw [hSa_def, hSb_def, hSe_def,
      sum_im_log_segRatio_left_eq_zero hs_zero hs_mono (fun j hj => hs_avoid j hj.le),
      sum_im_log_segRatio_right_eq_sum_im_log_endpoint_div hs_N hs_mono]
    ring
  -- The two polar forms of the same nonzero point `γ a - w` force `exp (I · Se) = 1`.
  have hexp_one : Complex.exp (Complex.I * (Se : ℂ)) = 1 := by
    have h := exp_I_mul_ofReal_sub_eq_one_of_polar_eq
      (sub_ne_zero.mpr (h_avoid a (left_mem_Icc.mpr hab))) hla hlb
    rwa [hEdiff] at h
  -- So `I · Se = n · (2π i)` for some integer `n`, and closedness kills the modulus increment,
  -- leaving `∫ = I · Se`. Converting through the avoidance form of `windingNumber` reads off `n`.
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp_one
  have hlog_zero : Real.log ‖γ b - w‖ - Real.log ‖γ a - w‖ = 0 := by rw [hclosed, sub_self]
  have hint' : (∫ t in a..b, (γ t - w)⁻¹ * deriv γ t) = Complex.I * (Se : ℂ) := by
    rw [hint, hlog_zero, Complex.ofReal_zero, zero_add]
  refine ⟨n, ?_⟩
  have hcont_u : ContinuousOn γ (Set.uIcc a b) := by rw [Set.uIcc_of_le hab]; exact hγ_cont
  have havoid_u : ∀ t ∈ Set.uIcc a b, γ t ≠ w := by rw [Set.uIcc_of_le hab]; exact h_avoid
  have h2πI_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  rw [windingNumber_eq_integral_of_avoidance hcont_u havoid_u h_int, hint', hn,
    mul_comm (n : ℂ) (2 * (Real.pi : ℂ) * Complex.I), ← mul_assoc,
    inv_mul_cancel₀ h2πI_ne, one_mul]

/-- **The winding number of a closed curve is an integer.** For a curve `γ` on the oriented interval
with endpoints `a`, `b` that returns to its start (`γ a = γ b`), is continuous on `Set.uIcc a b`,
differentiable off a countable set `P`, avoids `w` throughout `Set.uIcc a b`, and has an
interval-integrable index integrand `(γ · - w)⁻¹ * deriv γ`, the generalized winding number
`windingNumber γ a b w` is an integer. -/
theorem exists_int_windingNumber_of_closed {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (Set.uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_avoid : ∀ t ∈ Set.uIcc a b, γ t ≠ w)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    ∃ n : ℤ, windingNumber γ a b w = n := by
  rcases le_total a b with hab | hba
  · -- Forward orientation: apply the core directly on `[a, b] = uIcc a b`.
    rw [Set.uIcc_of_le hab] at hγ_cont h_avoid
    rw [min_eq_left hab, max_eq_right hab] at hγ_diff
    exact exists_int_windingNumber_of_closed_of_le hab hclosed hP hγ_cont hγ_diff h_avoid h_int
  · -- Reversed orientation: the core on `[b, a]` gives `windingNumber γ b a w = m`, and
    -- `windingNumber γ a b w = -windingNumber γ b a w` by `integral_symm`, so `n = -m`.
    have hcont_ba : ContinuousOn γ (Icc b a) := by rw [← Set.uIcc_of_ge hba]; exact hγ_cont
    have havoid_ba : ∀ t ∈ Icc b a, γ t ≠ w := fun t ht ↦
      h_avoid t (by rw [Set.uIcc_of_ge hba]; exact ht)
    rw [min_eq_right hba, max_eq_left hba] at hγ_diff
    obtain ⟨m, hm⟩ := exists_int_windingNumber_of_closed_of_le hba hclosed.symm hP hcont_ba
      hγ_diff havoid_ba h_int.symm
    refine ⟨-m, ?_⟩
    have hrev : windingNumber γ a b w = -windingNumber γ b a w := by
      rw [windingNumber_eq_integral_of_avoidance hγ_cont h_avoid h_int,
        windingNumber_eq_integral_of_avoidance (by rw [Set.uIcc_comm]; exact hγ_cont)
          (fun t ht ↦ h_avoid t (by rw [Set.uIcc_comm] at ht; exact ht)) h_int.symm,
        intervalIntegral.integral_symm a b]
      ring
    rw [hrev, hm]; push_cast; ring

end TauCeti.Contour
