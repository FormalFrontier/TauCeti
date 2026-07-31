/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Analysis.Contour.Cauchy.PrincipalValue.Basic
public import TauCeti.Analysis.Contour.PwC1ImmersionOn
public import TauCeti.Analysis.Contour.RegularityConditions
import TauCeti.Analysis.Contour.Crossing.Finiteness
import TauCeti.Analysis.Contour.Crossing.PVAggregation
import TauCeti.Analysis.Contour.Crossing.Windows
import TauCeti.Analysis.Contour.PerWindow.HigherOrder
import TauCeti.Analysis.Contour.PiecewiseC1On

/-!
# The principal value of a higher-order polar term along an immersed curve

For a piecewise-`C¹` immersed curve `γ` on `[a, b]` whose value-`s` parameters are interior,
flat of order `n ≥ k`, and sector-compatible, the single-point Cauchy principal value of the
order-`k ≥ 2` polar term `t ↦ c / (γ t - s) ^ k * deriv γ t` exists on `[a, b]` and equals the
boundary difference of the antiderivative `c · (-(k-1)⁻¹ (· - s)^{-(k-1)}) ∘ γ` — in
particular it vanishes around a closed curve, which is why only the simple-pole part of a
polar decomposition contributes to the generalized residue theorem. The crossings are finitely
many (`Contour.IsPwC1ImmersionOn.finite_crossings`), a common window radius separates them
(`Contour.exists_common_window_radius`), each window integral converges to the boundary
difference (`Contour.perWindow_higherOrder_truncated_integral_tendsto`), and the pieces
telescope (`Contour.hasCauchyPVAt_of_perWindow_boundary_tendsto`).

The flatness and sector hypotheses are the raw per-crossing forms of the Hungerbühler–Wasem
conditions (A′) and (B) at `s` (`Contour.FlatOfOrder`; the tangent-direction power equation,
stated for the one-sided derivative limits, which are unique).

## Main results

* `Contour.IsPwC1ImmersionOn.hasCauchyPVAt_pow_inv` — the single-point principal value of the
  order-`k ≥ 2` polar term along a piecewise-`C¹` immersion is the boundary difference of its
  antiderivative.

## Provenance

Migrated from the higher-order content of `hasCauchyPVOn_multiCrossing_higherOrder_corner` of
`MultiCrossingCPV.lean` in the AINTLIB `LeanModularForms` development (there stated for the
bundled `ClosedPwC1Immersion`). See N. Hungerbühler, M. Wasem, *Non-integer valued winding
numbers and a generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- At an interior crossing that is flat of order `n ≥ k` and sector-compatible, the truncated
window integral of the order-`k` polar term converges to the boundary difference of the
antiderivative, at every window radius whose window lies inside `[a, b]` and contains no other
crossing. -/
private theorem perWindow_boundary_tendsto_of_interior {γ : ℝ → ℂ} {a b t₀ : ℝ} {s : ℂ}
    {k n : ℕ} {P : Set ℝ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a < b)
    (ht₀ : t₀ ∈ Ioo a b) (h_at : γ t₀ = s) (hk : 2 ≤ k) (hkn : k ≤ n)
    (h_flat : FlatOfOrder γ t₀ n)
    (h_B : ∀ L_R L_L : ℂ, Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R) →
      Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L) →
      (L_R / (‖L_R‖ : ℂ)) ^ (k - 1) = ((-L_L) / (‖L_L‖ : ℂ)) ^ (k - 1))
    (c : ℂ) (hP : P.Countable)
    (hγ_diffP : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    {ρ : ℝ} (hρ_pos : 0 < ρ) (h_lo : a < t₀ - ρ) (h_hi : t₀ + ρ ≤ b)
    (h_unique : ∀ t ∈ Icc (t₀ - ρ) (t₀ + ρ), γ t = s → t = t₀) :
    Tendsto (fun ε : ℝ => ∫ t in (t₀ - ρ)..(t₀ + ρ),
        if ‖γ t - s‖ > ε then c / (γ t - s) ^ k * deriv γ t else 0)
      (𝓝[>] (0 : ℝ))
      (𝓝 (c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t₀ + ρ) - s) ^ (k - 1))⁻¹) -
        c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t₀ - ρ) - s) ^ (k - 1))⁻¹))) := by
  have hmin : min a b = a := min_eq_left hab.le
  have hmax : max a b = b := max_eq_right hab.le
  have ht₀' : t₀ ∈ Ioo (min a b) (max a b) := by rwa [hmin, hmax]
  obtain ⟨L_R, hL_R, h_tend_R⟩ := h_imm.exists_deriv_right_limit
    (by rw [hmin, hmax]; exact ⟨ht₀.1.le, ht₀.2⟩)
  obtain ⟨L_L, hL_L, h_tend_L⟩ := h_imm.exists_deriv_left_limit
    (by rw [hmin, hmax]; exact ⟨ht₀.1, ht₀.2.le⟩)
  refine perWindow_higherOrder_truncated_integral_tendsto hρ_pos h_at
    (h_imm.continuousOn.mono (by
      rw [uIcc_of_le hab.le]
      exact Icc_subset_Icc (by linarith) h_hi))
    hL_R hL_L h_tend_R h_tend_L
    (h_imm.isPiecewiseC1On.eventually_differentiableAt_right ht₀')
    (h_imm.isPiecewiseC1On.eventually_differentiableAt_left ht₀')
    hP
    (fun t ht => hγ_diffP t ⟨by
      rw [hmin, hmax]
      exact ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩, ht.2⟩)
    (h_imm.isPiecewiseC1On.intervalIntegrable_deriv.mono_set (by
      rw [uIcc_of_le (by linarith : t₀ - ρ ≤ t₀ + ρ), uIcc_of_le hab.le]
      exact Icc_subset_Icc (by linarith) h_hi))
    h_unique h_flat hk hkn (h_B L_R L_L h_tend_R h_tend_L) c

/-- On a pole-free subinterval of `[a, b]`, the integral of the order-`k` polar term along a
piecewise-`C¹` curve is the boundary difference of its antiderivative — the plain-piece input
to the telescoping aggregation. -/
private theorem plain_piece_integral_eq {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} {k : ℕ}
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a < b) (hk : 2 ≤ k) (c : ℂ)
    {l u : ℝ} (hal : a ≤ l) (hlu : l ≤ u) (hub : u ≤ b)
    (h_ne : ∀ t ∈ Icc l u, γ t ≠ s) :
    ∫ t in l..u, c / (γ t - s) ^ k * deriv γ t =
      c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ u - s) ^ (k - 1))⁻¹) -
        c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ l - s) ^ (k - 1))⁻¹) := by
  obtain ⟨p, hp⟩ := h_imm.isPiecewiseC1On.exists_finset_differentiableAt
  refine integral_pow_inv_mul_deriv_eq_sub hk c hlu p.countable_toSet h_ne
    (fun t ht => hp t ⟨by
      rw [min_eq_left hab.le, max_eq_right hab.le]
      exact ⟨lt_of_le_of_lt hal ht.1.1, lt_of_lt_of_le ht.1.2 hub⟩, ht.2⟩)
    ((h_imm.continuousOn.mono (uIcc_of_le hab.le).ge).mono (Icc_subset_Icc hal hub))
    (h_imm.isPiecewiseC1On.intervalIntegrable_deriv.mono_set (by
      rw [uIcc_of_le hlu, uIcc_of_le hab.le]
      exact Icc_subset_Icc hal hub))

/-- **The principal value of a higher-order polar term along a piecewise-`C¹` immersion is the
boundary difference of its antiderivative**: if every parameter of `[a, b]` where `γ` meets
`s` is interior, flat of order `n ≥ k`, and sector-compatible in the tangent-direction power
sense, then for `k ≥ 2` the single-point Cauchy principal value of
`t ↦ c / (γ t - s) ^ k * deriv γ t` at `s` exists on `[a, b]` with value
`c · (-(k-1)⁻¹ (· - s)^{-(k-1)}) ∘ γ` differenced at the endpoints — zero around a closed
curve. Endpoint crossings are excluded by `h_interior`; for a closed curve this is the choice
of a basepoint off `s`. -/
theorem IsPwC1ImmersionOn.hasCauchyPVAt_pow_inv {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} {k n : ℕ}
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b)
    (h_interior : ∀ t ∈ Icc a b, γ t = s → t ∈ Ioo a b)
    (hk : 2 ≤ k) (hkn : k ≤ n)
    (h_flat : ∀ t ∈ Icc a b, γ t = s → FlatOfOrder γ t n)
    (h_B : ∀ t ∈ Icc a b, γ t = s → ∀ L_R L_L : ℂ,
      Tendsto (deriv γ) (𝓝[>] t) (𝓝 L_R) → Tendsto (deriv γ) (𝓝[<] t) (𝓝 L_L) →
      (L_R / (‖L_R‖ : ℂ)) ^ (k - 1) = ((-L_L) / (‖L_L‖ : ℂ)) ^ (k - 1))
    (c : ℂ) :
    HasCauchyPVAt γ a b (fun z => c / (z - s) ^ k) s
      (c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ b - s) ^ (k - 1))⁻¹) -
        c * (-(↑(k - 1) : ℂ)⁻¹ * ((γ a - s) ^ (k - 1))⁻¹)) := by
  classical
  rcases hab.eq_or_lt with rfl | hab
  · simpa using HasCauchyPVAt.of_eq γ rfl (fun z => c / (z - s) ^ k) s
  set T : Finset ℝ := (h_imm.finite_crossings (z₀ := s)).toFinset with hT_def
  have hT_mem : ∀ {t : ℝ}, t ∈ T ↔ t ∈ Icc a b ∧ γ t = s := fun {_} => by
    rw [hT_def, h_imm.mem_toFinset_finite_crossings, uIcc_of_le hab.le]
  have h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ T := fun t ht h_eq => hT_mem.mpr ⟨ht, h_eq⟩
  have h_Ioo : ∀ t ∈ T, t ∈ Ioo a b := fun t ht =>
    h_interior t (hT_mem.mp ht).1 (hT_mem.mp ht).2
  have hγ_cont : ContinuousOn γ (Icc a b) := h_imm.continuousOn.mono (uIcc_of_le hab.le).ge
  obtain ⟨p, hp⟩ := h_imm.isPiecewiseC1On.exists_finset_differentiableAt
  have h_int_tr : ∀ ε : ℝ, 0 < ε → IntervalIntegrable
      (fun t => if ‖γ t - s‖ > ε then c / (γ t - s) ^ k * deriv γ t else 0)
      MeasureTheory.volume a b :=
    fun _ hε => intervalIntegrable_pow_inv_mul_deriv_truncated c k h_imm.continuousOn
      h_imm.isPiecewiseC1On.intervalIntegrable_deriv hε
  have h_plain := fun l u =>
    plain_piece_integral_eq (s := s) h_imm hab hk c (l := l) (u := u)
  rcases T.eq_empty_or_nonempty with hT_empty | -
  · refine hasCauchyPVAt_of_perWindow_boundary_tendsto
      (Φ := fun z => c * (-(↑(k - 1) : ℂ)⁻¹ * ((z - s) ^ (k - 1))⁻¹))
      one_pos hab.le T ?_ ?_ ?_ h_int_tr h_plain ?_
      (exists_complement_windows_dist_lower_bound hγ_cont h_complete (fun _ => 1)
        fun t _ => one_pos)
    all_goals simp [hT_empty]
  · -- The same uniform radius as in `InvSubCPVExistence`; the constant bound `1` is inert here,
    -- and the strict margins it returns are what removes the halving this used to need.
    obtain ⟨ρ, hρ_pos, h_endpts, h_pair, -⟩ :=
      exists_common_window_radius_le h_Ioo (fun _ => 1) fun _ _ => one_pos
    refine hasCauchyPVAt_of_perWindow_boundary_tendsto
      (Φ := fun z => c * (-(↑(k - 1) : ℂ)⁻¹ * ((z - s) ^ (k - 1))⁻¹))
      hρ_pos hab.le T
      (fun t ht => by linarith [(h_endpts t ht).1])
      (fun t ht => by linarith [(h_endpts t ht).2])
      h_pair
      h_int_tr h_plain
      (fun t₀ ht₀ => perWindow_boundary_tendsto_of_interior h_imm hab (h_Ioo t₀ ht₀)
        (hT_mem.mp ht₀).2 hk hkn (h_flat t₀ (hT_mem.mp ht₀).1 (hT_mem.mp ht₀).2)
        (h_B t₀ (hT_mem.mp ht₀).1 (hT_mem.mp ht₀).2) c p.countable_toSet hp hρ_pos
        (by linarith [(h_endpts t₀ ht₀).1]) (by linarith [(h_endpts t₀ ht₀).2])
        fun t ht h_eq => eq_of_mem_window_of_eq_of_lt_of_two_mul_lt (h_endpts t₀ ht₀)
          (h_pair t₀ ht₀) h_complete ht h_eq)
      (exists_complement_windows_dist_lower_bound hγ_cont h_complete (fun _ => ρ)
        fun t _ => hρ_pos)

end TauCeti.Contour

end
