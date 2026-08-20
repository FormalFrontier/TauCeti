/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Crossing.Finiteness
public import TauCeti.Analysis.Contour.PwC1ImmersionOn
public import TauCeti.Analysis.Contour.RegularityConditions
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import TauCeti.Analysis.Contour.Crossing.Windows
import TauCeti.Analysis.Contour.InvSubCPVExistence
import TauCeti.Analysis.Contour.PerWindow.CPV
import TauCeti.Analysis.Contour.Winding.EndpointRatio

/-!
# The crossing angles of a closed immersion, modulo an integer

Hungerbühler–Wasem Proposition 2.2 decomposes a closed piecewise-`C¹` immersion `Λ` meeting a
point `s` at the finitely many parameters `t₁, …, tₙ` as
`Λ = \tilde{\Lambda} + Γ₁ + ⋯ + Γₙ`, with `\tilde{\Lambda}` avoiding `s` and each `Γ_ℓ`
a model sector of opening angle `α_ℓ`, and concludes

`n_s(Λ) = n_s(\tilde{\Lambda}) + ∑_ℓ α_ℓ / 2π`.

Since `\tilde{\Lambda}` avoids `s`, its winding number is an integer
(`TauCeti.Contour.IsPiecewiseC1On.exists_int_windingNumber`). This file proves the identity in
the form that does not name the surgered curve:

`n_s(Λ) - ∑_ℓ α_ℓ / 2π ∈ ℤ`,

where `α_ℓ = crossingAngle Λ t_ℓ` is read off the one-sided tangents at the crossing.
Nothing here builds `\tilde{\Lambda}`, so the integer is produced abstractly rather than
identified with `n_s(\tilde{\Lambda})`; that identification, which needs the excise-and-cap
construction, is what remains of HW Proposition 2.2.

The proof does not decompose the curve either. It exponentiates. The principal value
`2πi · n_s(Λ)` is aggregated out of plain pieces and crossing windows exactly as the existence
proof aggregates it (`TauCeti.Contour.IsPwC1ImmersionOn.cauchyPVExistsAt_inv_sub`), and both
kinds of contribution exponentiate to a chord ratio: a plain piece to `(Λ u - s)/(Λ l - s)`
(`TauCeti.Contour.IsPiecewiseC1On.exp_two_pi_I_mul_windingNumber`), and a crossing window to
that same ratio times `exp (i α_ℓ)`
(`TauCeti.Contour.exp_log_norm_add_arg_eq_mul_exp_crossingAngle` below, which is where the
crossing angle enters). The ratios telescope along the curve and cancel at the closed-up
basepoint, leaving `exp (2πi · n_s(Λ)) = exp (i ∑_ℓ α_ℓ)`. Reading that off is the whole
content: with no crossings it is the classical integrality statement, and each crossing shifts
the winding number by its angle over `2π`.

## Main results

* `TauCeti.Contour.exp_log_norm_add_arg_eq_mul_exp_crossingAngle` — the per-window principal
  value of the Cauchy kernel exponentiates to the window's chord ratio times
  `exp (i · crossingAngle)`.
* `TauCeti.Contour.IsPwC1ImmersionOn.exp_two_pi_I_mul_windingNumber_eq_exp_sum_crossingAngle` —
  `exp (2πi · n_s(γ)) = exp (i ∑ α)` for a closed piecewise-`C¹` immersion based off `s`.
* `TauCeti.Contour.IsPwC1ImmersionOn.exists_int_windingNumber_eq_add_sum_crossingAngle` — **HW
  Proposition 2.2, modulo the integer**: `n_s(γ) = k + (∑ α) / 2π` for some `k : ℤ`, and
  `…_toFinset`, the same against the canonical crossing set of the immersion.
* `TauCeti.Contour.IsPwC1ImmersionOn.exists_int_windingNumber_eq_add_card_div_two` — the smooth
  case: if every crossing is smooth, each contributes `½`.

## Provenance

No formal source is vendored for the exponential argument. Its two inputs are migrated material:
the per-window principal value of the Cauchy kernel
(`TauCeti.Analysis.Contour.PerWindow.CPV`, from `LocalCutoffs.lean` of the AINTLIB
`LeanModularForms` development) and the crossing-angle reading of its boundary arguments
(`TauCeti.Analysis.Contour.RegularityConditions`).

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Proposition 2.2.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace TauCeti.Contour

/-- Two reals equal in `Real.Angle` have the same `exp (· * I)`: the multiple of `2π` between
them is invisible to the complex exponential. -/
private theorem exp_mul_I_congr_angle {x y : ℝ} (h : (x : Real.Angle) = (y : Real.Angle)) :
    Complex.exp ((x : ℂ) * Complex.I) = Complex.exp ((y : ℂ) * Complex.I) := by
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h
  have hx : (x : ℂ) = (y : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ)) := by
    have hxy : x = y + (k : ℝ) * (2 * Real.pi) := by linarith [hk]
    rw [hxy]
    push_cast
    ring
  have hk_exp : ((k : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    ring
  rw [hx, add_mul, Complex.exp_add, hk_exp,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **The per-window principal value exponentiates to the chord ratio times the crossing angle.**
`TauCeti.Contour.perWindow_truncated_integral_tendsto` evaluates the `ε`-truncated integral of
the Cauchy kernel over a crossing window to
`(log ‖w_R‖ - log ‖w_L‖) + i · (arg (-L_L / w_L) + arg (w_R / L_R))`, where `w_L`, `w_R` are the
chords to the two window endpoints and `L_L`, `L_R` the one-sided tangents at the crossing. This
identity says its exponential is `w_R / w_L · exp (i · crossingAngle γ t₀)`: the log-norm part
supplies the modulus of the chord ratio, and the two boundary arguments supply its argument plus
exactly the crossing angle, by
`TauCeti.Contour.coe_crossingAngle_eq_arg_neg_div_add_arg_div_sub_arg_div`.

The chords `w_L`, `w_R` are left free, as they are there; the intended reading takes them to be
`γ (t₀ - ρ) - s` and `γ (t₀ + ρ) - s`. -/
theorem exp_log_norm_add_arg_eq_mul_exp_crossingAngle {γ : ℝ → ℂ} {t₀ : ℝ} {L_R L_L w_L w_R : ℂ}
    (hL_L : L_L ≠ 0) (hL_R : L_R ≠ 0) (hw_L : w_L ≠ 0) (hw_R : w_R ≠ 0)
    (h_R : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_R))
    (h_L : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_L)) :
    Complex.exp (((Real.log ‖w_R‖ - Real.log ‖w_L‖ : ℝ) : ℂ) +
        ((((-L_L) / w_L).arg + (w_R / L_R).arg : ℝ) : ℂ) * Complex.I)
      = w_R / w_L * Complex.exp ((crossingAngle γ t₀ : ℂ) * Complex.I) := by
  have hangle : ((((-L_L) / w_L).arg + (w_R / L_R).arg : ℝ) : Real.Angle)
      = ((crossingAngle γ t₀ + (w_R / w_L).arg : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add, Real.Angle.coe_add,
      coe_crossingAngle_eq_arg_neg_div_add_arg_div_sub_arg_div hL_L hL_R hw_L hw_R h_R h_L]
    abel
  have hnorm : Complex.exp (((Real.log ‖w_R‖ - Real.log ‖w_L‖ : ℝ) : ℂ))
      = ((‖w_R / w_L‖ : ℝ) : ℂ) := by
    rw [norm_div, ← Real.log_div (norm_ne_zero_iff.mpr hw_R) (norm_ne_zero_iff.mpr hw_L),
      ← Complex.ofReal_exp, Real.exp_log (by positivity)]
  have hsplit : Complex.exp (((crossingAngle γ t₀ + (w_R / w_L).arg : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((crossingAngle γ t₀ : ℂ) * Complex.I) *
        Complex.exp ((((w_R / w_L).arg : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [Complex.exp_add, exp_mul_I_congr_angle hangle, hnorm, hsplit]
  calc ((‖w_R / w_L‖ : ℝ) : ℂ) * (Complex.exp ((crossingAngle γ t₀ : ℂ) * Complex.I) *
        Complex.exp ((((w_R / w_L).arg : ℝ) : ℂ) * Complex.I))
      = (((‖w_R / w_L‖ : ℝ) : ℂ) * Complex.exp ((((w_R / w_L).arg : ℝ) : ℂ) * Complex.I)) *
          Complex.exp ((crossingAngle γ t₀ : ℂ) * Complex.I) := by ring
    _ = w_R / w_L * Complex.exp ((crossingAngle γ t₀ : ℂ) * Complex.I) := by
        rw [Complex.norm_mul_exp_arg_mul_I]

/-- **The winding number of a closed immersion exponentiates to its crossing angles.** For a
closed piecewise-`C¹` immersion `γ` on `[a, b]` whose basepoint avoids `s`, and a finset `T`
listing exactly the parameters where `γ` meets `s`,

`exp (2πi · n_s(γ)) = exp (i · ∑_{t ∈ T} crossingAngle γ t)`.

The principal value on the left is aggregated by cutting `[a, b]` into plain pieces, on which
`γ` keeps a positive distance from `s`, and one window around each crossing. Exponentiated, a
plain piece contributes the chord ratio of its endpoints, and a crossing window contributes
that ratio times `exp (i · crossingAngle)`
(`TauCeti.Contour.exp_log_norm_add_arg_eq_mul_exp_crossingAngle`); the ratios telescope, and
closedness cancels the two ends. With `T = ∅` this is the endpoint-ratio proof of
integrality. -/
theorem IsPwC1ImmersionOn.exp_two_pi_I_mul_windingNumber_eq_exp_sum_crossingAngle
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} {T : Finset ℝ}
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b) (hclosed : γ a = γ b) (hbase : γ a ≠ s)
    (hT : ∀ t, t ∈ T ↔ t ∈ Icc a b ∧ γ t = s) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b s)
      = Complex.exp (((∑ t ∈ T, crossingAngle γ t : ℝ) : ℂ) * Complex.I) := by
  classical
  rcases hab.eq_or_lt with rfl | hab'
  · have hTe : T = ∅ := Finset.eq_empty_of_forall_notMem fun t ht => by
      obtain ⟨ht_mem, ht_eq⟩ := (hT t).mp ht
      rw [Icc_self, mem_singleton_iff] at ht_mem
      exact hbase (ht_mem ▸ ht_eq)
    rw [hTe, windingNumber_same]
    simp
  have hγ_cont : ContinuousOn γ (Icc a b) := h_imm.continuousOn.mono (uIcc_of_le hab).ge
  have h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ T := fun t ht he => (hT t).mpr ⟨ht, he⟩
  have h_Ioo : ∀ t ∈ T, t ∈ Ioo a b := by
    intro t ht
    obtain ⟨⟨h1, h2⟩, he⟩ := (hT t).mp ht
    refine ⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_⟩
    · rintro rfl; exact hbase he
    · rintro rfl; exact hbase (hclosed.trans he)
  choose! R hR_pos L_R L_L hL_R hL_L h_tend_R h_tend_L h_spec using
    fun t₀ (ht₀ : t₀ ∈ T) => exists_radius_perWindow_tendsto_log_norm_add_arg h_imm hab'
      (h_Ioo t₀ ht₀) ((hT t₀).mp ht₀).2
  obtain ⟨ρ, hρ_pos, h_endpts, h_pair, hρ_le_R⟩ := exists_common_window_radius_le h_Ioo R hR_pos
  obtain ⟨m, hm_pos, hm⟩ := exists_complement_windows_dist_lower_bound hγ_cont h_complete
    (fun _ => ρ) fun _ _ => hρ_pos
  have h_unique : ∀ t₀ ∈ T, ∀ t ∈ Icc (t₀ - ρ) (t₀ + ρ), γ t = s → t = t₀ :=
    fun t₀ ht₀ t ht he => eq_of_mem_window_of_eq_of_lt_of_two_mul_lt (h_endpts t₀ ht₀)
      (h_pair t₀ ht₀) h_complete ht he
  set cf : ℝ → ℂ := fun t => Complex.exp ((crossingAngle γ t : ℂ) * Complex.I) with hcf
  set Φ : ℝ → ℂ := fun x => (γ x - s) * ∏ t ∈ T.filter (fun t => t < x), cf t with hΦ
  -- The aggregated principal value, with its exponential telescoped along `Φ`.
  have hQ : ∃ v : ℂ, HasCauchyPVAt γ a b (fun z => (z - s)⁻¹) s v ∧ Complex.exp v * Φ a = Φ b := by
    refine sorted_crossing_gluing_induction
      (Q := fun l u => ∃ v : ℂ, HasCauchyPVAt γ l u (fun z => (z - s)⁻¹) s v ∧
        Complex.exp v * Φ l = Φ u)
      (γ := γ) (s := s) (A := a) (b := b) (r := ρ) (m := m) ?_ ?_
      (T.sort (· ≤ ·)) (Finset.sortedLT_sort T) (fun _ => hρ_pos.le) a le_rfl hab
      (fun t ht => by linarith [(h_endpts t ((Finset.mem_sort _).mp ht)).1])
      (fun t ht => by linarith [(h_endpts t ((Finset.mem_sort _).mp ht)).2])
      (fun t ht t' ht' hne => (h_pair t ((Finset.mem_sort _).mp ht) t'
        ((Finset.mem_sort _).mp ht') hne).le)
      ?_
      (fun u hu h_avoid => hm u hu fun t ht => h_avoid t ((Finset.mem_sort _).mpr ht))
    · -- A plain piece: the winding number is an ordinary integral and exponentiates to the
      -- chord ratio, and no crossing lies in it, so the sector product does not move.
      intro l u hal hlu hub hfar
      have havoid : ∀ t ∈ uIcc l u, γ t ≠ s := by
        intro t ht he
        rw [uIcc_of_le hlu] at ht
        have hle := hfar t ht
        rw [he, sub_self, norm_zero] at hle
        linarith
      have hpc : IsPiecewiseC1On γ l u := h_imm.isPiecewiseC1On.mono (by
        rw [uIcc_of_le hlu, uIcc_of_le hab]
        exact Icc_subset_Icc hal hub)
      have hint : IntervalIntegrable (fun t => (γ t - s)⁻¹ * deriv γ t) volume l u :=
        intervalIntegrable_inv_sub_mul_deriv hpc.continuousOn havoid hpc.intervalIntegrable_deriv
      have hval : 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ l u s
          = ∫ t in l..u, (γ t - s)⁻¹ * deriv γ t := by
        rw [windingNumber_eq_integral_of_avoidance hpc.continuousOn havoid hint,
          mul_inv_cancel_left₀ Complex.two_pi_I_ne_zero]
      refine ⟨2 * (Real.pi : ℂ) * Complex.I * windingNumber γ l u s, ?_, ?_⟩
      · have h0 : HasCauchyPVAt γ l u (fun z => (z - s)⁻¹) s
            (∫ t in l..u, (γ t - s)⁻¹ * deriv γ t) :=
          HasCauchyPVAt.of_avoidance hpc.continuousOn havoid hint
        rwa [← hval] at h0
      · have hfilter : T.filter (fun t => t < l) = T.filter (fun t => t < u) := by
          refine Finset.filter_congr fun t ht => ⟨fun h => by linarith, fun h => ?_⟩
          by_contra hlt
          rw [not_lt] at hlt
          have hle := hfar t ⟨hlt, h.le⟩
          rw [((hT t).mp ht).2, sub_self, norm_zero] at hle
          linarith
        have hl : γ l - s ≠ 0 := sub_ne_zero.mpr (havoid l left_mem_uIcc)
        simp only [hΦ, hpc.exp_two_pi_I_mul_windingNumber havoid, hfilter]
        field_simp
    · rintro l u₀ u - - ⟨v₁, h₁, e₁⟩ ⟨v₂, h₂, e₂⟩
      refine ⟨v₁ + v₂, h₁.concat h₂, ?_⟩
      rw [Complex.exp_add, mul_comm (Complex.exp v₁), mul_assoc, e₁, e₂]
    · -- A crossing window: the per-window principal value exponentiates to the chord ratio
      -- times the crossing angle, which is exactly the sector factor `Φ` gains there.
      intro t₀ ht₀'
      have ht₀ : t₀ ∈ T := (Finset.mem_sort _).mp ht₀'
      have hlo : a < t₀ - ρ := by linarith [(h_endpts t₀ ht₀).1]
      have hhi : t₀ + ρ ≤ b := by linarith [(h_endpts t₀ ht₀).2]
      have hwin : uIcc (t₀ - ρ) (t₀ + ρ) ⊆ uIcc a b := by
        rw [uIcc_of_le (by linarith : t₀ - ρ ≤ t₀ + ρ), uIcc_of_le hab]
        exact Icc_subset_Icc hlo.le hhi
      have hpc : IsPiecewiseC1On γ (t₀ - ρ) (t₀ + ρ) := h_imm.isPiecewiseC1On.mono hwin
      have hne : ∀ t ∈ Icc (t₀ - ρ) (t₀ + ρ), t ≠ t₀ → γ t - s ≠ 0 := fun t ht hne0 h0 =>
        hne0 (h_unique t₀ ht₀ t ht (sub_eq_zero.mp h0))
      have hw_L : γ (t₀ - ρ) - s ≠ 0 :=
        hne _ ⟨le_rfl, by linarith⟩ (by intro h; linarith)
      have hw_R : γ (t₀ + ρ) - s ≠ 0 :=
        hne _ ⟨by linarith, le_rfl⟩ (by intro h; linarith)
      refine ⟨((Real.log ‖γ (t₀ + ρ) - s‖ - Real.log ‖γ (t₀ - ρ) - s‖ : ℝ) : ℂ) +
        ((((-L_L t₀) / (γ (t₀ - ρ) - s)).arg + ((γ (t₀ + ρ) - s) / L_R t₀).arg : ℝ) : ℂ) *
          Complex.I, ?_, ?_⟩
      · refine hasCauchyPVAt_iff.mpr ⟨?_, h_spec t₀ ht₀ ρ hρ_pos (hρ_le_R t₀ ht₀) hlo hhi
          (h_unique t₀ ht₀)⟩
        exact Filter.eventually_iff_exists_mem.mpr ⟨Ioi 0, self_mem_nhdsWithin,
          fun ε hε => intervalIntegrable_inv_sub_truncated hpc.continuousOn
            hpc.intervalIntegrable_deriv hε⟩
      · have hnotmem : t₀ ∉ T.filter (fun t => t < t₀ - ρ) := by
          simp only [Finset.mem_filter, not_and]
          intro _
          linarith
        have hfil : T.filter (fun t => t < t₀ + ρ)
            = insert t₀ (T.filter (fun t => t < t₀ - ρ)) := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_insert]
          refine ⟨fun ⟨htT, hlt⟩ => ?_, ?_⟩
          · by_cases h : t < t₀ - ρ
            · exact Or.inr ⟨htT, h⟩
            · exact Or.inl (h_unique t₀ ht₀ t ⟨not_lt.mp h, hlt.le⟩ ((hT t).mp htT).2)
          · rintro (rfl | ⟨htT, hlt⟩)
            · exact ⟨ht₀, by linarith⟩
            · exact ⟨htT, by linarith⟩
        simp only [hΦ, hfil, Finset.prod_insert hnotmem,
          exp_log_norm_add_arg_eq_mul_exp_crossingAngle (hL_L t₀ ht₀) (hL_R t₀ ht₀) hw_L hw_R
            (h_tend_R t₀ ht₀) (h_tend_L t₀ ht₀)]
        field_simp
        ring
  obtain ⟨v, hv, he⟩ := hQ
  have hΦa : Φ a = γ a - s := by
    simp only [hΦ, Finset.filter_false_of_mem fun t ht => not_lt.mpr (h_Ioo t ht).1.le,
      Finset.prod_empty, mul_one]
  have hΦb : Φ b = (γ a - s) * ∏ t ∈ T, cf t := by
    simp only [hΦ, ← hclosed, Finset.filter_true_of_mem fun t ht => (h_Ioo t ht).2]
  rw [windingNumber_eq_of_hasCauchyPVAt hv, mul_inv_cancel_left₀ Complex.two_pi_I_ne_zero]
  rw [hΦa, hΦb] at he
  have hbase' : γ a - s ≠ 0 := sub_ne_zero.mpr hbase
  have hprod : Complex.exp v = ∏ t ∈ T, cf t :=
    mul_right_cancel₀ hbase' (by rw [he]; ring)
  rw [hprod, hcf, ← Complex.exp_sum, ← Finset.sum_mul, Complex.ofReal_sum]

/-- **Hungerbühler–Wasem Proposition 2.2, modulo the integer.** For a closed piecewise-`C¹`
immersion `γ` on `[a, b]` whose basepoint avoids `s`, and a finset `T` listing exactly the
parameters where `γ` meets `s`, the generalized winding number is an integer plus the crossing
angles over `2π`:

`n_s(γ) = k + (∑_{t ∈ T} crossingAngle γ t) / 2π`.

In HW's decomposition `Λ = \tilde{\Lambda} + Γ₁ + ⋯ + Γₙ` the integer is
`n_s(\tilde{\Lambda})`, the winding number of the curve obtained by excising the crossings and
capping them off; that surgery is not performed here, so `k` is produced abstractly.
Everything else is: the crossings' contribution is exactly their model-sector value `α_ℓ / 2π`.

With no crossings this is `TauCeti.Contour.IsPiecewiseC1On.exists_int_windingNumber`, and with a
single smooth crossing it gives the half-integral winding number of the half-residue regime
(`exists_int_windingNumber_eq_add_card_div_two`). -/
theorem IsPwC1ImmersionOn.exists_int_windingNumber_eq_add_sum_crossingAngle
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} {T : Finset ℝ}
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b) (hclosed : γ a = γ b) (hbase : γ a ≠ s)
    (hT : ∀ t, t ∈ T ↔ t ∈ Icc a b ∧ γ t = s) :
    ∃ k : ℤ, windingNumber γ a b s
      = k + ((∑ t ∈ T, crossingAngle γ t : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp
    (h_imm.exp_two_pi_I_mul_windingNumber_eq_exp_sum_crossingAngle hab hclosed hbase hT)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  refine ⟨k, mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_⟩
  rw [hk]
  field_simp
  ring

/-- **Hungerbühler–Wasem Proposition 2.2 against the canonical crossing set.** The form of
`exists_int_windingNumber_eq_add_sum_crossingAngle` that takes its crossing finset from the
finiteness of the crossing set of an immersion
(`TauCeti.Contour.IsPwC1ImmersionOn.finite_crossings`) rather than from the caller. -/
theorem IsPwC1ImmersionOn.exists_int_windingNumber_eq_add_sum_crossingAngle_toFinset
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ}
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b) (hclosed : γ a = γ b) (hbase : γ a ≠ s) :
    ∃ k : ℤ, windingNumber γ a b s
      = k + ((∑ t ∈ (h_imm.finite_crossings (z₀ := s)).toFinset, crossingAngle γ t : ℝ) : ℂ)
          / (2 * (Real.pi : ℂ)) :=
  h_imm.exists_int_windingNumber_eq_add_sum_crossingAngle hab hclosed hbase fun t => by
    rw [h_imm.mem_toFinset_finite_crossings, uIcc_of_le hab]

/-- **Every smooth crossing contributes `½`.** A crossing where the two one-sided tangents agree
has angle `π` (`TauCeti.Contour.crossingAngle_eq_pi`), hence winding weight `π / 2π = ½`. So a
closed immersion running smoothly through `s` exactly `n` times has winding number `n / 2` modulo
an integer — in particular a single smooth crossing gives the `½` of the half-residue regime and
of the valence formula's elliptic point `i`. -/
theorem IsPwC1ImmersionOn.exists_int_windingNumber_eq_add_card_div_two
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} {T : Finset ℝ}
    (h_imm : IsPwC1ImmersionOn γ a b) (hab : a ≤ b) (hclosed : γ a = γ b) (hbase : γ a ≠ s)
    (hT : ∀ t, t ∈ T ↔ t ∈ Icc a b ∧ γ t = s)
    (hsmooth : ∀ t ∈ T, crossingAngle γ t = Real.pi) :
    ∃ k : ℤ, windingNumber γ a b s = k + (T.card : ℂ) / 2 := by
  obtain ⟨k, hk⟩ := h_imm.exists_int_windingNumber_eq_add_sum_crossingAngle hab hclosed hbase hT
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  refine ⟨k, ?_⟩
  rw [hk, Finset.sum_congr rfl hsmooth, Finset.sum_const, nsmul_eq_mul]
  push_cast
  field_simp


end TauCeti.Contour

end
