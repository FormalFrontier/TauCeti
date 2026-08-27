/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Crossing.Decomposition
public import TauCeti.Analysis.Contour.Crossing.ExitWindow
public import TauCeti.Analysis.Contour.Crossing.Finiteness
public import TauCeti.Analysis.Contour.Crossing.Windows

/-!
# Winding decomposition of an immersed contour

This file completes Hungerbühler--Wasem Proposition 2.2.  A closed piecewise-`C¹` immersion
meets a point at finitely many parameters.  Simultaneously replacing small neighbourhoods of
those crossings by circular caps gives a closed piecewise-`C¹` curve avoiding the point, and
the original winding number is the winding number of that avoiding curve plus the sum of the
crossing angles divided by `2π`.

The proof selects one common parameter radius below all the local principal-value radii, then one
common spatial radius reached on both sides of every crossing.  The resulting first-exit windows
are strictly ordered.  `Crossing.Decomposition` supplies their finite winding-number accounting,
while `Crossing.ExitWindow` evaluates every local window-minus-cap contribution.

## Main result

* `TauCeti.Contour.IsPwC1ImmersionOn.exists_windingNumber_eq_avoiding_add_sum_crossingAngle` --
  **Hungerbühler--Wasem Proposition 2.2**: the winding decomposition over the canonical finite
  crossing set.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 (2018), Proposition 2.2.

## Provenance

Independently assembled from Tau Ceti's finite-excision and exit-window APIs; no external Lean
formalization is copied or adapted.  The `ContourIntegration` roadmap designates the AINTLIB
`LeanModularForms` development as a source for this area, but its crossing files do not contain
this excise-and-cap winding decomposition.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set

/-- **Hungerbühler--Wasem Proposition 2.2 (finite-crossing winding decomposition).**
Let `γ` be a closed piecewise-`C¹` immersion on a nondegenerate interval, based away from `s`.
There is a closed piecewise-`C¹` curve `γ₀` avoiding `s` whose winding number accounts for the
integer part of the generalized winding number of `γ`; the remaining contribution is the sum of
the crossing angles over exactly the parameters where `γ` meets `s`:

`n_s(γ) = n_s(γ₀) + ∑_{γ(t)=s} crossingAngle(γ,t) / 2π`.

The witness `γ₀` is obtained by replacing pairwise disjoint first-exit windows around all
crossings by equal-radius circular caps.  The statement deliberately exposes only the resulting
curve and its defining geometric properties, not the auxiliary radii or tangent choices used to
construct it. -/
theorem IsPwC1ImmersionOn.exists_windingNumber_eq_avoiding_add_sum_crossingAngle
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} (h_imm : IsPwC1ImmersionOn γ a b) (hab : a < b)
    (hclosed : γ a = γ b) (hbase : γ a ≠ s) :
    ∃ γ₀ : ℝ → ℂ,
      IsPiecewiseC1On γ₀ a b ∧ γ₀ a = γ₀ b ∧ (∀ t ∈ Icc a b, γ₀ t ≠ s) ∧
        windingNumber γ a b s = windingNumber γ₀ a b s +
          ∑ t ∈ (h_imm.finite_crossings (z₀ := s)).toFinset,
            (crossingAngle γ t : ℂ) / (2 * (Real.pi : ℂ)) := by
  classical
  let T := (h_imm.finite_crossings (z₀ := s)).toFinset
  have hT : ∀ t, t ∈ T ↔ t ∈ Icc a b ∧ γ t = s := by
    intro t
    change t ∈ (h_imm.finite_crossings (z₀ := s)).toFinset ↔ _
    rw [h_imm.mem_toFinset_finite_crossings, uIcc_of_le hab.le]
  have h_at : ∀ t ∈ T, γ t = s := fun t ht => (hT t).mp ht |>.2
  have h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ T :=
    fun t ht hγt => (hT t).mpr ⟨ht, hγt⟩
  have h_Ioo : ∀ t ∈ T, t ∈ Ioo a b := by
    intro t ht
    obtain ⟨⟨hat, htb⟩, hγt⟩ := (hT t).mp ht
    refine ⟨lt_of_le_of_ne hat ?_, lt_of_le_of_ne htb ?_⟩
    · rintro rfl
      exact hbase hγt
    · rintro rfl
      exact hbase (hclosed.trans hγt)
  choose! R hR_pos L_R L_L hL_R hL_L h_R h_L h_pv using
    fun t (ht : t ∈ T) =>
      exists_radius_hasCauchyPVAt_exitCapWindow h_imm hab (h_Ioo t ht) (h_at t ht)
  obtain ⟨δ, hδ, h_endpoints, h_separated, hδR⟩ :=
    exists_common_window_radius_le h_Ioo R hR_pos
  have h_unique : ∀ t₀ ∈ T, ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), γ t = s → t = t₀ := by
    intro t₀ ht₀ t ht hγt
    exact eq_of_mem_window_of_eq_of_lt_of_two_mul_lt (h_endpoints t₀ ht₀)
      (h_separated t₀ ht₀) h_complete ht hγt
  have hγ_window : ∀ t ∈ T, ContinuousOn γ (Icc (t - δ) (t + δ)) := by
    intro t ht
    apply h_imm.continuousOn.mono
    rw [uIcc_of_le hab.le]
    exact Icc_subset_Icc (by linarith [(h_endpoints t ht).1])
      (by linarith [(h_endpoints t ht).2])
  have h_window_endpoints : ∀ t ∈ T, γ (t - δ) ≠ s ∧ γ (t + δ) ≠ s := by
    intro t ht
    constructor
    · intro heq
      have := h_unique t ht (t - δ) ⟨le_rfl, by linarith [hδ]⟩ heq
      linarith
    · intro heq
      have := h_unique t ht (t + δ) ⟨by linarith [hδ], le_rfl⟩ heq
      linarith
  obtain ⟨ε, hε, hε_endpoints, h_crossing_mem⟩ :=
    exists_common_exitCapWindows_radius hδ hγ_window h_at h_window_endpoints
      (L_R := L_R) (L_L := L_L)
  let windows := exitCapWindows γ s T δ ε L_R L_L
  have hεL : ∀ t ∈ T, ε ≤ ‖γ (t - δ) - s‖ := fun t ht => (hε_endpoints t ht).1
  have hεR : ∀ t ∈ T, ε ≤ ‖γ (t + δ) - s‖ := fun t ht => (hε_endpoints t ht).2
  have hordered : windows.Pairwise fun W V => W.upper < V.lower := by
    exact pairwise_upper_lt_lower_exitCapWindows hδ.le hεL hεR
      (fun t ht t' ht' hne => h_separated t ht t' ht' hne.symm)
  have hinside : ∀ W ∈ windows, a < W.lower ∧ W.lower < W.upper ∧ W.upper < b := by
    intro W hW
    refine ⟨lt_lower_of_mem_exitCapWindows hδ.le
      (fun t ht => by linarith [(h_endpoints t ht).1]) hεL hW, ?_,
      upper_lt_of_mem_exitCapWindows hδ.le
        (fun t ht => by linarith [(h_endpoints t ht).2]) hεR hW⟩
    exact lower_lt_upper_of_mem_exitCapWindows hδ hε hγ_window h_at hεL hεR hW
  have hradius : ∀ W ∈ windows, W.radius ≠ 0 := by
    intro W hW
    rw [radius_eq_of_mem_exitCapWindows hW]
    exact hε.ne'
  have havoid : ∀ t ∈ Icc a b,
      (∀ W ∈ windows, t ∉ Ioo W.lower W.upper) → γ t ≠ s := by
    intro t ht hnot hγt
    have htT := h_complete t ht hγt
    let W := exitCapWindow γ s t δ ε (L_R t) (L_L t)
    have hW : W ∈ windows := by
      exact mem_exitCapWindows_iff.mpr ⟨t, htT, rfl⟩
    exact hnot W hW (h_crossing_mem t htT)
  have hpv : ∀ W ∈ windows,
      CauchyPVExistsAt γ W.lower W.upper (fun z => (z - s)⁻¹) s := by
    intro W hW
    obtain ⟨t, ht, rfl⟩ := mem_exitCapWindows_iff.mp hW
    apply CauchyPVExistsAt.intro
    exact h_pv t ht δ hδ (hδR t ht)
      (by linarith [(h_endpoints t ht).1])
      (by linarith [(h_endpoints t ht).2]) (h_unique t ht) ε hε (hεL t ht) (hεR t ht)
  have hstart : ∀ W ∈ windows, γ W.lower = circleMap s W.radius W.startAngle := by
    intro W hW
    exact eq_circleMap_startAngle_of_mem_exitCapWindows hδ hε
      (fun t ht => (hγ_window t ht).mono (Icc_subset_Icc le_rfl (by linarith)))
      h_at hεL hW
  have hend : ∀ W ∈ windows, γ W.upper = circleMap s W.radius W.endAngle := by
    intro W hW
    exact eq_circleMap_endAngle_of_mem_exitCapWindows hδ hε hγ_window h_at hεL hεR
      hL_R hL_L h_R h_L hW
  have hlocal : ∀ t ∈ T,
      (exitCapWindow γ s t δ ε (L_R t) (L_L t)).localContribution γ s =
        (crossingAngle γ t : ℂ) / (2 * (Real.pi : ℂ)) := by
    intro t ht
    let W := exitCapWindow γ s t δ ε (L_R t) (L_L t)
    have hW : W ∈ windows := mem_exitCapWindows_iff.mpr ⟨t, ht, rfl⟩
    rw [W.localContribution_eq_sub_windingNumber_cap γ s
      (hradius W hW) (hinside W hW).2.1.ne]
    exact windingNumber_sub_cap_exitCapWindow_eq_crossingAngle_div_two_pi hδ hε (h_at t ht)
      (hγ_window t ht) (hεL t ht) (hεR t ht) (hL_R t ht) (hL_L t ht)
      (h_R t ht) (h_L t ht)
      (h_pv t ht δ hδ (hδR t ht)
        (by linarith [(h_endpoints t ht).1])
        (by linarith [(h_endpoints t ht).2]) (h_unique t ht) ε hε (hεL t ht) (hεR t ht))
  have hsum : (windows.map fun W => W.localContribution γ s).sum =
      ∑ t ∈ T, (crossingAngle γ t : ℂ) / (2 * (Real.pi : ℂ)) := by
    change (exitCapWindows γ s T δ ε L_R L_L |>.map
      fun W => W.localContribution γ s).sum = _
    rw [sum_map_exitCapWindows]
    exact Finset.sum_congr rfl hlocal
  let γ₀ := exciseCrossings γ s windows
  have hγ₀ : IsPiecewiseC1On γ₀ a b :=
    h_imm.isPiecewiseC1On.exciseCrossings
      (pairwise_disjoint_interval_of_pairwise_upper_lt_lower hordered) hinside hstart hend
  have hclosed₀ : γ₀ a = γ₀ b := by
    apply exciseCrossings_closed hclosed
    intro W hW
    exact ⟨fun haW => by
      rw [CircularCapWindow.mem_interval_iff] at haW
      exact (not_lt_of_ge haW.1) (hinside W hW).1,
      fun hbW => by
        rw [CircularCapWindow.mem_interval_iff] at hbW
        exact (not_lt_of_ge hbW.2) (hinside W hW).2.2⟩
  have havoid₀ : ∀ t ∈ Icc a b, γ₀ t ≠ s := by
    apply exciseCrossings_ne_center
    · intro W hW _
      exact hradius W hW
    · intro t ht hγt
      have htT := h_complete t ht hγt
      refine ⟨exitCapWindow γ s t δ ε (L_R t) (L_L t),
        mem_exitCapWindows_iff.mpr ⟨t, htT, rfl⟩, ?_⟩
      rw [CircularCapWindow.mem_interval_iff]
      exact ⟨(h_crossing_mem t htT).1.le, (h_crossing_mem t htT).2.le⟩
  refine ⟨γ₀, hγ₀, hclosed₀, havoid₀, ?_⟩
  rw [windingNumber_eq_exciseCrossings_add_sum h_imm.isPiecewiseC1On hordered hinside
    hradius havoid hpv, hsum]

end TauCeti.Contour

end
