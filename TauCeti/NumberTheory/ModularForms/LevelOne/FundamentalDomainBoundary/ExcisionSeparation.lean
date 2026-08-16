/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.SingularSets

import TauCeti.Analysis.Contour.Curve.Distance

/-!
# The arc keeps its distance from the vertical excision centres

The principal-value assembly of the valence formula excises the union
`arcSingularSet S ∪ verticalSingularSet S`. Along the closed arc `[1, 3]` of the boundary
contour only the arc part can fire once `ε` is small: a vertical centre outside the arc set
never lies on the closed arc — the open arc has `|re| < 1/2` strictly, and the endpoints are
the corners `ρ + 1` and `ρ`, which the arc set contains *unconditionally* — so compactness
gives a positive distance from the arc to each such centre, uniform over the finitely many of
them. Below that distance the union excision test agrees with its arc part at every arc
parameter, which is what lets the arc pairing machinery, built for unit-norm inversion-closed
excision sets, apply to the union.

## Main declarations

* `TauCeti.ModularForm.exists_pos_forall_le_norm_fdBoundary_sub_of_mem_verticalSingularSet`:
  a positive `δ` under the distance from every arc point to every vertical centre outside the
  arc set.
* `TauCeti.ModularForm.exists_norm_fdBoundary_sub_le_union_iff`: for `ε` under that distance
  the union excision test along the arc reads the same as the arc-only test.
* `TauCeti.ModularForm.eventually_forall_lt_norm_fdBoundary_sub_of_mem_verticalSingularSet`:
  the separation holds for every sufficiently small `ε > 0`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/ArcContribution.lean`: the strict real-part
  bounds, the corner capture, the compactness minimum, and the `∀ᶠ` reduction of the union
  test to the arc test) this file ports onto the current Mathlib pin.
-/

public section

open Filter Metric Set Topology UpperHalfPlane

namespace TauCeti

namespace ModularForm

/-- On the open arc the real part lies strictly between `-1/2` and `1/2`: the angle runs
strictly inside `(π/3, 2π/3)`, where the cosine is strictly monotone. -/
private theorem re_fdBoundary_arc_strictly_between (H : ℝ) {t : ℝ} (ht : t ∈ Ioo (1 : ℝ) 3) :
    -(1 / 2) < (fdBoundary H t).re ∧ (fdBoundary H t).re < 1 / 2 := by
  rw [eqOn_fdBoundary_arc H ⟨ht.1.le, ht.2.le⟩, circleMap_zero_re, one_mul]
  have hpi := Real.pi_pos
  have hlo : Real.pi / 3 < (t + 1) * (Real.pi / 6) := by nlinarith [ht.1]
  have hhi : (t + 1) * (Real.pi / 6) < 2 * Real.pi / 3 := by nlinarith [ht.2]
  have hmem : (t + 1) * (Real.pi / 6) ∈ Icc 0 Real.pi :=
    ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  constructor
  · have h1 := Real.strictAntiOn_cos hmem ⟨by positivity, by linarith⟩ hhi
    have h23 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    have h2 : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
      rw [h23, Real.cos_pi_sub, Real.cos_pi_div_three]
    linarith
  · have h1 := Real.strictAntiOn_cos ⟨by positivity, by linarith⟩ hmem hlo
    rw [Real.cos_pi_div_three] at h1
    linarith

/-- A point of either vertical line that is not in the arc singular set never lies on the
closed arc: the open arc has `|re| < 1/2` strictly, and the endpoints are the corners `ρ + 1`
and `ρ`, which the arc singular set contains unconditionally. -/
private theorem fdBoundary_arc_ne_of_notMem_arcSingularSet {H : ℝ} {S : Finset ℍ} {s : ℂ}
    (hre : s.re = 1 / 2 ∨ s.re = -(1 / 2)) (hs : s ∉ arcSingularSet S) {t : ℝ}
    (ht : t ∈ Icc (1 : ℝ) 3) : fdBoundary H t ≠ s := by
  intro heq
  rcases ht.1.eq_or_lt with h1 | h1
  · rw [← h1, fdBoundary_apply_one] at heq
    exact hs (heq ▸ rho_add_one_mem_arcSingularSet S)
  · rcases ht.2.eq_or_lt with h3 | h3
    · rw [h3, fdBoundary_apply_three] at heq
      exact hs (heq ▸ rho_mem_arcSingularSet S)
    · have hb := re_fdBoundary_arc_strictly_between H ⟨h1, h3⟩
      rw [heq] at hb
      rcases hre with h | h <;> rw [h] at hb
      · linarith [hb.2]
      · linarith [hb.1]

/-- **The arc keeps a positive distance from the non-arc vertical centres.** The closed arc is
compact and misses every vertical centre outside the arc set, so each such centre sits at a
positive infimum distance from it, and a single `δ` under all the finitely many of them
works uniformly. -/
theorem exists_pos_forall_le_norm_fdBoundary_sub_of_mem_verticalSingularSet (H : ℝ)
    (S : Finset ℍ) :
    ∃ δ > 0, ∀ s ∈ verticalSingularSet S, s ∉ arcSingularSet S →
      ∀ t ∈ Icc (1 : ℝ) 3, δ ≤ ‖fdBoundary H t - s‖ := by
  classical
  set V : Finset ℂ := (verticalSingularSet S).filter (· ∉ arcSingularSet S)
  rcases V.eq_empty_or_nonempty with hVe | hVne
  · exact ⟨1, one_pos, fun s hsv hsna =>
      absurd (hVe ▸ Finset.mem_filter.mpr ⟨hsv, hsna⟩) (Finset.notMem_empty s)⟩
  have huIcc : uIcc (1 : ℝ) 3 = Icc 1 3 := uIcc_of_le (by norm_num)
  have hbound : ∀ s ∈ V, ∃ ρ > 0, ∀ t ∈ uIcc (1 : ℝ) 3, ρ ≤ ‖fdBoundary H t - s‖ := by
    intro s hsV
    obtain ⟨hsv, hsna⟩ := Finset.mem_filter.mp hsV
    exact Contour.exists_curve_dist_lower_bound (γ := fdBoundary H) (w := s)
      (continuous_fdBoundary H).continuousOn (by
        rw [huIcc]
        exact fun t ht => fdBoundary_arc_ne_of_notMem_arcSingularSet
          (re_eq_of_mem_verticalSingularSet hsv) hsna ht)
  choose! ρ hρpos hρbound using hbound
  exact ⟨V.inf' hVne ρ, (Finset.lt_inf'_iff hVne).mpr hρpos,
    fun s hsv hsna t ht => (Finset.inf'_le ρ (Finset.mem_filter.mpr ⟨hsv, hsna⟩)).trans
      (hρbound s (Finset.mem_filter.mpr ⟨hsv, hsna⟩) t (huIcc ▸ ht))⟩

/-- **Under the separation the union excision test degenerates to its arc part on the arc.**
The vertical centres already in the arc set are absorbed by it, and the remaining ones are
farther than `ε` from every arc point by `hfar`, so along the arc only the arc part of the
union can fire. -/
theorem exists_norm_fdBoundary_sub_le_union_iff {H ε : ℝ} {S : Finset ℍ}
    (hfar : ∀ s ∈ verticalSingularSet S, s ∉ arcSingularSet S →
      ∀ t ∈ Icc (1 : ℝ) 3, ε < ‖fdBoundary H t - s‖)
    {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 3) :
    (∃ s ∈ arcSingularSet S ∪ verticalSingularSet S, ‖fdBoundary H t - s‖ ≤ ε) ↔
      ∃ s ∈ arcSingularSet S, ‖fdBoundary H t - s‖ ≤ ε := by
  refine ⟨?_, fun ⟨s, hsa, hle⟩ => ⟨s, Finset.mem_union_left _ hsa, hle⟩⟩
  rintro ⟨s, hs, hle⟩
  rcases Finset.mem_union.mp hs with ha | hv
  · exact ⟨s, ha, hle⟩
  by_cases ha : s ∈ arcSingularSet S
  · exact ⟨s, ha, hle⟩
  · exact absurd hle (not_le.mpr (hfar s hv ha t ht))

/-- The separation of the arc from the non-arc vertical centres holds for every sufficiently
small `ε > 0`: the positive distance of
`exists_pos_forall_le_norm_fdBoundary_sub_of_mem_verticalSingularSet` dominates. -/
theorem eventually_forall_lt_norm_fdBoundary_sub_of_mem_verticalSingularSet (H : ℝ)
    (S : Finset ℍ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ s ∈ verticalSingularSet S, s ∉ arcSingularSet S →
      ∀ t ∈ Icc (1 : ℝ) 3, ε < ‖fdBoundary H t - s‖ := by
  obtain ⟨δ, hδ, hfar⟩ :=
    exists_pos_forall_le_norm_fdBoundary_sub_of_mem_verticalSingularSet H S
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε s hsv hsna t ht
  exact hε.2.trans_le (hfar s hsv hsna t ht)

end ModularForm

end TauCeti

end
