/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic

import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Deriv

/-!
# The vertical integrals of a periodic integrand cancel

The reflection `t ↦ 4 - t` carries the right vertical of the boundary contour onto the
left vertical through the translation `z ↦ z - 1`, reversing the orientation. For any
integrand `φ` of period `1` — the level-one situation, where `φ` is the logarithmic
derivative of the extension of a modular form — the left vertical contour integral of
`γ' • φ ∘ γ` is therefore the negative of the right one: the values are identified by
periodicity and the derivatives by the reflection, up to the orientation sign. The
statement is unconditional: the substitution and the interior congruence need no
integrability.

The cancellation also survives `ε`-excision, which is what the principal-value assembly of
the valence formula needs: when the form vanishes at a point *on* the contour the integrand
is not interval-integrable there, so the boundary integral is assembled from an excised
integrand and the limit taken only after the pieces are combined. The excised cancellation
holds whenever the excision set is invariant under the reflection `z ↦ -conj z` that
exchanges the two verticals — reflection invariance, not translation closure, is the usable
hypothesis, since a finite set closed under `s ↦ s + 1` is empty.

## Main declarations

* `TauCeti.ModularForm.intervalIntegral_fdBoundarySegment4_eq_neg_segment1`.
* `TauCeti.ModularForm.intervalIntegral_excised_fdBoundarySegment4_eq_neg_segment1`: the
  same cancellation for a reflection-invariantly excised integrand.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/Assembly.lean`, the vertical
  cancellation) this file ports onto the current Mathlib pin.
-/

public section

open MeasureTheory Set

namespace TauCeti

namespace ModularForm

/-- The left vertical integral of a period-`1` integrand along the boundary contour is
the negative of the right vertical integral: the reflection `t ↦ 4 - t` carries the
right vertical onto the left through the translation `z ↦ z - 1`, which the periodicity
absorbs, and reverses the orientation. -/
theorem intervalIntegral_fdBoundarySegment4_eq_neg_segment1 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (H : ℝ) {φ : ℂ → E}
    (hφ : Function.Periodic φ 1) :
    ∫ t in (3 : ℝ)..4, deriv (fdBoundary H) t • φ (fdBoundary H t) =
      -∫ t in (0 : ℝ)..1, deriv (fdBoundary H) t • φ (fdBoundary H t) := by
  have hsub : (∫ t in (3 : ℝ)..4, deriv (fdBoundary H) t • φ (fdBoundary H t)) =
      ∫ u in (0 : ℝ)..1, deriv (fdBoundary H) (4 - u) • φ (fdBoundary H (4 - u)) := by
    have h41 : (4 : ℝ) - 1 = 3 := by norm_num
    have h40 : (4 : ℝ) - 0 = 4 := by norm_num
    have h := intervalIntegral_comp_fdBoundary_four_sub H φ (a := 0) (b := 1)
    rwa [h41, h40] at h
  rw [hsub, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun u hu ↦ ?_
  rw [fdBoundary_four_sub_vertical H ⟨hu.1.le, hu.2.le⟩,
    deriv_fdBoundary_four_sub_vertical H hu, hφ.sub_eq, neg_smul]

/-- The right-vertical integrability of a period-`1` integrand reflects to the left
vertical: the reflection carries the integrand to its negation through the translation
and the periodicity. -/
theorem intervalIntegrable_deriv_smul_fdBoundarySegment4 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {H : ℝ} {φ : ℂ → E}
    (hφ : Function.Periodic φ 1)
    (hint : IntervalIntegrable (fun t ↦ deriv (fdBoundary H) t • φ (fdBoundary H t))
      volume 0 1) :
    IntervalIntegrable (fun t ↦ deriv (fdBoundary H) t • φ (fdBoundary H t))
      volume 3 4 := by
  have hI := (hint.neg.comp_sub_left 4).symm
  have h41 : (4 : ℝ) - 1 = 3 := by norm_num
  have h40 : (4 : ℝ) - 0 = 4 := by norm_num
  rw [h40, h41] at hI
  refine hI.congr_uIoo ?_
  rw [Set.uIoo_of_le (by norm_num : (3 : ℝ) ≤ 4)]
  intro x hx
  have hu : 4 - x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hval := fdBoundary_four_sub_vertical H ⟨hu.1.le, hu.2.le⟩
  have hder := deriv_fdBoundary_four_sub_vertical H hu
  have hxx : (4 : ℝ) - (4 - x) = x := by ring
  rw [hxx] at hval hder
  have hval' : fdBoundary H (4 - x) = fdBoundary H x + 1 := by linear_combination -hval
  have hder' : deriv (fdBoundary H) (4 - x) = -deriv (fdBoundary H) x := by
    linear_combination hder
  simp only [Pi.neg_apply, hval', hder', hφ (fdBoundary H x), neg_smul, neg_neg]

/-- **The excision test is invariant under the vertical reflection.** On the verticals the
substitution `t ↦ 4 - t` acts as `z ↦ -conj z`, since there the real part is `±1/2`. That map
is an isometry of `ℂ`, so it carries the `ε`-ball around a centre to the `ε`-ball around the
reflected centre; for an excision set closed under the reflection the test therefore reads the
same at `4 - u` as at `u`.

Reflection invariance, not translation closure, is the right hypothesis: a finite set closed
under `s ↦ s + 1` would have to be empty, since it has an element of largest real part. -/
theorem exists_norm_fdBoundary_four_sub_le_iff {H : ℝ} {S : Finset ℂ} {ε : ℝ}
    (hrefl : ∀ s ∈ S, -(starRingEnd ℂ) s ∈ S) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∃ s ∈ S, ‖fdBoundary H (4 - u) - s‖ ≤ ε) ↔ ∃ s ∈ S, ‖fdBoundary H u - s‖ ≤ ε := by
  have hval : fdBoundary H (4 - u) = fdBoundary H u - 1 :=
    fdBoundary_four_sub_vertical H ⟨hu.1.le, hu.2.le⟩
  have hconj : fdBoundary H (4 - u) = -(starRingEnd ℂ) (fdBoundary H u) := by
    rw [hval]
    refine Complex.ext ?_ ?_ <;> simp [re_fdBoundary_of_le_one hu.2.le]
    norm_num
  have hdist : ∀ s : ℂ, ‖fdBoundary H (4 - u) - s‖
      = ‖fdBoundary H u - -(starRingEnd ℂ) s‖ := by
    intro s
    have hneg : -fdBoundary H u - (starRingEnd ℂ) s
        = -(fdBoundary H u - -(starRingEnd ℂ) s) := by ring
    rw [hconj, ← Complex.norm_conj (-(starRingEnd ℂ) (fdBoundary H u) - s)]
    simp only [map_sub, map_neg, Complex.conj_conj]
    rw [hneg, norm_neg]
  refine ⟨fun ⟨s, hs, hle⟩ => ⟨-(starRingEnd ℂ) s, hrefl s hs, by rwa [← hdist s]⟩,
    fun ⟨s, hs, hle⟩ => ⟨-(starRingEnd ℂ) s, hrefl s hs, ?_⟩⟩
  rw [hdist, map_neg, Complex.conj_conj, neg_neg]
  exact hle

/-- **Integrability on the left vertical, excised.** The reflection `t ↦ 4 - t` carries the
right vertical onto the left, and it carries the excised integrand to itself: the excision
test transports by `exists_norm_fdBoundary_four_sub_le_iff`, and the integrand's value by the
periodicity already used without the excision. -/
theorem intervalIntegrable_excised_deriv_smul_fdBoundarySegment4 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {H : ℝ} {φ : ℂ → E}
    (hφ : Function.Periodic φ 1) {S : Finset ℂ} {ε : ℝ}
    (hrefl : ∀ s ∈ S, -(starRingEnd ℂ) s ∈ S)
    (hint : IntervalIntegrable (fun t ↦ deriv (fdBoundary H) t •
      (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0 else φ (fdBoundary H t))) volume 0 1) :
    IntervalIntegrable (fun t ↦ deriv (fdBoundary H) t •
      (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0 else φ (fdBoundary H t))) volume 3 4 := by
  have hI := (hint.neg.comp_sub_left 4).symm
  norm_num at hI
  refine hI.congr_uIoo ?_
  rw [Set.uIoo_of_le (by norm_num : (3 : ℝ) ≤ 4)]
  intro x hx
  have hu : 4 - x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hiff := exists_norm_fdBoundary_four_sub_le_iff (H := H) (ε := ε) hrefl hu
  have hval : fdBoundary H (4 - (4 - x)) = fdBoundary H (4 - x) - 1 :=
    fdBoundary_four_sub_vertical H ⟨hu.1.le, hu.2.le⟩
  have hder := deriv_fdBoundary_four_sub_vertical H hu
  rw [sub_sub_self] at hval hder hiff
  by_cases hc : ∃ s ∈ S, ‖fdBoundary H (4 - x) - s‖ ≤ ε
  · simp only [ite_eq_left hc, ite_eq_left (hiff.mpr hc), smul_zero, neg_zero]
  · -- Discharge both `if`s first: rewriting values inside a live condition would stop
    -- `ite_eq_right` from matching it.
    simp only [ite_eq_right hc, ite_eq_right fun h => hc (hiff.mp h)]
    simp only [hval, hφ.sub_eq, hder, neg_smul]

/-- **The vertical cancellation survives excision.** The reflection `t ↦ 4 - t` carries the right
vertical onto the left by `z ↦ -conj z`, an isometry of `ℂ`, so an integrand excised within `ε`
of a set invariant under that reflection is excised at matching parameters on the two verticals,
and the cancellation of the untruncated integrals
(`TauCeti.ModularForm.intervalIntegral_fdBoundarySegment4_eq_neg_segment1`) persists.

Reflection invariance, not translation closure, is the right hypothesis: the two verticals are
exchanged by `z ↦ -conj z`, and being an isometry it moves an `ε`-ball to an `ε`-ball. (A set
closed under the bare translation `s ↦ s + 1` would have to be empty, since a finite set has an
element of largest real part.) For `TauCeti.ModularForm.verticalSingularSet` the invariance is the
composite of `re_eq_of_mem_verticalSingularSet` with `sub_one_mem_verticalSingularSet` or
`add_one_mem_verticalSingularSet`, whose translations are conditional on the real part. -/
theorem intervalIntegral_excised_fdBoundarySegment4_eq_neg_segment1 {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (H : ℝ) {φ : ℂ → E}
    (hφ : Function.Periodic φ 1) {S : Finset ℂ} {ε : ℝ}
    (hrefl : ∀ s ∈ S, -(starRingEnd ℂ) s ∈ S) :
    (∫ t in (3 : ℝ)..4, deriv (fdBoundary H) t •
        (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0 else φ (fdBoundary H t))) =
      -∫ t in (0 : ℝ)..1, deriv (fdBoundary H) t •
        (if ∃ s ∈ S, ‖fdBoundary H t - s‖ ≤ ε then 0 else φ (fdBoundary H t)) := by
  -- The substitution is the boundary-specific combinator, applied to the excised integrand.
  have h41 : (4 : ℝ) - 1 = 3 := by norm_num
  have h40 : (4 : ℝ) - 0 = 4 := by norm_num
  have hcomp := intervalIntegral_comp_fdBoundary_four_sub H
    (fun z => if ∃ s ∈ S, ‖z - s‖ ≤ ε then (0 : E) else φ z) (a := 0) (b := 1)
  -- Only the endpoints need normalizing; `norm_num` here would also distribute the
  -- scalar into the branches of the `if` and stop matching the goal.
  simp only [h41, h40] at hcomp
  rw [hcomp, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun u hu => ?_
  have hiff := exists_norm_fdBoundary_four_sub_le_iff (H := H) (ε := ε) hrefl hu
  have hval : fdBoundary H (4 - u) = fdBoundary H u - 1 :=
    fdBoundary_four_sub_vertical H ⟨hu.1.le, hu.2.le⟩
  by_cases hc : ∃ s ∈ S, ‖fdBoundary H u - s‖ ≤ ε
  · rw [ite_eq_left (hiff.mpr hc), ite_eq_left hc, smul_zero, smul_zero, neg_zero]
  · rw [ite_eq_right fun h => hc (hiff.mp h), ite_eq_right hc, hval,
      deriv_fdBoundary_four_sub_vertical H hu, hφ.sub_eq, neg_smul]

end ModularForm

end TauCeti

end
