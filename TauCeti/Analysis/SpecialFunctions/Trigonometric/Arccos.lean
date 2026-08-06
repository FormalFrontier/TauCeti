/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Comparing an angle with an arccosine

Mathlib's `Analysis/SpecialFunctions/Trigonometric/Inverse.lean` carries a complete comparison
family for `Real.arcsin` — `Real.arcsin_le_iff_le_sin`, `Real.le_arcsin_iff_sin_le`,
`Real.arcsin_lt_iff_lt_sin`, `Real.lt_arcsin_iff_sin_lt` and their primed variants — turning an
inequality between an angle and an `arcsin` into one between a real number and a `sin`. It carries
no counterpart for `Real.arccos`: the pinned Mathlib knows `Real.arccos_le_arccos`,
`Real.arccos_lt_arccos` and `Real.cos_arccos`, but nothing that compares an *angle* with an
arccosine.

This file supplies that family, and reads it off as a description of the sublevel and superlevel
sets of `Real.cos` on one period. Since `arccos` is antitone, the comparisons swap sides:
`arccos x ≤ y ↔ cos y ≤ x` where the `arcsin` family has `arcsin x ≤ y ↔ x ≤ sin y`.

## Main results

* `Real.arccos_le_iff_cos_le`, `Real.le_arccos_iff_le_cos`, `Real.arccos_lt_iff_cos_lt` and
  `Real.lt_arccos_iff_lt_cos` — the four comparisons, for an angle `y` in `[0, π]`. Nothing at all
  is assumed of `x`: as with Mathlib's primed `arcsin` lemmas, the degenerate values `x < -1` and
  `1 < x`, where `arccos` is constant, are covered by excluding the one endpoint of `[0, π]` at
  which the comparison would fail.
* `Real.abs_lt_arccos_iff_lt_cos` and `Real.abs_le_arccos_iff_le_cos` — since `cos` is even, an
  angle `t` of the full period `[-π, π]` may be compared through `|t|`; here the excluded endpoint
  is paid for by a one-sided bound on `x` instead.
* `Real.lt_cos_iff_mem_Ioo` and `Real.le_cos_iff_mem_Icc` — the same statements read as
  `{t ∈ [-π, π] | x < cos t} = (-arccos x, arccos x)` and its closed companion: on one period
  centred at `0`, the angles at which `cos` exceeds a threshold form the symmetric interval of
  half-width `arccos x`.
* `Real.lt_cos_of_mem_Icc` — the unimodality corollary: `cos` has no interior minimum on `[-π, π]`,
  so a strict lower bound holding at both ends of a subinterval holds throughout it.

## The argument

Everything is `Real.arccos_eq_pi_div_two_sub_arcsin` fed into Mathlib's `arcsin` family, followed by
`Real.sin_pi_div_two_sub`; the four comparisons come in two proofs and two negations, exactly as the
`arcsin` family does. The `|t|` forms then split off the single degenerate angle that the
half-period statement does not reach, and the interval forms are `abs_lt` and `abs_le`.

This is general real analysis, extracted from two places that had proved fragments of it privately:
`TauCeti/Analysis/Complex/Conformal/Crosscut/Endpoints.lean`, which described a circular crosscut of
a disc as an angular arc of half-width `arccos (ρ / (2 * r))`, and
`TauCeti/Topology/Circle/Metric.lean`, which needed the unimodality corollary to see that a circle
meets a disc in a connected set of angles. Both belong to layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`, the Jordan-domain case of the Carathéodory boundary
correspondence, but neither statement mentions a holomorphic map, a disc, or even the plane.
-/

public section

namespace TauCeti

open Set

open scoped Real

/-- **An arccosine is at most an angle exactly when the angle's cosine is at most the value.** The
`Real.arccos` counterpart of Mathlib's `Real.le_arcsin_iff_sin_le'`, with the sides swapped because
`Real.arccos` is antitone.

The angle `y` is excluded from `π`, and in exchange nothing is assumed of `x`. At `y = π` the left
side is automatic and the right side, `-1 ≤ x`, is not; at the other endpoint `y = 0` the statement
is `Real.arccos_eq_zero`. -/
theorem _root_.Real.arccos_le_iff_cos_le {x y : ℝ} (hy : y ∈ Ico 0 π) :
    Real.arccos x ≤ y ↔ Real.cos y ≤ x := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin, sub_le_comm,
    Real.le_arcsin_iff_sin_le' ⟨by linarith [hy.2], by linarith [hy.1]⟩, Real.sin_pi_div_two_sub]

/-- **An angle is at most an arccosine exactly when the value is at most the angle's cosine.** The
`Real.arccos` counterpart of Mathlib's `Real.arcsin_le_iff_le_sin'`.

The angle `y` is excluded from `0`, and in exchange nothing is assumed of `x`. At `y = 0` the left
side is automatic and the right side, `x ≤ 1`, is not; at the other endpoint `y = π` the statement
is `Real.arccos_eq_pi`. -/
theorem _root_.Real.le_arccos_iff_le_cos {x y : ℝ} (hy : y ∈ Ioc 0 π) :
    y ≤ Real.arccos x ↔ x ≤ Real.cos y := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin, le_sub_comm,
    Real.arcsin_le_iff_le_sin' ⟨by linarith [hy.2], by linarith [hy.1]⟩, Real.sin_pi_div_two_sub]

/-- The strict companion of `Real.le_arccos_iff_le_cos`, by negation. -/
theorem _root_.Real.arccos_lt_iff_cos_lt {x y : ℝ} (hy : y ∈ Ioc 0 π) :
    Real.arccos x < y ↔ Real.cos y < x :=
  not_le.symm.trans <| (not_congr (Real.le_arccos_iff_le_cos hy)).trans not_le

/-- The strict companion of `Real.arccos_le_iff_cos_le`, by negation. -/
theorem _root_.Real.lt_arccos_iff_lt_cos {x y : ℝ} (hy : y ∈ Ico 0 π) :
    y < Real.arccos x ↔ x < Real.cos y :=
  not_le.symm.trans <| (not_congr (Real.arccos_le_iff_cos_le hy)).trans not_le

/-- **On a full period, a strict lower bound on the cosine is a strict upper bound on the angle.**
Because `Real.cos` is even, `Real.lt_arccos_iff_lt_cos` extends from `[0, π]` to `[-π, π]` read
through `|t|`. The angle is now allowed to reach `π`, at the cost of the hypothesis `-1 ≤ x`, which
is what makes the two sides agree there: both are false. -/
theorem _root_.Real.abs_lt_arccos_iff_lt_cos {x t : ℝ} (hx : -1 ≤ x) (ht : |t| ≤ π) :
    |t| < Real.arccos x ↔ x < Real.cos t := by
  rcases eq_or_lt_of_le ht with hπ | hπ
  · have hcos : Real.cos t = -1 := by rw [← Real.cos_abs, hπ, Real.cos_pi]
    refine iff_of_false ?_ ?_
    · rw [hπ]
      exact not_lt.mpr (Real.arccos_le_pi x)
    · rw [hcos]
      exact not_lt.mpr hx
  · rw [← Real.cos_abs t]
    exact Real.lt_arccos_iff_lt_cos ⟨abs_nonneg t, hπ⟩

/-- **On a full period, a lower bound on the cosine is an upper bound on the angle.** The weak
companion of `Real.abs_lt_arccos_iff_lt_cos`; here it is the angle `0` that the half-period
statement does not reach, and the hypothesis `x ≤ 1` that makes both sides true there. -/
theorem _root_.Real.abs_le_arccos_iff_le_cos {x t : ℝ} (hx : x ≤ 1) (ht : |t| ≤ π) :
    |t| ≤ Real.arccos x ↔ x ≤ Real.cos t := by
  rcases eq_or_lt_of_le (abs_nonneg t) with h0 | h0
  · have ht0 : t = 0 := abs_eq_zero.mp h0.symm
    subst ht0
    rw [abs_zero, Real.cos_zero]
    exact iff_of_true (Real.arccos_nonneg x) hx
  · rw [← Real.cos_abs t]
    exact Real.le_arccos_iff_le_cos ⟨h0, ht⟩

/-- **The cosine exceeds a threshold on a symmetric interval.** On the period `[-π, π]` the angles
at which `Real.cos` exceeds `x` are exactly those of `(-arccos x, arccos x)`. -/
theorem _root_.Real.lt_cos_iff_mem_Ioo {x t : ℝ} (hx : -1 ≤ x) (ht : t ∈ Icc (-π) π) :
    x < Real.cos t ↔ t ∈ Ioo (-Real.arccos x) (Real.arccos x) := by
  rw [← Real.abs_lt_arccos_iff_lt_cos hx (abs_le.mpr ⟨ht.1, ht.2⟩), abs_lt, mem_Ioo]

/-- **The cosine reaches a threshold on a symmetric closed interval.** The weak companion of
`Real.lt_cos_iff_mem_Ioo`. -/
theorem _root_.Real.le_cos_iff_mem_Icc {x t : ℝ} (hx : x ≤ 1) (ht : t ∈ Icc (-π) π) :
    x ≤ Real.cos t ↔ t ∈ Icc (-Real.arccos x) (Real.arccos x) := by
  rw [← Real.abs_le_arccos_iff_le_cos hx (abs_le.mpr ⟨ht.1, ht.2⟩), abs_le, mem_Icc]

/-- **The cosine has no interior minimum on `[-π, π]`.** If `k < cos a` and `k < cos b`, with
`-π ≤ a` and `b ≤ π`, then `k < cos θ` for every `θ ∈ [a, b]`.

This is `Real.lt_cos_iff_mem_Ioo` read as unimodality: below `-1` the bound is vacuous, and above it
the angles admitted form an interval symmetric about `0`, which therefore contains `[a, b]` as soon
as it contains both endpoints. -/
theorem _root_.Real.lt_cos_of_mem_Icc {k a b θ : ℝ} (ha : -π ≤ a) (hb : b ≤ π) (hθ : θ ∈ Icc a b)
    (hka : k < Real.cos a) (hkb : k < Real.cos b) : k < Real.cos θ := by
  rcases lt_or_ge k (-1) with hk | hk
  · exact hk.trans_le (Real.neg_one_le_cos θ)
  · have hab : a ≤ b := hθ.1.trans hθ.2
    rw [← Real.abs_lt_arccos_iff_lt_cos hk (abs_le.mpr ⟨ha, hab.trans hb⟩)] at hka
    rw [← Real.abs_lt_arccos_iff_lt_cos hk (abs_le.mpr ⟨ha.trans hab, hb⟩)] at hkb
    rw [← Real.abs_lt_arccos_iff_lt_cos hk (abs_le.mpr ⟨ha.trans hθ.1, hθ.2.trans hb⟩)]
    exact (abs_le_max_abs_abs hθ.1 hθ.2).trans_lt (max_lt hka hkb)

end TauCeti
