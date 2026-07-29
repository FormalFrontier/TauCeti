/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.PiecewiseC1On
public import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Piecewise `C¹` immersions on an interval

The on-cycle Layer 4 targets of the contour-integration roadmap — the Hungerbühler–Wasem
generalized residue theorem and its half-residue specialisation — are stated for a **piecewise
`C¹` immersion**: a piecewise-`C¹` curve whose within-piece derivative is non-vanishing on every
closed piece, one-sided at the piece endpoints. This file introduces that regularity as the
predicate `Contour.IsPwC1ImmersionOn γ a b` on the raw function `γ` — the roadmap's pinned
definition, verbatim — together with its basic API.

The non-vanishing tangent is what the on-cycle theory needs and the plain `IsPiecewiseC1On`
cannot supply: Hungerbühler–Wasem represent each on-cycle singularity by model sectors of a
definite opening angle, which requires a well-defined non-zero tangent there. The one-sided
conditions are load-bearing: merely asking `deriv γ ≠ 0` off a finite set would admit zero-speed
turnarounds (`γ t = t ^ 2` on `[-1, 1]`, whose one-sided tangents both vanish at `0`) and
zero-speed seams of a closed curve, which are not immersions. `derivWithin` is used because at a
corner the global `deriv` is `0` by Mathlib convention, which would falsely contradict
non-vanishing; at interior points of a piece it agrees with `deriv`. (The homology Cauchy
theorem, whose singularities lie *off* the curve, needs only `IsPiecewiseC1On`.)

## Main definitions

* `Contour.IsPwC1ImmersionOn γ a b` — over a common finite breakpoint set, every breakpoint-free
  closed subinterval of `[[a, b]]` carries a `C¹` restriction with non-vanishing within-piece
  derivative.

## Main results

* `Contour.isPwC1ImmersionOn_iff` — unfold the predicate to its defining clauses.
* `Contour.IsPwC1ImmersionOn.isPiecewiseC1On` — an immersion is in particular piecewise `C¹`,
  with the same breakpoint witness.
* `Contour.IsPwC1ImmersionOn.continuousOn` — the underlying continuity on `[[a, b]]`.
* `Contour.IsPwC1ImmersionOn.of_breakpoints`, `Contour.IsPwC1ImmersionOn.exists_breakpoints` —
  introduce the predicate from, and eliminate it to, a finite breakpoint witness.
* `Contour.isPwC1ImmersionOn_comm`, `Contour.IsPwC1ImmersionOn.symm` — endpoint-swap invariance.
* `Contour.IsPwC1ImmersionOn.exists_deriv_slope_right_limit`,
  `Contour.IsPwC1ImmersionOn.exists_deriv_slope_left_limit` — the same one-sided tangent as the
  limit of both `deriv γ` and the chord slope `(γ t - γ t₀) / (t - t₀)`; the chord form is what
  the crossing angle needs.
* `Contour.IsPwC1ImmersionOn.exists_deriv_right_limit`,
  `Contour.IsPwC1ImmersionOn.exists_deriv_left_limit` — the tangent-limit projections of
  `exists_deriv_slope_right_limit` and `exists_deriv_slope_left_limit`.

## Provenance

The raw-function mirror of the `ClosedPwC1Immersion` structure of the AINTLIB `LeanModularForms`
development (`PaperPwC1Immersion.lean`): the pieces clause matches its `contDiffOn_pieces` and
`derivWithin_ne_zero_pieces` fields — Hungerbühler–Wasem's `Λ̇|_{[aₖ,aₖ₊₁]} ≠ 0` (arXiv:1808.00997,
p. 3) — whose closed partition includes the interval endpoints, so the seam of a closed curve is
constrained too. Closedness itself (`γ a = γ b`) stays a separate hypothesis of the theorems. The
definition is pinned in the roadmap (`TauCetiRoadmap/ContourIntegration/Suggested.lean`).
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter Set Topology

variable {γ : ℝ → ℂ} {a b : ℝ}

/-- **Piecewise-`C¹` immersion on the interval between `a` and `b`.** The curve `γ : ℝ → ℂ` is
continuous on `[[a, b]]` and, over a common finite breakpoint set
`p ⊆ (min a b, max a b)`, every breakpoint-free closed subinterval `[c, d]` carries a `C¹`
restriction whose within-piece derivative is non-vanishing on **all** of `[c, d]` — one-sided at
the piece endpoints, including at `a` and `b`. This strengthens `IsPiecewiseC1On` by a
non-vanishing tangent on every piece (`IsPwC1ImmersionOn.isPiecewiseC1On`); the `c < d` guard
excludes degenerate pieces, on which `derivWithin` is not meaningful. -/
def IsPwC1ImmersionOn (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ContinuousOn γ (uIcc a b) ∧
    ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
      ∀ c d : ℝ, c < d → Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
        ContDiffOn ℝ 1 γ (Icc c d) ∧
          ∀ t ∈ Icc c d, derivWithin γ (Icc c d) t ≠ 0

/-- `IsPwC1ImmersionOn` unfolded to its defining clauses: continuity on `[[a, b]]`, and a finite
breakpoint set off which every breakpoint-free closed subinterval carries a `C¹` restriction with
non-vanishing within-piece derivative. -/
theorem isPwC1ImmersionOn_iff :
    IsPwC1ImmersionOn γ a b ↔
      ContinuousOn γ (uIcc a b) ∧
        ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
          ∀ c d : ℝ, c < d → Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
            ContDiffOn ℝ 1 γ (Icc c d) ∧
              ∀ t ∈ Icc c d, derivWithin γ (Icc c d) t ≠ 0 :=
  Iff.rfl

/-- A piecewise-`C¹` immersion is continuous on the parameter interval `[[a, b]]`. -/
theorem IsPwC1ImmersionOn.continuousOn (h : IsPwC1ImmersionOn γ a b) :
    ContinuousOn γ (uIcc a b) :=
  h.1

/-- Build a piecewise-`C¹` immersion from continuity on `[[a, b]]` together with a finite
breakpoint set off which every breakpoint-free closed subinterval carries a `C¹` restriction with
non-vanishing within-piece derivative. -/
theorem IsPwC1ImmersionOn.of_breakpoints (hcont : ContinuousOn γ (uIcc a b)) (p : Finset ℝ)
    (hp : ↑p ⊆ Ioo (min a b) (max a b))
    (hpieces : ∀ c d : ℝ, c < d → Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
      ContDiffOn ℝ 1 γ (Icc c d) ∧ ∀ t ∈ Icc c d, derivWithin γ (Icc c d) t ≠ 0) :
    IsPwC1ImmersionOn γ a b :=
  ⟨hcont, p, hp, hpieces⟩

/-- Extract the finite breakpoint set of a piecewise-`C¹` immersion, together with the `C¹`
restriction and the non-vanishing within-piece derivative it induces on every breakpoint-free
closed subinterval of `[[a, b]]`. -/
theorem IsPwC1ImmersionOn.exists_breakpoints (h : IsPwC1ImmersionOn γ a b) :
    ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
      ∀ c d : ℝ, c < d → Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
        ContDiffOn ℝ 1 γ (Icc c d) ∧
          ∀ t ∈ Icc c d, derivWithin γ (Icc c d) t ≠ 0 :=
  h.2

/-- A piecewise-`C¹` immersion is in particular piecewise `C¹`, with the same breakpoint
witness. -/
theorem IsPwC1ImmersionOn.isPiecewiseC1On (h : IsPwC1ImmersionOn γ a b) :
    IsPiecewiseC1On γ a b := by
  obtain ⟨hcont, p, hp, hpieces⟩ := h
  refine IsPiecewiseC1On.of_breakpoints hcont p hp fun c d hsub hdisj => ?_
  rcases lt_trichotomy c d with hlt | rfl | hgt
  · exact (hpieces c d hlt hsub hdisj).1
  · rw [Icc_self]
    exact fun x hx => by rw [mem_singleton_iff] at hx; subst hx; exact contDiffWithinAt_singleton
  · simp [Icc_eq_empty (not_le.mpr hgt)]

/-- Piecewise-`C¹`-immersion regularity is symmetric in the endpoints, since
`[[a, b]] = [[b, a]]`. -/
theorem isPwC1ImmersionOn_comm : IsPwC1ImmersionOn γ a b ↔ IsPwC1ImmersionOn γ b a := by
  simp only [isPwC1ImmersionOn_iff, Set.uIcc_comm a b, min_comm a b, max_comm a b]

/-- Piecewise-`C¹`-immersion regularity is invariant under swapping the endpoints of the
interval. -/
theorem IsPwC1ImmersionOn.symm (h : IsPwC1ImmersionOn γ a b) : IsPwC1ImmersionOn γ b a :=
  isPwC1ImmersionOn_comm.mp h

/-- Given a finite breakpoint set, every parameter `t₀ < max a b` in `[[a, b]]` has a
breakpoint-free closed piece `[t₀, d]` to its right inside `[[a, b]]`. -/
private theorem exists_Icc_right_avoiding {p : Finset ℝ} {t₀ : ℝ}
    (hp : ↑p ⊆ Ioo (min a b) (max a b)) (ht₀ : t₀ ∈ Ico (min a b) (max a b)) :
    ∃ d : ℝ, t₀ < d ∧ Icc t₀ d ⊆ uIcc a b ∧ Disjoint (↑p : Set ℝ) (Ioo t₀ d) := by
  classical
  set q : Finset ℝ := insert (max a b) (p.filter (t₀ < ·)) with hq_def
  have hq_ne : q.Nonempty := ⟨max a b, Finset.mem_insert_self _ _⟩
  refine ⟨q.min' hq_ne, ?_, ?_, ?_⟩
  · rcases Finset.mem_insert.mp (q.min'_mem hq_ne) with hm | hm
    · exact hm ▸ ht₀.2
    · exact (Finset.mem_filter.mp hm).2
  · refine (Icc_subset_Icc ht₀.1 ?_).trans Icc_min_max.subset
    rcases Finset.mem_insert.mp (q.min'_mem hq_ne) with hm | hm
    · exact hm.le
    · exact (hp (Finset.mem_filter.mp hm).1).2.le
  · rw [Set.disjoint_left]
    intro x hxp hx
    exact absurd (q.min'_le x (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hxp, hx.1⟩))) (not_le.mpr hx.2)

/-- Given a finite breakpoint set, every parameter `min a b < t₀` in `[[a, b]]` has a
breakpoint-free closed piece `[c, t₀]` to its left inside `[[a, b]]`. -/
private theorem exists_Icc_left_avoiding {p : Finset ℝ} {t₀ : ℝ}
    (hp : ↑p ⊆ Ioo (min a b) (max a b)) (ht₀ : t₀ ∈ Ioc (min a b) (max a b)) :
    ∃ c : ℝ, c < t₀ ∧ Icc c t₀ ⊆ uIcc a b ∧ Disjoint (↑p : Set ℝ) (Ioo c t₀) := by
  classical
  set q : Finset ℝ := insert (min a b) (p.filter (· < t₀)) with hq_def
  have hq_ne : q.Nonempty := ⟨min a b, Finset.mem_insert_self _ _⟩
  refine ⟨q.max' hq_ne, ?_, ?_, ?_⟩
  · rcases Finset.mem_insert.mp (q.max'_mem hq_ne) with hm | hm
    · exact hm ▸ ht₀.1
    · exact (Finset.mem_filter.mp hm).2
  · refine (Icc_subset_Icc ?_ ht₀.2).trans Icc_min_max.subset
    rcases Finset.mem_insert.mp (q.max'_mem hq_ne) with hm | hm
    · exact hm.ge
    · exact (hp (Finset.mem_filter.mp hm).1).1.le
  · rw [Set.disjoint_left]
    intro x hxp hx
    exact absurd (q.le_max' x (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hxp, hx.2⟩))) (not_le.mpr hx.1)

/-- **The piece to the right of a parameter**: every `t₀ ∈ [min, max)` begins a breakpoint-free
closed piece `[t₀, d] ⊆ [[a, b]]` on which the immersion is `C¹` with non-vanishing within-piece
derivative. -/
theorem IsPwC1ImmersionOn.exists_Icc_piece_right (h : IsPwC1ImmersionOn γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ico (min a b) (max a b)) :
    ∃ d : ℝ, t₀ < d ∧ Icc t₀ d ⊆ uIcc a b ∧ ContDiffOn ℝ 1 γ (Icc t₀ d) ∧
      ∀ t ∈ Icc t₀ d, derivWithin γ (Icc t₀ d) t ≠ 0 := by
  obtain ⟨p, hp, hpieces⟩ := h.exists_breakpoints
  obtain ⟨d, hlt, hsub, hdisj⟩ := exists_Icc_right_avoiding hp ht₀
  exact ⟨d, hlt, hsub, hpieces t₀ d hlt hsub hdisj⟩

/-- **The piece to the left of a parameter**: every `t₀ ∈ (min, max]` ends a breakpoint-free
closed piece `[c, t₀] ⊆ [[a, b]]` on which the immersion is `C¹` with non-vanishing within-piece
derivative. -/
theorem IsPwC1ImmersionOn.exists_Icc_piece_left (h : IsPwC1ImmersionOn γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioc (min a b) (max a b)) :
    ∃ c : ℝ, c < t₀ ∧ Icc c t₀ ⊆ uIcc a b ∧ ContDiffOn ℝ 1 γ (Icc c t₀) ∧
      ∀ t ∈ Icc c t₀, derivWithin γ (Icc c t₀) t ≠ 0 := by
  obtain ⟨p, hp, hpieces⟩ := h.exists_breakpoints
  obtain ⟨c, hlt, hsub, hdisj⟩ := exists_Icc_left_avoiding hp ht₀
  exact ⟨c, hlt, hsub, hpieces c t₀ hlt hsub hdisj⟩

/-- **Non-zero one-sided tangent of an immersion, from the right.** At every parameter
`t₀ ∈ [min, max)` a piecewise-`C¹` immersion has a non-zero limit of `deriv γ` from the right —
the within-piece derivative there — and the chord slope `(γ t - γ t₀) / (t - t₀)` converges from
the right to the **same** value.

Both limits are stated together, and about one `L`, because they are the same tangent: the
derivative form is what the flatness conditions are stated against, while the chord form is what
the direction of `γ t - z₀` at a crossing is computed from. Splitting them into two existentials
would lose the fact that they agree. -/
theorem IsPwC1ImmersionOn.exists_deriv_slope_right_limit (h : IsPwC1ImmersionOn γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ico (min a b) (max a b)) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L) ∧
      Tendsto (slope γ t₀) (𝓝[>] t₀) (𝓝 L) := by
  obtain ⟨d, hlt, hsub, hC1, hne⟩ := h.exists_Icc_piece_right ht₀
  refine ⟨derivWithin γ (Icc t₀ d) t₀, hne t₀ (left_mem_Icc.mpr hlt.le), ?_, ?_⟩
  · have h1 : Tendsto (derivWithin γ (Icc t₀ d)) (𝓝[Ioo t₀ d] t₀)
        (𝓝 (derivWithin γ (Icc t₀ d) t₀)) :=
      (((hC1.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl) t₀
        (left_mem_Icc.mpr hlt.le)).tendsto).mono_left (nhdsWithin_mono t₀ Ioo_subset_Icc_self)
    rw [← nhdsWithin_Ioo_eq_nhdsGT hlt]
    exact h1.congr' <| eventually_mem_nhdsWithin.mono fun t ht =>
      derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  · have hd : HasDerivWithinAt γ (derivWithin γ (Icc t₀ d) t₀) (Icc t₀ d) t₀ :=
      ((hC1.differentiableOn one_ne_zero) t₀ (left_mem_Icc.mpr hlt.le)).hasDerivWithinAt
    rw [← nhdsWithin_Ioo_eq_nhdsGT hlt]
    exact (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1 (hd.mono Ioo_subset_Icc_self)

/-- The tangent-limit half of `IsPwC1ImmersionOn.exists_deriv_slope_right_limit`. -/
theorem IsPwC1ImmersionOn.exists_deriv_right_limit (h : IsPwC1ImmersionOn γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ico (min a b) (max a b)) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L) :=
  let ⟨L, hL, hd, _⟩ := h.exists_deriv_slope_right_limit ht₀
  ⟨L, hL, hd⟩

/-- **Non-zero one-sided tangent of an immersion, from the left.** The left-hand companion of
`IsPwC1ImmersionOn.exists_deriv_slope_right_limit`: at every parameter `t₀ ∈ (min, max]` both
`deriv γ` and the chord slope converge from the left to the same non-zero within-piece
derivative. -/
theorem IsPwC1ImmersionOn.exists_deriv_slope_left_limit (h : IsPwC1ImmersionOn γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioc (min a b) (max a b)) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L) ∧
      Tendsto (slope γ t₀) (𝓝[<] t₀) (𝓝 L) := by
  obtain ⟨c, hlt, hsub, hC1, hne⟩ := h.exists_Icc_piece_left ht₀
  refine ⟨derivWithin γ (Icc c t₀) t₀, hne t₀ (right_mem_Icc.mpr hlt.le), ?_, ?_⟩
  · have h1 : Tendsto (derivWithin γ (Icc c t₀)) (𝓝[Ioo c t₀] t₀)
        (𝓝 (derivWithin γ (Icc c t₀) t₀)) :=
      (((hC1.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl) t₀
        (right_mem_Icc.mpr hlt.le)).tendsto).mono_left (nhdsWithin_mono t₀ Ioo_subset_Icc_self)
    rw [← nhdsWithin_Ioo_eq_nhdsLT hlt]
    exact h1.congr' <| eventually_mem_nhdsWithin.mono fun t ht =>
      derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  · have hd : HasDerivWithinAt γ (derivWithin γ (Icc c t₀) t₀) (Icc c t₀) t₀ :=
      ((hC1.differentiableOn one_ne_zero) t₀ (right_mem_Icc.mpr hlt.le)).hasDerivWithinAt
    rw [← nhdsWithin_Ioo_eq_nhdsLT hlt]
    exact (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1 (hd.mono Ioo_subset_Icc_self)

/-- The tangent-limit half of `IsPwC1ImmersionOn.exists_deriv_slope_left_limit`. -/
theorem IsPwC1ImmersionOn.exists_deriv_left_limit (h : IsPwC1ImmersionOn γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioc (min a b) (max a b)) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L) :=
  let ⟨L, hL, hd, _⟩ := h.exists_deriv_slope_left_limit ht₀
  ⟨L, hL, hd⟩

end TauCeti.Contour

end
