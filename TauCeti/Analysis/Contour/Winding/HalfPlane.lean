/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Winding
public import TauCeti.Analysis.Contour.NullHomologous
public import TauCeti.Analysis.Contour.Winding.UnboundedComponent
import TauCeti.Analysis.Contour.Winding.Proximity

/-!
# Curves confined to a half-plane, and cycles in a convex domain

A point `w` sees winding number `0` from any closed curve that stays strictly on one side of a
line through `w`: the closed half-plane on `w`'s side of that line is convex, hence connected,
misses the curve, and is unbounded, so `w` lies in an unbounded component of the curve complement
and `TauCeti.Contour.windingNumber_eq_zero_of_unbounded_component` applies.

Consequently **every closed curve in a convex set `Ω` is null-homologous in `Ω`**: the
straight-line contraction to any point of the curve stays in `Ω`, and hence avoids every point
outside `Ω`.

This discharges the `TauCeti.Contour.IsNullHomologous` hypothesis carried by the Layer 3 homology
Cauchy theorem and by everything above it, on the domains that ordinary applications supply — a
disc, a half-plane, a strip, a rectangle. Before this file the only route to that hypothesis was a
null-homotopy (`TauCeti.Contour.isNullHomologous_of_pathHomotopy_refl`), which asks the user to
produce a contracting homotopy; convexity of the ambient domain asks for nothing about the curve.

## Main results

* `TauCeti.Contour.windingNumber_eq_zero_of_re_mul_lt` — a closed curve strictly on one side
  of a line through `w` has winding number `0` about `w`.
* `TauCeti.Contour.windingNumber_eq_zero_of_convex` — a closed curve in a convex set has
  winding number `0` about every point outside that set.
* `TauCeti.Contour.isNullHomologous_of_convex` — a closed piecewise-`C¹` curve in a convex
  set is null-homologous there, and `TauCeti.Contour.Cycle.isNullHomologous_of_convex` for a
  cycle.

## Provenance

No formalization is vendored. That a cycle in a convex (indeed, in a simply connected) domain is
null-homologous is standard complex analysis; see the references of the contour integration
roadmap, e.g. Lang, *Complex Analysis*, Ch. IV.
-/

public section

open Bornology Complex Set

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}

/-- The `ℝ`-linear form `z ↦ (c * z).re` on `ℂ`, whose level sets are the lines perpendicular to
the conjugate of `c`. -/
private theorem isLinearMap_re_mul (c : ℂ) : IsLinearMap ℝ fun z : ℂ ↦ (c * z).re where
  map_add z z' := by simp [mul_add]
  map_smul p z := by
    rw [Complex.real_smul, ← mul_assoc, mul_comm c, mul_assoc]
    simp [Complex.mul_re]

/-- The closed half-plane `{z | (c * w).re ≤ (c * z).re}` bounded by the line through `w`
perpendicular to the conjugate of `c`. It is the region avoided by a curve satisfying the
hypothesis of `TauCeti.Contour.windingNumber_eq_zero_of_re_mul_lt`. -/
private def farHalfPlane (c w : ℂ) : Set ℂ := {z : ℂ | (c * w).re ≤ (c * z).re}

/-- Membership in the far half-plane, unfolded. -/
private theorem mem_farHalfPlane {c w z : ℂ} :
    z ∈ farHalfPlane c w ↔ (c * w).re ≤ (c * z).re := Iff.rfl

private theorem convex_farHalfPlane (c w : ℂ) : Convex ℝ (farHalfPlane c w) :=
  convex_halfSpace_ge (isLinearMap_re_mul c) _

/-- A closed half-plane in `ℂ` is unbounded: it contains the ray leaving `w` in the direction of
the conjugate of `c`, along which the norm grows without bound. -/
private theorem not_isBounded_farHalfPlane {c : ℂ} (hc : c ≠ 0) (w : ℂ) :
    ¬IsBounded (farHalfPlane c w) := by
  intro hbdd
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbdd
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  set t : ℝ := (|C| + ‖w‖ + 1) / ‖c‖ with ht
  have ht0 : 0 ≤ t := by
    rw [ht]
    positivity
  have hscale : t * ‖c‖ = |C| + ‖w‖ + 1 := by
    rw [ht, div_mul_cancel₀ _ hcpos.ne']
  have hzmem : w + (t : ℂ) * (starRingEnd ℂ) c ∈ farHalfPlane c w := by
    have hexp : c * (w + (t : ℂ) * (starRingEnd ℂ) c)
        = c * w + (t : ℂ) * (c * (starRingEnd ℂ) c) := by ring
    rw [mem_farHalfPlane, hexp, Complex.add_re, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_re, le_add_iff_nonneg_right]
    exact mul_nonneg ht0 (Complex.normSq_nonneg c)
  have hnorm : ‖w + (t : ℂ) * (starRingEnd ℂ) c‖ ≤ C := hC _ hzmem
  have hlow : ‖(t : ℂ) * (starRingEnd ℂ) c‖ = |C| + ‖w‖ + 1 := by
    rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht0, hscale]
  have hrev : ‖(t : ℂ) * (starRingEnd ℂ) c‖ - ‖w‖ ≤ ‖w + (t : ℂ) * (starRingEnd ℂ) c‖ := by
    simpa [sub_neg_eq_add, add_comm] using
      norm_sub_norm_le ((t : ℂ) * (starRingEnd ℂ) c) (-w)
  have := le_abs_self C
  linarith

/-- **The winding number vanishes for a curve confined to one side of a line through the point.**
Let `c ≠ 0` and let the closed curve `γ` satisfy `(c * γ t).re < (c * w).re` throughout: `γ` runs
strictly inside the open half-plane bounded by the line through `w` perpendicular to the conjugate
of `c`, on the side away from that conjugate. Then `n_w(γ) = 0`.

The complementary closed half-plane is convex, hence connected, contains `w`, misses the curve,
and is unbounded, so `w` lies in an unbounded component of the curve complement and
`TauCeti.Contour.windingNumber_eq_zero_of_unbounded_component` applies. -/
theorem windingNumber_eq_zero_of_re_mul_lt {P : Set ℝ} {c : ℂ} (hc : c ≠ 0)
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) MeasureTheory.volume a b)
    (hside : ∀ t ∈ uIcc a b, (c * γ t).re < (c * w).re) :
    windingNumber γ a b w = 0 := by
  refine windingNumber_eq_zero_of_unbounded_component hclosed hP hγ_cont hγ_diff hderiv_int ?_
  have hsub : farHalfPlane c w ⊆ (γ '' uIcc a b)ᶜ := by
    rintro z hz ⟨t, ht, rfl⟩
    exact absurd (mem_farHalfPlane.mp hz) (not_le.mpr (hside t ht))
  have hcomp : farHalfPlane c w ⊆ connectedComponentIn ((γ '' uIcc a b)ᶜ) w :=
    (convex_farHalfPlane c w).isPreconnected.subset_connectedComponentIn
      (mem_farHalfPlane.mpr le_rfl) hsub
  exact fun hbdd ↦ not_isBounded_farHalfPlane hc w (hbdd.subset hcomp)

/-- **The winding number vanishes at every point outside a convex set containing the curve.**
If the closed piecewise-`C¹` curve `γ` stays in a convex `Ω` and `w ∉ Ω`, then `n_w(γ) = 0`.
Indeed, the straight-line contraction of `γ` to its basepoint stays in `Ω`, so it avoids `w`. -/
theorem windingNumber_eq_zero_of_convex {Ω : Set ℂ} (hconv : Convex ℝ Ω)
    (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hw : w ∉ Ω) :
    windingNumber γ a b w = 0 := by
  let γ₀ : ℝ → ℂ := Function.const ℝ (γ a)
  have hγ₀ : IsPiecewiseC1On γ₀ a b :=
    IsPiecewiseC1On.of_contDiffOn contDiff_const.contDiffOn
  have hseg : ∀ t ∈ uIcc a b, w ∉ segment ℝ (γ t) (γ₀ t) := by
    intro t ht hwt
    exact hw (hconv.segment_subset (hγΩ t ht) (hγΩ a left_mem_uIcc) hwt)
  rw [← hγ.windingNumber_eq_of_notMem_segment hγ₀ hclosed rfl hseg]
  exact windingNumber_const (γ a) a b w

/-- **A closed piecewise-`C¹` curve in a convex set is null-homologous there.** -/
theorem isNullHomologous_of_convex {Ω : Set ℂ} (hconv : Convex ℝ Ω)
    (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b) (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) :
    IsNullHomologous γ a b Ω := by
  exact isNullHomologous_iff.mpr fun w hw ↦
    windingNumber_eq_zero_of_convex hconv hγ hclosed hγΩ hw

/-- **A closed piecewise-`C¹` curve in a ball is null-homologous there** — the disc case of
`TauCeti.Contour.isNullHomologous_of_convex`, and the shape in which Mathlib's disc Cauchy theory
is usually met. -/
theorem isNullHomologous_of_mapsTo_ball {c : ℂ} {r : ℝ} (hγ : IsPiecewiseC1On γ a b)
    (hclosed : γ a = γ b) (hγr : ∀ t ∈ uIcc a b, γ t ∈ Metric.ball c r) :
    IsNullHomologous γ a b (Metric.ball c r) :=
  isNullHomologous_of_convex (convex_ball c r) hγ hclosed hγr

namespace Cycle

/-- **A cycle in a convex set is null-homologous there.** Every generator of the cycle is a
closed piecewise-`C¹` curve confined to `Ω`, so each has vanishing winding number outside `Ω` by
`TauCeti.Contour.isNullHomologous_of_convex`, and the cycle winding number is their
`ℤ`-combination. -/
theorem isNullHomologous_of_convex {C : Cycle} {Ω : Set ℂ} (hconv : Convex ℝ Ω)
    (hC : IsIn C Ω) : IsNullHomologous C Ω := by
  refine isNullHomologous_iff.mpr fun w hw ↦ ?_
  rw [windingNumber_eq_sum_support]
  refine Finset.sum_eq_zero fun δ hδ ↦ ?_
  have hδΩ : ∀ t ∈ uIcc δ.a δ.b, δ t ∈ Ω := fun t ht ↦
    isIn_iff.mp hC (mem_trace_iff.mpr ⟨δ, hδ, t, ht, rfl⟩)
  rw [TauCeti.Contour.isNullHomologous_iff.mp
    (TauCeti.Contour.isNullHomologous_of_convex hconv δ.isPiecewiseC1On
      δ.source_eq_target hδΩ) w hw, mul_zero]

end Cycle

end TauCeti.Contour

end
