/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Winding
import TauCeti.Analysis.Contour.Winding.Proximity

/-!
# Curves in a star-shaped set are null-homologous there

A closed piecewise-`C¹` curve drawn inside a set `Ω` that is star-shaped about `x` has winding
number `0` about every point outside `Ω`. The proof is the straight-line contraction of the curve
to the constant curve at the centre: for each parameter `t` the segment from `γ t` to `x` lies in
`Ω` by star-convexity, hence misses every `w ∉ Ω`, so
`TauCeti.Contour.IsPiecewiseC1On.windingNumber_eq_of_notMem_segment` equates `n_w(γ)` with the
winding number of a constant curve, which is `0`.

This discharges the `TauCeti.Contour.IsNullHomologous` hypothesis carried by the Layer 3 homology
Cauchy theorem and by everything above it, on the domains that ordinary applications supply — a
disc, a half-plane, a strip, a rectangle, the slit plane. Star-shapedness is a condition on the
*domain* alone: nothing is asked of the curve beyond the piecewise-`C¹` regularity that the
statements already carry. The homotopy route,
`TauCeti.Contour.isNullHomologous_of_pathHomotopy_refl`, covers strictly more domains, but asks the
caller to exhibit a contracting homotopy; a star-shaped domain supplies one for free.

## Main results

* `TauCeti.Contour.windingNumber_eq_zero_of_starConvex` — a closed piecewise-`C¹` curve in a
  star-shaped set has winding number `0` about every point outside that set.
* `TauCeti.Contour.isNullHomologous_of_starConvex` — such a curve is null-homologous there, and
  `TauCeti.Contour.Cycle.isNullHomologous_of_starConvex` for a contour cycle.

A convex `Ω` is star-shaped about any of its points, so a caller holding `hconv : Convex ℝ Ω` and a
curve in `Ω` supplies `hconv.starConvex (hγΩ a left_mem_uIcc)`.

## Provenance

No formalization is vendored. That a cycle in a star-shaped (indeed, in a simply connected) domain
is null-homologous is standard complex analysis; see the references of the contour integration
roadmap, e.g. Lang, *Complex Analysis*, Ch. IV.
-/

public section

open Set

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}

/-- **The winding number vanishes at every point outside a star-shaped set containing the curve.**
If the closed piecewise-`C¹` curve `γ` stays in a set `Ω` star-shaped about `x` and `w ∉ Ω`, then
`n_w(γ) = 0`. Indeed, the straight-line contraction of `γ` to the centre `x` stays in `Ω`, so it
avoids `w`. -/
theorem windingNumber_eq_zero_of_starConvex {Ω : Set ℂ} {x : ℂ} (hstar : StarConvex ℝ x Ω)
    (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) (hw : w ∉ Ω) :
    windingNumber γ a b w = 0 := by
  let γ₀ : ℝ → ℂ := Function.const ℝ x
  have hγ₀ : IsPiecewiseC1On γ₀ a b :=
    IsPiecewiseC1On.of_contDiffOn contDiff_const.contDiffOn
  have hseg : ∀ t ∈ uIcc a b, w ∉ segment ℝ (γ t) (γ₀ t) := by
    intro t ht hwt
    have hwt' : w ∈ segment ℝ x (γ t) := by
      rw [segment_symm]
      exact hwt
    exact hw (hstar.segment_subset (hγΩ t ht) hwt')
  rw [← hγ.windingNumber_eq_of_notMem_segment hγ₀ hclosed rfl hseg]
  exact windingNumber_const x a b w

/-- **A closed piecewise-`C¹` curve in a star-shaped set is null-homologous there.** -/
theorem isNullHomologous_of_starConvex {Ω : Set ℂ} {x : ℂ} (hstar : StarConvex ℝ x Ω)
    (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b) (hγΩ : ∀ t ∈ uIcc a b, γ t ∈ Ω) :
    IsNullHomologous γ a b Ω :=
  isNullHomologous_iff.mpr fun _ hw ↦
    windingNumber_eq_zero_of_starConvex hstar hγ hclosed hγΩ hw

namespace Cycle

/-- **A cycle in a star-shaped set is null-homologous there.** Every generator of the cycle is a
closed piecewise-`C¹` curve confined to `Ω`, so each has vanishing winding number outside `Ω` by
`TauCeti.Contour.isNullHomologous_of_starConvex`, and the cycle winding number is their
`ℤ`-combination. -/
theorem isNullHomologous_of_starConvex {C : Cycle} {Ω : Set ℂ} {x : ℂ}
    (hstar : StarConvex ℝ x Ω) (hC : IsIn C Ω) : IsNullHomologous C Ω := by
  refine isNullHomologous_iff.mpr fun w hw ↦ ?_
  rw [windingNumber_eq_sum_support]
  refine Finset.sum_eq_zero fun δ hδ ↦ ?_
  have hδΩ : ∀ t ∈ uIcc δ.a δ.b, δ t ∈ Ω := fun t ht ↦
    isIn_iff.mp hC (mem_trace_iff.mpr ⟨δ, hδ, t, ht, rfl⟩)
  rw [TauCeti.Contour.isNullHomologous_iff.mp
    (TauCeti.Contour.isNullHomologous_of_starConvex hstar δ.isPiecewiseC1On
      δ.source_eq_target hδΩ) w hw, mul_zero]

end Cycle

end TauCeti.Contour

end
