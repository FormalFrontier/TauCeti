/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.NumberTheory.ModularForms.LevelOne.FundamentalDomainBoundary.Basic
public import TauCeti.NumberTheory.ModularForms.Order.AtCusp

import TauCeti.Analysis.Complex.IsolatedZero
import TauCeti.Analysis.Contour.Argument.Principle

/-!
# The ceiling of the boundary contour maps to a `q`-circle

Under the level-one `q`-parameter `𝕢 1 z = exp (2πiz)`, the truncation ceiling of the
fundamental-domain boundary — the horizontal from `-1/2 + H·i` to `1/2 + H·i` — traces
the circle of radius `e^{-2πH}` about the origin, traversed once counterclockwise. This
is the change of variables that turns the ceiling contour integral of the logarithmic
derivative of a level-one form into a `q`-circle integral of its cusp function, whose
value is `2πi` times the order at the cusp.

## Main declarations

* `TauCeti.ModularForm.fdBoundaryQRadius`: the radius `e^{-2πH}` of the ceiling's
  `q`-circle, with `fdBoundaryQRadius_def`, `_pos`, and `_lt_one`.
* `TauCeti.ModularForm.qParam_fdBoundarySegment5`: the ceiling parametrizes the
  `q`-circle.
* `TauCeti.ModularForm.circleIntegral_logDeriv_cuspFunction`: the `q`-circle integral of
  the cusp function's logarithmic derivative is `2πi` times the cusp order.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/PVChain/Seg5CuspIntegral.lean`) this file ports
  onto the current Mathlib pin.
-/

public section

open Complex Function

open scoped Real

namespace TauCeti

namespace ModularForm

/-- The radius of the `q`-image of the truncation ceiling of the boundary contour at
height `H`. Sealed as a definition so the ceiling bridge, the cusp-function circle
integral, and the radius bounds all speak about one constant. -/
noncomputable def fdBoundaryQRadius (H : ℝ) : ℝ := Real.exp (-2 * Real.pi * H)

/-- The defining equation of the `q`-circle radius, in the normal form of
`Function.Periodic.norm_qParam`. -/
lemma fdBoundaryQRadius_def (H : ℝ) :
    fdBoundaryQRadius H = Real.exp (-2 * Real.pi * H) := by
  unfold fdBoundaryQRadius
  rfl

/-- The `q`-circle radius is positive. -/
lemma fdBoundaryQRadius_pos (H : ℝ) : 0 < fdBoundaryQRadius H := by
  simpa only [fdBoundaryQRadius_def] using Real.exp_pos (-2 * Real.pi * H)

/-- The `q`-circle radius is less than one for a positive truncation height. -/
lemma fdBoundaryQRadius_lt_one {H : ℝ} (hH : 0 < H) : fdBoundaryQRadius H < 1 := by
  rw [fdBoundaryQRadius_def, Real.exp_lt_one_iff]
  have := Real.pi_pos
  nlinarith

/-- Under the level-one `q`-parameter, the ceiling of the boundary contour traces the
`q`-circle of radius `e^{-2πH}`: the segment parameter `t ∈ [4, 5]` becomes the angle
`2π(t - 9/2)`, sweeping `[-π, π]` once counterclockwise. -/
theorem qParam_fdBoundarySegment5 (H t : ℝ) :
    Periodic.qParam (1 : ℝ) (fdBoundarySegment5 H t) =
      circleMap 0 (fdBoundaryQRadius H) (2 * Real.pi * (t - 9 / 2)) := by
  have hz : fdBoundarySegment5 H t = ((t - 9 / 2 : ℝ) : ℂ) + H * Complex.I := by
    rw [fdBoundarySegment5_apply, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      Complex.real_smul]
    push_cast
    ring
  have hexp : 2 * ↑Real.pi * Complex.I * (((t - 9 / 2 : ℝ) : ℂ) + ↑H * Complex.I) /
      ((1 : ℝ) : ℂ) = ↑(-2 * Real.pi * H) + ↑(2 * Real.pi * (t - 9 / 2)) * Complex.I := by
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * H) * Complex.I_sq
  rw [hz, Periodic.qParam, fdBoundaryQRadius_def, circleMap_zero, hexp, Complex.exp_add,
    Complex.ofReal_exp]


/-- The `q`-circle integral of the logarithmic derivative of the cusp function is `2πi`
times the `q`-expansion order at the cusp: the cusp function is analytic on the closed
`q`-disc and vanishes there at most at the origin, so the argument principle localizes
the order contribution to the origin — the cusp order, which is `0` when the cusp
function does not vanish there. The order is finite because a cusp function vanishing
identically near `0` would also vanish somewhere on the punctured disc. -/
theorem circleIntegral_logDeriv_cuspFunction {g : UpperHalfPlane → ℂ} {H : ℝ}
    (hga : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 g) q)
    (hgz : ∀ q ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H), q ≠ 0 →
      UpperHalfPlane.cuspFunction 1 g q ≠ 0) :
    circleIntegral (logDeriv (UpperHalfPlane.cuspFunction 1 g)) 0 (fdBoundaryQRadius H) =
      2 * Real.pi * Complex.I * qExpansionOrderAtCusp 1 g := by
  have hR := fdBoundaryQRadius_pos H
  have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H) :=
    Metric.mem_closedBall_self hR.le
  have hfin : analyticOrderAt (UpperHalfPlane.cuspFunction 1 g) 0 ≠ ⊤ :=
    TauCeti.analyticOrderAt_ne_top_of_forall_ne_zero hR
      (fun z hz hz0 => hgz z (Metric.ball_subset_closedBall hz) hz0)
  have hmer : MeromorphicOn (UpperHalfPlane.cuspFunction 1 g)
      (Metric.closedBall 0 (fdBoundaryQRadius H)) := fun q hq => (hga q hq).meromorphicAt
  have honly : ∀ z ∈ Metric.closedBall (0 : ℂ) (fdBoundaryQRadius H),
      meromorphicOrderAt (UpperHalfPlane.cuspFunction 1 g) z ≠ 0 → z = 0 := by
    intro z hz hord
    by_contra hz0
    refine hord ?_
    rw [(hga z hz).meromorphicOrderAt_eq,
      (hga z hz).analyticOrderAt_eq_zero.mpr (hgz z hz hz0)]
    rfl
  have hn : meromorphicOrderAt (UpperHalfPlane.cuspFunction 1 g) 0 =
      ((qExpansionOrderAtCusp 1 g : ℤ) : WithTop ℤ) := by
    rw [(hga 0 h0).meromorphicOrderAt_eq,
      qExpansionOrderAtCusp_eq_analyticOrderAt (hga 0 h0)]
    lift analyticOrderAt (UpperHalfPlane.cuspFunction 1 g) 0 to ℕ using hfin with n hnn
    simp
  have key := Contour.argumentPrinciple_local hR hmer honly hn
  rw [key]

end ModularForm

end TauCeti

end
