/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.GradientFlow
public import TauCeti.Dynamics.Flow.OfLipschitz

/-!
# Existence of the negative gradient flow

The dynamical description of Morse theory reads its trajectory spaces off a *flow*: stable and
unstable sets, and the Lyapunov theory of a decreasing function along trajectories, are statements
about a `Flow.IsNegativeGradient` flow. This file produces such a flow for every function whose
gradient is globally Lipschitz, by feeding `-∇ f` to `Flow.ofLipschitz`.

Global Lipschitz continuity of `∇ f` is a sufficient hypothesis for the trajectories to exist for
all time; it holds for instance whenever `f` is `C²` with a bounded second derivative, and in
particular for the split quadratic model.

## Main declarations

* `TauCeti.negativeGradientFlow`: the negative gradient flow of a function with globally Lipschitz
  gradient.
* `TauCeti.isNegativeGradient_negativeGradientFlow`: it is a negative gradient flow of `f`.
* `TauCeti.eq_negativeGradientFlow`: every global negative gradient trajectory is one of its
  orbits.
* `TauCeti.negativeGradientFlow_congr`: it does not depend on the chosen Lipschitz bound.
* `TauCeti.forall_negativeGradientFlow_eq_self_iff`: its rest points are the critical points
  of `f`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
-/

public section

open InnerProductSpace
open scoped Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {K : ℝ≥0}

/-- **The negative gradient flow** of a function whose gradient is globally Lipschitz. -/
noncomputable def negativeGradientFlow (f : E → ℝ) {K : ℝ≥0} (hf : LipschitzWith K (∇ f)) :
    _root_.Flow ℝ E :=
  _root_.Flow.ofLipschitz (fun x ↦ -∇ f x) hf.neg

/-- **The negative gradient flow is a negative gradient flow**: each of its orbits solves
`γ' = -∇f(γ)`. -/
theorem isNegativeGradient_negativeGradientFlow (f : E → ℝ) (hf : LipschitzWith K (∇ f)) :
    Flow.IsNegativeGradient (negativeGradientFlow f hf) f :=
  Flow.isNegativeGradient_iff.2 fun x ↦ _root_.Flow.isIntegralCurve_ofLipschitz hf.neg x

/-- **Every global negative gradient trajectory is an orbit** of the negative gradient flow. -/
theorem eq_negativeGradientFlow (f : E → ℝ) (hf : LipschitzWith K (∇ f)) {γ : ℝ → E}
    (hγ : IsIntegralCurve γ fun _ y ↦ -∇ f y) (t : ℝ) :
    γ t = negativeGradientFlow f hf t (γ 0) :=
  _root_.Flow.eq_ofLipschitz hf.neg hγ t

/-- **Independence of the Lipschitz bound.** Two Lipschitz witnesses for `∇ f`, with possibly
different constants, produce the same negative gradient flow. -/
theorem negativeGradientFlow_congr (f : E → ℝ) {K' : ℝ≥0} (hf : LipschitzWith K (∇ f))
    (hf' : LipschitzWith K' (∇ f)) : negativeGradientFlow f hf = negativeGradientFlow f hf' :=
  _root_.Flow.ofLipschitz_congr hf.neg hf'.neg

/-- **The rest points of the negative gradient flow are the critical points of `f`.** -/
theorem forall_negativeGradientFlow_eq_self_iff (f : E → ℝ) (hf : LipschitzWith K (∇ f)) (x : E) :
    (∀ t, negativeGradientFlow f hf t x = x) ↔ ∇ f x = 0 := by
  rw [negativeGradientFlow, _root_.Flow.forall_ofLipschitz_eq_self_iff, neg_eq_zero]

end TauCeti
