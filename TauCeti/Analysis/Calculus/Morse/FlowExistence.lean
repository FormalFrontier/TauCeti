/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.SplitModel
public import TauCeti.Dynamics.Flow.OfLipschitz

/-!
# Existence of the negative gradient flow

The dynamical route to Morse homology reads its trajectory spaces off a *flow*: the stable and
unstable sets of `TauCeti/Dynamics/Flow/Stable.lean`, and the Lyapunov theory of
`TauCeti/Analysis/Calculus/Morse/GradientFlow.lean`, are all statements about a
`Flow.IsNegativeGradient` flow. Until now the only such flow available was the explicit
hyperbolic one of the split quadratic model. This file produces one for every function whose
gradient is globally Lipschitz, by feeding `-∇ f` to `Flow.ofLipschitz`.

Global Lipschitz continuity of `∇ f` is exactly what rules out escape to infinity in finite time;
it holds for instance whenever `f` is `C²` with a bounded second derivative, and in particular for
the split quadratic model, whose explicit flow is recovered here as a special case.

## Main declarations

* `TauCeti.negativeGradientFlow`: the negative gradient flow of a function with globally Lipschitz
  gradient.
* `TauCeti.isNegativeGradient_negativeGradientFlow`: it is a negative gradient flow of `f`.
* `TauCeti.forall_negativeGradientFlow_eq_self_iff`: its rest points are the critical points
  of `f`.
* `TauCeti.negativeGradientFlow_splitQuadratic`: for the split quadratic model it is the explicit
  hyperbolic flow.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HeegaardFloer/README.md),
  Lane M, "Morse homology".
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

/-- **The rest points of the negative gradient flow are the critical points of `f`.** -/
theorem forall_negativeGradientFlow_eq_self_iff (f : E → ℝ) (hf : LipschitzWith K (∇ f)) (x : E) :
    (∀ t, negativeGradientFlow f hf t x = x) ↔ ∇ f x = 0 := by
  rw [negativeGradientFlow, _root_.Flow.forall_ofLipschitz_eq_self_iff, neg_eq_zero]

section SplitModel

variable {Eₛ Eᵤ : Type*} [NormedAddCommGroup Eₛ] [NormedAddCommGroup Eᵤ]
  [InnerProductSpace ℝ Eₛ] [InnerProductSpace ℝ Eᵤ] [CompleteSpace Eₛ] [CompleteSpace Eᵤ]

/-- On the split quadratic model the abstract construction returns the explicit hyperbolic flow,
which is the acceptance check that `TauCeti.negativeGradientFlow` is the intended object. -/
theorem negativeGradientFlow_splitQuadratic :
    negativeGradientFlow (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ))
        lipschitzWith_gradient_splitQuadratic = splitQuadraticFlow := by
  refine _root_.Flow.ext fun t z ↦ ?_
  have hγ := (Flow.isNegativeGradient_splitQuadraticFlow (Eₛ := Eₛ) (Eᵤ := Eᵤ)).isIntegralCurve z
  have h := eq_negativeGradientFlow (splitQuadratic (Eₛ := Eₛ) (Eᵤ := Eᵤ))
    lipschitzWith_gradient_splitQuadratic hγ t
  have h0 : splitQuadraticFlow (Eₛ := Eₛ) (Eᵤ := Eᵤ) 0 z = z := _root_.Flow.map_zero_apply _ z
  rw [h0] at h
  exact h.symm

end SplitModel

end TauCeti
