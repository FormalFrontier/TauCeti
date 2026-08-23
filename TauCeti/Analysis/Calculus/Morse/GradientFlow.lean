/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
-- Private: monotonicity, constant-curve recognition, and the fundamental theorem of calculus are
-- used only in proofs; no declaration below exposes their APIs.
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Transform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Negative gradient trajectories

This file develops the first dynamical facts about negative gradient trajectories in a real
Hilbert space.  A curve `γ` is read through Mathlib's existing `IsIntegralCurveOn` predicate for
the autonomous vector field `fun _ x ↦ -∇ f x`; no parallel notion of trajectory is introduced.

The basic calculation is

`d/dt f(γ(t)) = -‖∇f(γ(t))‖²`.

It makes `f` a Lyapunov function: `f ∘ γ` is antitone, and strictly antitone on any interval on
which the trajectory contains no critical point.  Integrating the calculation gives the energy
identity

`∫ t in a..b, ‖∇f(γ(t))‖² = f(γ(a)) - f(γ(b))`.

In particular a periodic negative gradient trajectory is stationary in the dynamical sense that
its gradient vanishes at every point of the curve.  These statements are the entry point to the
gradient-flow, stable/unstable-manifold, and broken-trajectory constructions in the dynamical
route to Morse homology.

## Main results

* `TauCeti.isIntegralCurve_const_neg_gradient_iff`: the constant curves are precisely the critical
  points of the vector field.
* `TauCeti.IsIntegralCurveOn.hasDerivWithinAt_comp_neg_gradient`: derivative of `f` along a
  negative gradient trajectory.
* `TauCeti.IsIntegralCurveOn.antitoneOn_comp_neg_gradient` and
  `TauCeti.IsIntegralCurveOn.strictAntiOn_comp_neg_gradient`: Lyapunov monotonicity and strict
  descent away from critical points.
* `TauCeti.IsIntegralCurve.integral_norm_gradient_sq_eq_sub`: the energy identity.
* `TauCeti.IsIntegralCurve.gradient_eq_zero_of_periodic` and
  `TauCeti.IsIntegralCurve.eq_of_periodic_neg_gradient`: a periodic negative gradient trajectory
  consists entirely of critical points and is constant.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HeegaardFloer/README.md),
  Lane M, "Morse homology".
-/

public section

open Filter Function InnerProductSpace Set
open scoped Gradient Interval Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {γ : ℝ → E} {s : Set ℝ} {t a b : ℝ}

/-- A constant curve is an integral curve of the negative gradient field exactly when its value
is a critical point of that field. -/
theorem isIntegralCurve_const_neg_gradient_iff {x : E} :
    IsIntegralCurve (fun _ : ℝ ↦ x) (fun _ y ↦ -∇ f y) ↔ ∇ f x = 0 := by
  constructor
  · intro h
    have hderiv := (h 0).deriv
    simpa only [deriv_const, neg_eq_zero] using hderiv.symm
  · intro hx
    exact isIntegralCurve_const fun _ ↦ by simp [hx]

namespace IsIntegralCurveOn

/-- Along a negative gradient trajectory, the derivative of `f` is the negative squared norm of
its gradient.  This within-set form is the one used for trajectories on their maximal interval of
definition. -/
theorem hasDerivWithinAt_comp_neg_gradient
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) s) (ht : t ∈ s)
    (hf : DifferentiableAt ℝ f (γ t)) :
    HasDerivWithinAt (f ∘ γ) (-‖∇ f (γ t)‖ ^ 2) s t := by
  have hcomp := hf.hasFDerivAt.comp_hasDerivWithinAt t (hγ t ht)
  apply hcomp.congr_deriv
  rw [map_neg, ← inner_gradient_left, real_inner_self_eq_norm_sq]

/-- The value of `f` is antitone along a negative gradient trajectory on a convex time domain. -/
theorem antitoneOn_comp_neg_gradient
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) s) (hs : Convex ℝ s)
    (hf : ∀ t ∈ s, DifferentiableAt ℝ f (γ t)) :
    AntitoneOn (f ∘ γ) s := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos hs
  · exact fun t ht ↦ (hf t ht).continuousAt.comp_continuousWithinAt
      (hγ.continuousWithinAt ht)
  · intro t ht
    exact (hasDerivWithinAt_comp_neg_gradient hγ (interior_subset ht)
      (hf t (interior_subset ht))).mono interior_subset
  · intro t _
    exact neg_nonpos.mpr (sq_nonneg _)

/-- Away from critical points, the value of `f` is strictly decreasing along a negative gradient
trajectory on a convex time domain. -/
theorem strictAntiOn_comp_neg_gradient
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) s) (hs : Convex ℝ s)
    (hf : ∀ t ∈ s, DifferentiableAt ℝ f (γ t))
    (hcrit : ∀ t ∈ interior s, ∇ f (γ t) ≠ 0) :
    StrictAntiOn (f ∘ γ) s := by
  apply strictAntiOn_of_hasDerivWithinAt_neg hs
  · exact fun t ht ↦ (hf t ht).continuousAt.comp_continuousWithinAt
      (hγ.continuousWithinAt ht)
  · intro t ht
    exact (hasDerivWithinAt_comp_neg_gradient hγ (interior_subset ht)
      (hf t (interior_subset ht))).mono interior_subset
  · intro t ht
    exact neg_lt_zero.mpr (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (hcrit t ht)))

end IsIntegralCurveOn

namespace IsIntegralCurve

/-- Along a global negative gradient trajectory, the derivative of `f` is the negative squared
norm of its gradient. -/
theorem hasDerivAt_comp_neg_gradient
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : DifferentiableAt ℝ f (γ t)) :
    HasDerivAt (f ∘ γ) (-‖∇ f (γ t)‖ ^ 2) t :=
  (IsIntegralCurveOn.hasDerivWithinAt_comp_neg_gradient (hγ.isIntegralCurveOn univ)
    (mem_univ t) hf).hasDerivAt univ_mem

/-- The value of `f` is antitone along a global negative gradient trajectory. -/
theorem antitone_comp_neg_gradient
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : Differentiable ℝ f) :
    Antitone (f ∘ γ) :=
  antitone_of_hasDerivAt_nonpos
    (fun t ↦ hasDerivAt_comp_neg_gradient hγ (hf (γ t))) fun _ ↦ neg_nonpos.mpr (sq_nonneg _)

/-- If a global negative gradient trajectory contains no critical point, then the value of `f` is
strictly decreasing along it. -/
theorem strictAnti_comp_neg_gradient
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : Differentiable ℝ f)
    (hcrit : ∀ t, ∇ f (γ t) ≠ 0) :
    StrictAnti (f ∘ γ) :=
  strictAnti_of_hasDerivAt_neg (fun t ↦ hasDerivAt_comp_neg_gradient hγ (hf (γ t)))
    fun t ↦ neg_lt_zero.mpr (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (hcrit t)))

/-- **Energy identity for a negative gradient trajectory.**  The drop in `f` between two times
equals the integral of the squared norm of its gradient along the trajectory. -/
theorem integral_norm_gradient_sq_eq_sub
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ContDiff ℝ 1 f) :
    ∫ t in a..b, ‖∇ f (γ t)‖ ^ 2 = f (γ a) - f (γ b) := by
  have hgrad : Continuous (fun x ↦ ∇ f x) := by
    exact (toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
  have henergy : Continuous (fun t ↦ ‖∇ f (γ t)‖ ^ 2) :=
    ((hgrad.comp hγ.continuous).norm.pow 2)
  have henergy_neg : Continuous (fun t ↦ -‖∇ f (γ t)‖ ^ 2) := henergy.neg
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (f := f ∘ γ) (f' := fun t ↦ -‖∇ f (γ t)‖ ^ 2)
    (fun t _ ↦ hasDerivAt_comp_neg_gradient hγ (hf.differentiable one_ne_zero (γ t)))
    (henergy_neg.intervalIntegrable a b)
  rw [intervalIntegral.integral_neg] at hFTC
  simpa only [Function.comp_apply, neg_neg, neg_sub] using congrArg Neg.neg hFTC

/-- A periodic negative gradient trajectory consists entirely of critical points.  Thus negative
gradient dynamics has no nonconstant periodic orbit. -/
theorem gradient_eq_zero_of_periodic
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : Differentiable ℝ f)
    {T : ℝ} (hT : 0 < T) (hper : Periodic γ T) (t : ℝ) :
    ∇ f (γ t) = 0 := by
  have hanti := antitone_comp_neg_gradient hγ hf
  have hright : ∀ u ∈ Icc t (t + T), (f ∘ γ) u = (f ∘ γ) t := by
    intro u hu
    apply le_antisymm (hanti hu.1)
    calc
      (f ∘ γ) t = (f ∘ γ) (t + T) := by simp only [Function.comp_apply, hper t]
      _ ≤ (f ∘ γ) u := hanti hu.2
  have hleft : ∀ u ∈ Icc (t - T) t, (f ∘ γ) u = (f ∘ γ) t := by
    intro u hu
    apply le_antisymm
    · calc
        (f ∘ γ) u ≤ (f ∘ γ) (t - T) := hanti hu.1
        _ = (f ∘ γ) t := by
          simpa only [Function.comp_apply, sub_add_cancel] using (congrArg f (hper (t - T))).symm
    · exact hanti hu.2
  have hlocal : (f ∘ γ) =ᶠ[𝓝 t] fun _ ↦ (f ∘ γ) t := by
    filter_upwards [Ioo_mem_nhds (sub_lt_self t hT) (lt_add_of_pos_right t hT)] with u hu
    rcases le_total u t with hut | htu
    · exact hleft u ⟨hu.1.le, hut⟩
    · exact hright u ⟨htu, hu.2.le⟩
  have hzero : deriv (f ∘ γ) t = 0 := by
    rw [hlocal.deriv_eq, deriv_const]
  rw [(hasDerivAt_comp_neg_gradient hγ (hf (γ t))).deriv] at hzero
  simpa only [neg_eq_zero, sq_eq_zero_iff, norm_eq_zero] using hzero

/-- A periodic negative gradient trajectory is constant. -/
theorem eq_of_periodic_neg_gradient
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : Differentiable ℝ f)
    {T : ℝ} (hT : 0 < T) (hper : Periodic γ T) (t u : ℝ) :
    γ t = γ u := by
  apply is_const_of_deriv_eq_zero (fun v ↦ (hγ v).differentiableAt) _ t u
  intro v
  rw [(hγ v).deriv]
  exact neg_eq_zero.mpr (gradient_eq_zero_of_periodic hγ hf hT hper v)

end IsIntegralCurve

end TauCeti
