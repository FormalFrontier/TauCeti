/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
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
* `TauCeti.IsIntegralCurveOn.integral_norm_gradient_sq_eq_sub` and
  `TauCeti.IsIntegralCurve.integral_norm_gradient_sq_eq_sub`: the energy identity.
* `TauCeti.IsIntegralCurve.gradient_eq_zero_of_eventually_const_value`: a trajectory on which
  `f` is eventually constant passes through critical points.
* `TauCeti.IsIntegralCurve.gradient_eq_zero_of_periodic` and
  `TauCeti.IsIntegralCurve.eq_of_periodic_neg_gradient`: a periodic negative gradient trajectory
  consists entirely of critical points and is constant.
* `Flow.IsNegativeGradient`: every orbit of a flow solves the negative gradient equation.
* `Flow.isNegativeGradient_iff`: the introduction and elimination rule for that predicate.
* `Flow.IsNegativeGradient.isIntegralCurve`: the orbit curve through a point, as an integral
  curve of the negative gradient field.
* `Flow.IsNegativeGradient.orbit_antitone`: the defining function is antitone along every orbit
  of its negative gradient flow.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HeegaardFloer/README.md),
  Lane M, "Morse homology".
-/

public section

open Filter Function InnerProductSpace MeasureTheory Set
open scoped Gradient Interval Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {γ : ℝ → E} {s : Set ℝ} {t a b : ℝ}

/-- A constant curve is an integral curve of the negative gradient field exactly when its value
is a critical point of that field. -/
@[simp]
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

/-- **Energy identity for a negative gradient trajectory.**  Between two times of the trajectory's
time domain, the drop in `f` equals the integral of the squared norm of its gradient along the
trajectory. -/
theorem integral_norm_gradient_sq_eq_sub
    (hγ : IsIntegralCurveOn γ (fun _ x ↦ -∇ f x) s) (hsub : [[a, b]] ⊆ s)
    (hf : ∀ t ∈ [[a, b]], DifferentiableAt ℝ f (γ t))
    (hint : IntervalIntegrable (fun t ↦ ‖∇ f (γ t)‖ ^ 2) volume a b) :
    ∫ t in a..b, ‖∇ f (γ t)‖ ^ 2 = f (γ a) - f (γ b) := by
  have huIcc : [[a, b]] = Icc (min a b) (max a b) := by
    rcases le_total a b with hab | hab <;> simp [hab, uIcc_of_le, uIcc_of_ge]
  have hcont : ContinuousOn (f ∘ γ) [[a, b]] := fun t ht ↦
    ((hf t ht).continuousAt.comp_continuousWithinAt (hγ.continuousWithinAt (hsub ht))).mono hsub
  have hmax : max a b ∈ [[a, b]] := by rw [huIcc]; exact right_mem_Icc.2 min_le_max
  have hderiv : ∀ t ∈ Ioo (min a b) (max a b),
      HasDerivWithinAt (f ∘ γ) (-‖∇ f (γ t)‖ ^ 2) (Ioi t) t := by
    intro t ht
    have htmem : t ∈ [[a, b]] := by rw [huIcc]; exact Ioo_subset_Icc_self ht
    exact ((hasDerivWithinAt_comp_neg_gradient hγ (hsub htmem) (hf t htmem)).mono
      hsub).mono_of_mem_nhdsWithin (ordConnected_uIcc.mem_nhdsGT htmem hmax ht.2)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hderiv hint.neg
  rw [intervalIntegral.integral_neg] at hFTC
  simpa only [Function.comp_apply, neg_neg, neg_sub] using congrArg Neg.neg hFTC

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
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ∀ t, DifferentiableAt ℝ f (γ t)) :
    Antitone (f ∘ γ) :=
  antitone_of_hasDerivAt_nonpos
    (fun t ↦ hasDerivAt_comp_neg_gradient hγ (hf t)) fun _ ↦ neg_nonpos.mpr (sq_nonneg _)

/-- If a global negative gradient trajectory contains no critical point, then the value of `f` is
strictly decreasing along it. -/
theorem strictAnti_comp_neg_gradient
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ∀ t, DifferentiableAt ℝ f (γ t))
    (hcrit : ∀ t, ∇ f (γ t) ≠ 0) :
    StrictAnti (f ∘ γ) :=
  strictAnti_of_hasDerivAt_neg (fun t ↦ hasDerivAt_comp_neg_gradient hγ (hf t))
    fun t ↦ neg_lt_zero.mpr (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (hcrit t)))

/-- **Energy identity for a global negative gradient trajectory.**  The drop in `f` between two
times equals the integral of the squared norm of its gradient along the trajectory. -/
theorem integral_norm_gradient_sq_eq_sub
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ∀ t, DifferentiableAt ℝ f (γ t))
    (hint : IntervalIntegrable (fun t ↦ ‖∇ f (γ t)‖ ^ 2) volume a b) :
    ∫ t in a..b, ‖∇ f (γ t)‖ ^ 2 = f (γ a) - f (γ b) :=
  IsIntegralCurveOn.integral_norm_gradient_sq_eq_sub (hγ.isIntegralCurveOn univ)
    (subset_univ _) (fun t _ ↦ hf t) hint

/-- If the value of `f` is eventually constant along a global negative gradient trajectory, then
the gradient of `f` vanishes at the corresponding point. -/
theorem gradient_eq_zero_of_eventually_const_value
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : DifferentiableAt ℝ f (γ t))
    {c : ℝ} (hval : ∀ᶠ u in 𝓝 t, f (γ u) = c) :
    ∇ f (γ t) = 0 := by
  have hzero : deriv (f ∘ γ) t = 0 := by
    have heq : (f ∘ γ) =ᶠ[𝓝 t] fun _ ↦ c := hval
    rw [heq.deriv_eq, deriv_const]
  rw [(hasDerivAt_comp_neg_gradient hγ hf).deriv] at hzero
  simpa only [neg_eq_zero, sq_eq_zero_iff, norm_eq_zero] using hzero

/-- A periodic negative gradient trajectory consists entirely of critical points.  Thus negative
gradient dynamics has no nonconstant periodic orbit. -/
theorem gradient_eq_zero_of_periodic
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ∀ t, DifferentiableAt ℝ f (γ t))
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
  have hconst : ∀ᶠ u in 𝓝 t, f (γ u) = (f ∘ γ) t := by
    filter_upwards [Ioo_mem_nhds (sub_lt_self t hT) (lt_add_of_pos_right t hT)] with u hu
    rcases le_total u t with hut | htu
    · exact hleft u ⟨hu.1.le, hut⟩
    · exact hright u ⟨htu, hu.2.le⟩
  exact gradient_eq_zero_of_eventually_const_value hγ (hf t) hconst

/-- A periodic negative gradient trajectory is constant. -/
theorem eq_of_periodic_neg_gradient
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ∀ t, DifferentiableAt ℝ f (γ t))
    {T : ℝ} (hT : 0 < T) (hper : Periodic γ T) (t u : ℝ) :
    γ t = γ u := by
  apply is_const_of_deriv_eq_zero (fun v ↦ (hγ v).differentiableAt) _ t u
  intro v
  rw [(hγ v).deriv]
  exact neg_eq_zero.mpr (gradient_eq_zero_of_periodic hγ hf hT hper v)

end IsIntegralCurve

end TauCeti

namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {φ : _root_.Flow ℝ E}

/-- A real flow is the **negative gradient flow** of `f` when each of its orbit curves solves
`γ' = -∇f(γ)`.  Regularity and uniqueness assumptions used to construct the flow remain
separate; this predicate records precisely the differential equation needed by its dynamical
consequences. -/
def IsNegativeGradient (φ : _root_.Flow ℝ E) (f : E → ℝ) : Prop :=
  ∀ x, IsIntegralCurve (fun t ↦ φ t x) (fun _ y ↦ -∇ f y)

/-- The introduction and elimination rule for a negative-gradient flow. -/
theorem isNegativeGradient_iff : IsNegativeGradient φ f ↔
    ∀ x, IsIntegralCurve (fun t ↦ φ t x) (fun _ y ↦ -∇ f y) :=
  Iff.rfl

/-- Each orbit curve of a negative gradient flow solves the negative gradient equation. -/
theorem IsNegativeGradient.isIntegralCurve (hφ : IsNegativeGradient φ f) (x : E) :
    IsIntegralCurve (fun t ↦ φ t x) (fun _ y ↦ -∇ f y) :=
  hφ x

/-- The defining function is antitone along every orbit of its negative gradient flow. -/
theorem IsNegativeGradient.orbit_antitone (hφ : IsNegativeGradient φ f) (x : E)
    (hf : ∀ t, DifferentiableAt ℝ f (φ t x)) :
    Antitone (fun t ↦ f (φ t x)) := by
  simpa only [Function.comp_def] using
    TauCeti.IsIntegralCurve.antitone_comp_neg_gradient (hφ x) hf

end Flow
