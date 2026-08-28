/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.MonotoneConvergence
public import TauCeti.Analysis.Calculus.Morse.GradientFlow
public import TauCeti.Dynamics.Flow.Stable
-- Private: used only to recognize a differentiable curve with zero derivative as constant.
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Stable and unstable sets of a negative gradient flow

This file specializes stable and unstable sets to a flow whose trajectories solve the negative
gradient equation.  Along such a flow the defining function is antitone.  Consequently, a point
in the stable set of `q` has value at least `f q`, while a point in the unstable set of `p` has
value at most `f p`.

The intersection `unstableSet φ p ∩ stableSet φ q` is the set underlying the parametrized Morse
trajectories from `p` to `q`.  It is empty unless `f q ≤ f p`; when `p ≠ q`, the inequality is
strict.  In particular a negative gradient flow has no nonconstant homoclinic trajectories.  The
stable-manifold and Morse--Smale theorems will later put smooth manifold structures on these sets
and their intersections.

## Main declarations

* `Flow.IsNegativeGradient.value_le_of_mem_stableSet`: stable-set points lie above the
  limiting critical value.
* `Flow.IsNegativeGradient.value_ge_of_mem_unstableSet`: unstable-set points lie below
  the limiting critical value.
* `Flow.IsNegativeGradient.value_le_of_mem_unstableSet_inter_stableSet`: a connecting
  trajectory goes from a weakly higher critical value to a lower one.
* `Flow.IsNegativeGradient.value_lt_of_mem_unstableSet_inter_stableSet`: the inequality is
  strict for distinct endpoints.
* `Flow.IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet`: there are no
  nonconstant homoclinic trajectories.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
* [Heegaard Floer homology roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HeegaardFloer/README.md),
  Lane M, "Morse homology".
-/

public section

open Filter Function InnerProductSpace Set Topology
open scoped Gradient

namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {φ : _root_.Flow ℝ E} {f : E → ℝ} {p q x : E}

/-- A point in the stable set of `p` has value at least `f p`.  Only differentiability along the
chosen orbit and continuity at its limiting point are required. -/
theorem IsNegativeGradient.value_le_of_mem_stableSet (hφ : IsNegativeGradient φ f)
    (hx : x ∈ stableSet φ p) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) :
    f p ≤ f x := by
  have hlim : Tendsto (fun t ↦ f (φ t x)) atTop (𝓝 (f p)) :=
    hfp.tendsto.comp (mem_stableSet.mp hx)
  simpa only [_root_.Flow.map_zero_apply] using (hφ.orbit_antitone x hf).le_of_tendsto hlim 0

/-- A point in the unstable set of `p` has value at most `f p`.  Only differentiability along the
chosen orbit and continuity at its limiting point are required. -/
theorem IsNegativeGradient.value_ge_of_mem_unstableSet (hφ : IsNegativeGradient φ f)
    (hx : x ∈ unstableSet φ p) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) :
    f x ≤ f p := by
  have hlim : Tendsto (fun t ↦ f (φ t x)) atBot (𝓝 (f p)) :=
    hfp.tendsto.comp (mem_unstableSet.mp hx)
  simpa only [_root_.Flow.map_zero_apply] using (hφ.orbit_antitone x hf).ge_of_tendsto hlim 0

/-- If an orbit converges to `p` in backward time and to `q` in forward time, then `f q ≤ f p`. -/
theorem IsNegativeGradient.value_le_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    f q ≤ f p :=
  (hφ.value_le_of_mem_stableSet hx.2 hf hfq).trans
    (hφ.value_ge_of_mem_unstableSet hx.1 hf hfp)

/-- An orbit on which `f` is constant is constant: any two of its points coincide. -/
private theorem IsNegativeGradient.orbit_eq_of_const_value (hφ : IsNegativeGradient φ f)
    (hf : ∀ t, DifferentiableAt ℝ f (φ t x)) (hc : ∀ t, f (φ t x) = f x) (t u : ℝ) :
    φ t x = φ u x := by
  let γ : ℝ → E := fun v ↦ φ v x
  have hγ : IsIntegralCurve γ (fun _ y ↦ -∇ f y) := hφ.isIntegralCurve x
  apply is_const_of_deriv_eq_zero (fun v ↦ (hγ v).differentiableAt) _ t u
  intro v
  have hgrad : ∇ f (γ v) = 0 :=
    TauCeti.IsIntegralCurve.gradient_eq_zero_of_eventually_const_value hγ (hf v)
      (Eventually.of_forall hc)
  rw [(hγ v).deriv]
  simp only [hgrad, neg_zero]

/-- If an orbit's values converge to the same constant in both forward and backward time, then the
orbit is constant: every time map fixes its initial point. -/
private theorem IsNegativeGradient.orbit_eq_self_of_tendsto_const_value
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    {c : ℝ} (hbot : Tendsto (fun t ↦ f (φ t x)) atBot (𝓝 c))
    (htop : Tendsto (fun t ↦ f (φ t x)) atTop (𝓝 c)) :
    ∀ t, φ t x = x := by
  have hanti := hφ.orbit_antitone x hf
  have hvalue : ∀ t, f (φ t x) = f x := fun t ↦ by
    simpa only [_root_.Flow.map_zero_apply] using le_antisymm
      ((hanti.ge_of_tendsto hbot t).trans (hanti.le_of_tendsto htop 0))
      ((hanti.ge_of_tendsto hbot 0).trans (hanti.le_of_tendsto htop t))
  intro t
  simpa only [_root_.Flow.map_zero_apply] using
    hφ.orbit_eq_of_const_value hf hvalue t 0

/-- A connecting orbit whose two endpoint values agree lies on the constant orbit through the
shared endpoint: `x = p` and `p = q`. -/
theorem IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet_of_value_eq
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) (hpq : f p = f q) :
    x = p ∧ p = q := by
  have horbit := hφ.orbit_eq_self_of_tendsto_const_value hf
    (hfp.tendsto.comp (mem_unstableSet.mp hx.1))
    (by simpa only [hpq, Function.comp_def] using
      hfq.tendsto.comp (mem_stableSet.mp hx.2))
  have hxbot : Tendsto (fun _ : ℝ ↦ x) atBot (𝓝 p) := by
    simpa only [horbit] using mem_unstableSet.mp hx.1
  have hxtop : Tendsto (fun _ : ℝ ↦ x) atTop (𝓝 q) := by
    simpa only [horbit] using mem_stableSet.mp hx.2
  have hpx : x = p := tendsto_nhds_unique tendsto_const_nhds hxbot
  have hxq : x = q := tendsto_nhds_unique tendsto_const_nhds hxtop
  exact ⟨hpx, hpx ▸ hxq⟩

/-- A negative gradient connecting orbit between distinct endpoints strictly lowers the defining
function. -/
theorem IsNegativeGradient.value_lt_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q) (hpq : p ≠ q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    f q < f p := by
  refine lt_of_le_of_ne
    (hφ.value_le_of_mem_unstableSet_inter_stableSet hf hfp hfq hx) ?_
  intro hvalue
  exact hpq
    (hφ.eq_of_mem_unstableSet_inter_stableSet_of_value_eq hf hfp hfq hx
      hvalue.symm).2

/-- A point lying in both the stable and unstable set of the same endpoint lies on the constant
orbit of that endpoint.  Thus a negative gradient flow has no nonconstant homoclinic orbit. -/
theorem IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ p) :
    x = p :=
  (hφ.eq_of_mem_unstableSet_inter_stableSet_of_value_eq hf hfp hfp hx rfl).1

end Flow
