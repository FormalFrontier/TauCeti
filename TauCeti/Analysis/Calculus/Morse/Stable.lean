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

* `Flow.IsNegativeGradient`: every orbit of a flow solves the negative gradient equation.
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

/-- A real flow is the **negative gradient flow** of `f` when each of its orbit curves solves
`γ' = -∇f(γ)`.  Regularity and uniqueness assumptions used to construct the flow remain
separate; this predicate records precisely the differential equation needed by its dynamical
consequences. -/
def IsNegativeGradient (φ : _root_.Flow ℝ E) (f : E → ℝ) : Prop :=
  ∀ x, IsIntegralCurve (fun t ↦ φ t x) (fun _ y ↦ -∇ f y)

/-- The defining orbitwise integral-curve characterization of a negative gradient flow. -/
theorem isNegativeGradient_iff :
    IsNegativeGradient φ f ↔
      ∀ x, IsIntegralCurve (fun t ↦ φ t x) (fun _ y ↦ -∇ f y) :=
  Iff.rfl

/-- The defining function is antitone along every orbit of its negative gradient flow. -/
theorem IsNegativeGradient.antitone_orbit (hφ : IsNegativeGradient φ f) (x : E)
    (hf : ∀ t, DifferentiableAt ℝ f (φ t x)) :
    Antitone (fun t ↦ f (φ t x)) := by
  simpa only [Function.comp_def] using
    TauCeti.IsIntegralCurve.antitone_comp_neg_gradient (hφ x) hf

/-- A point in the stable set of `p` has value at least `f p`.  Only differentiability along the
chosen orbit and continuity at its limiting point are required. -/
theorem IsNegativeGradient.value_le_of_mem_stableSet (hφ : IsNegativeGradient φ f)
    (hx : x ∈ stableSet φ p) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) :
    f p ≤ f x := by
  have hlim : Tendsto (fun t ↦ f (φ t x)) atTop (𝓝 (f p)) :=
    hfp.tendsto.comp (mem_stableSet.mp hx)
  simpa only [_root_.Flow.map_zero_apply] using (hφ.antitone_orbit x hf).le_of_tendsto hlim 0

/-- A point in the unstable set of `p` has value at most `f p`.  Only differentiability along the
chosen orbit and continuity at its limiting point are required. -/
theorem IsNegativeGradient.value_ge_of_mem_unstableSet (hφ : IsNegativeGradient φ f)
    (hx : x ∈ unstableSet φ p) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) :
    f x ≤ f p := by
  have hlim : Tendsto (fun t ↦ f (φ t x)) atBot (𝓝 (f p)) :=
    hfp.tendsto.comp (mem_unstableSet.mp hx)
  simpa only [_root_.Flow.map_zero_apply] using (hφ.antitone_orbit x hf).ge_of_tendsto hlim 0

/-- If an orbit converges to `p` in backward time and to `q` in forward time, then `f q ≤ f p`. -/
theorem IsNegativeGradient.value_le_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) :
    f q ≤ f p :=
  (hφ.value_le_of_mem_stableSet hx.2 hf hfq).trans
    (hφ.value_ge_of_mem_unstableSet hx.1 hf hfp)

private theorem IsNegativeGradient.orbit_eq_of_comp_eq (hφ : IsNegativeGradient φ f)
    (hf : ∀ t, DifferentiableAt ℝ f (φ t x)) (hc : ∀ t, f (φ t x) = f x) (t u : ℝ) :
    φ t x = φ u x := by
  let γ : ℝ → E := fun v ↦ φ v x
  have hγ : IsIntegralCurve γ (fun _ y ↦ -∇ f y) := hφ x
  apply is_const_of_deriv_eq_zero (fun v ↦ (hγ v).differentiableAt) _ t u
  intro v
  have hzero : deriv (f ∘ γ) v = 0 := by
    have heq : (f ∘ γ) =ᶠ[𝓝 v] fun _ ↦ f x :=
      Eventually.of_forall fun w ↦ hc w
    rw [heq.deriv_eq, deriv_const]
  rw [(TauCeti.IsIntegralCurve.hasDerivAt_comp_neg_gradient hγ (hf v)).deriv] at hzero
  have hgrad : ∇ f (γ v) = 0 := by
    simpa only [neg_eq_zero, sq_eq_zero_iff, norm_eq_zero] using hzero
  rw [(hγ v).deriv]
  simp only [hgrad, neg_zero]

private theorem eq_zero_of_antitone_of_tendsto_atBot_atTop {g : ℝ → ℝ} {a : ℝ}
    (hg : Antitone g) (hbot : Tendsto g atBot (𝓝 a)) (htop : Tendsto g atTop (𝓝 a))
    (t : ℝ) :
    g t = g 0 := by
  apply le_antisymm
  · exact (hg.ge_of_tendsto hbot t).trans (hg.le_of_tendsto htop 0)
  · exact (hg.ge_of_tendsto hbot 0).trans (hg.le_of_tendsto htop t)

/-- A connecting orbit whose two endpoint values agree has equal endpoints. -/
theorem IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet_of_value_eq
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) (hpq : f p = f q) :
    p = q := by
  have hanti := hφ.antitone_orbit x hf
  have hp : Tendsto (fun t ↦ f (φ t x)) atBot (𝓝 (f p)) :=
    hfp.tendsto.comp (mem_unstableSet.mp hx.1)
  have hq : Tendsto (fun t ↦ f (φ t x)) atTop (𝓝 (f q)) :=
    hfq.tendsto.comp (mem_stableSet.mp hx.2)
  have hq' : Tendsto (fun t ↦ f (φ t x)) atTop (𝓝 (f p)) := by
    simpa only [hpq] using hq
  have hvalue : ∀ t, f (φ t x) = f x := fun t ↦ by
    simpa only [_root_.Flow.map_zero_apply] using
      eq_zero_of_antitone_of_tendsto_atBot_atTop hanti hp hq' t
  have horbit : ∀ t, φ t x = x := by
    intro t
    simpa only [_root_.Flow.map_zero_apply] using
      hφ.orbit_eq_of_comp_eq hf hvalue t 0
  have hpt : Tendsto (fun _ : ℝ ↦ x) atBot (𝓝 p) := by
    simpa only [horbit] using mem_unstableSet.mp hx.1
  have hqt : Tendsto (fun _ : ℝ ↦ x) atTop (𝓝 q) := by
    simpa only [horbit] using mem_stableSet.mp hx.2
  have hpx : p = x := tendsto_nhds_unique hpt tendsto_const_nhds
  have hxq : x = q := tendsto_nhds_unique tendsto_const_nhds hqt
  exact hpx.trans hxq

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
    (hφ.eq_of_mem_unstableSet_inter_stableSet_of_value_eq hf hfp hfq hx hvalue.symm)

/-- A point lying in both the stable and unstable set of the same endpoint lies on the constant
orbit of that endpoint.  Thus a negative gradient flow has no nonconstant homoclinic orbit. -/
theorem IsNegativeGradient.eq_of_mem_unstableSet_inter_stableSet
    (hφ : IsNegativeGradient φ f) (hf : ∀ t, DifferentiableAt ℝ f (φ t x))
    (hfp : ContinuousAt f p)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ p) :
    x = p := by
  have hanti := hφ.antitone_orbit x hf
  have hpbot : Tendsto (fun t ↦ f (φ t x)) atBot (𝓝 (f p)) :=
    hfp.tendsto.comp (mem_unstableSet.mp hx.1)
  have hptop : Tendsto (fun t ↦ f (φ t x)) atTop (𝓝 (f p)) :=
    hfp.tendsto.comp (mem_stableSet.mp hx.2)
  have hvalue : ∀ t, f (φ t x) = f x := fun t ↦ by
    simpa only [_root_.Flow.map_zero_apply] using
      eq_zero_of_antitone_of_tendsto_atBot_atTop hanti hpbot hptop t
  have horbit : ∀ t, φ t x = x := by
    intro t
    simpa only [_root_.Flow.map_zero_apply] using
      hφ.orbit_eq_of_comp_eq hf hvalue t 0
  have hlim : Tendsto (fun _ : ℝ ↦ x) atTop (𝓝 p) := by
    simpa only [horbit] using mem_stableSet.mp hx.2
  exact tendsto_nhds_unique tendsto_const_nhds hlim

end Flow
