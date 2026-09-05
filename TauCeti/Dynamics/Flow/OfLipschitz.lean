/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import TauCeti.Analysis.ODE.GlobalSolution

/-!
# The flow of a globally Lipschitz vector field

A vector field whose solutions may blow up in finite time generates no flow: the group law
`φ (t₁ + t₂) = φ t₁ ∘ φ t₂` needs solutions defined for all time. A globally Lipschitz vector
field on a Banach space has them, by `ODE.globalSolution`, and this file assembles them into a
`Flow ℝ E`.

The group law is uniqueness of solutions applied to the time-translated orbit, the identity law is
the initial condition, and the joint continuity required by `Flow` is
`ODE.continuous_globalSolution`.

## Main declarations

* `TauCeti.flowOfLipschitz`: the flow of a globally Lipschitz vector field on a Banach space.
* `TauCeti.hasDerivAt_flowOfLipschitz` and `TauCeti.isIntegralCurve_flowOfLipschitz`: its
  orbits solve the differential equation.
* `TauCeti.eq_flowOfLipschitz`: every global solution is an orbit of the flow.
* `TauCeti.flowOfLipschitz_congr`: it does not depend on the chosen Lipschitz bound.
* `TauCeti.forall_flowOfLipschitz_eq_self_iff`: the rest points of the flow are the zeros of the
  vector field.

## References

* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press, 1969, Chapter X.
-/

public section

open Filter Topology
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {v : E → E} {K : ℝ≥0}

/-- **The flow of a globally Lipschitz vector field** on a Banach space: the time-`t` map sends an
initial point to the value at time `t` of the unique global solution of `γ' = v ∘ γ` through it. -/
noncomputable def flowOfLipschitz (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) : Flow ℝ E where
  toFun t x := ODE.globalSolution v hv x t
  cont' := ODE.continuous_globalSolution v hv
  map_add' t₁ t₂ x := by
    simpa [add_comm] using ODE.globalSolution_add v hv x t₂ t₁
  map_zero' x := ODE.globalSolution_zero v hv x

@[simp]
theorem flowOfLipschitz_apply (hv : LipschitzWith K v) (t : ℝ) (x : E) :
    flowOfLipschitz v hv t x = ODE.globalSolution v hv x t := (rfl)

/-- **Independence of the Lipschitz bound.** Two Lipschitz witnesses for the same vector field,
with possibly different constants, produce the same flow. -/
theorem flowOfLipschitz_congr {K' : ℝ≥0} (hv : LipschitzWith K v) (hv' : LipschitzWith K' v) :
    flowOfLipschitz v hv = flowOfLipschitz v hv' :=
  Flow.ext fun t x ↦ congrFun (ODE.globalSolution_congr v hv hv' x) t

/-- Every orbit of the flow solves the differential equation. -/
theorem hasDerivAt_flowOfLipschitz (hv : LipschitzWith K v) (x : E) (t : ℝ) :
    HasDerivAt (fun t ↦ flowOfLipschitz v hv t x) (v (flowOfLipschitz v hv t x)) t :=
  ODE.hasDerivAt_globalSolution v hv x t

/-- Every orbit of the flow is an integral curve of the vector field. -/
theorem isIntegralCurve_flowOfLipschitz (hv : LipschitzWith K v) (x : E) :
    IsIntegralCurve (fun t ↦ flowOfLipschitz v hv t x) fun _ y ↦ v y :=
  ODE.isIntegralCurve_globalSolution v hv x

/-- **Every global solution is an orbit** of the flow, namely the one through its initial value. -/
theorem eq_flowOfLipschitz (hv : LipschitzWith K v) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (t : ℝ) : γ t = flowOfLipschitz v hv t (γ 0) :=
  congrFun (ODE.eq_globalSolution v hv hγ) t

/-- **The rest points of the flow are the zeros of the vector field.** -/
theorem forall_flowOfLipschitz_eq_self_iff (hv : LipschitzWith K v) (x : E) :
    (∀ t, flowOfLipschitz v hv t x = x) ↔ v x = 0 := by
  refine ⟨fun h ↦ ?_, fun h t ↦ ?_⟩
  · have h1 : HasDerivAt (fun t ↦ flowOfLipschitz v hv t x)
        (v (flowOfLipschitz v hv 0 x)) 0 :=
      hasDerivAt_flowOfLipschitz hv x 0
    have h2 : HasDerivAt (fun t : ℝ ↦ flowOfLipschitz v hv t x) 0 0 :=
      (hasDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq (.of_forall h)
    have h3 := h1.unique h2
    rwa [h 0] at h3
  · have hconst : ∀ s : ℝ, HasDerivAt (fun _ : ℝ ↦ x) (v ((fun _ : ℝ ↦ x) s)) s := fun s ↦ by
      simpa [h] using hasDerivAt_const s x
    simpa using (eq_flowOfLipschitz hv hconst t).symm

end TauCeti
