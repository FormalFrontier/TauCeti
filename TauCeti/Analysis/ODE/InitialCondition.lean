/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.GlobalSolution
public import TauCeti.Analysis.ODE.SmoothParameter

/-!
# Smooth dependence of an ODE solution on its initial condition

Picard iteration produces a solution of `γ' = v ∘ γ` continuously, indeed Lipschitzly, in the
initial condition. It says nothing about differentiability: the contraction argument is metric.
This file upgrades continuity to smoothness of the same order as the field, jointly in the initial
condition and in time, near time `0`.

The mechanism is a change of variables that turns the initial condition into a *parameter* of a
new equation, so that `ODE.exists_contDiffAt_picard_solution_of_contDiff` applies. Writing a
solution through `x` as `t ↦ x + u (t / ε)`, the curve `u` solves

`u' s = ε • v (x + u s)`, `u 0 = 0`

on the fixed time interval `[0, 1]`, with `(x, ε)` a parameter and the initial state `0` fixed.
At `ε = 0` that field vanishes identically, which is exactly the degeneracy hypothesis of the
parameterized Picard theorem, and the solution at the base parameter is the constant curve `0`.
Evaluating the resulting smooth family of paths at the endpoint `s = 1` — a continuous linear
map on the path space — produces `x + u 1`, which `ODE_solution_unique` identifies with
the value of the global solution at time `ε`. Both the initial condition and the time are
therefore smooth directions.

## Main results

* `ODE.contDiffAt_globalSolution`: the global solution of a globally Lipschitz `C^(n+1)` field is
  `C^(n+1)` in time and initial condition near time `0`, for `n` finite or infinite.
* `ODE.eventually_contDiffAt_globalSolution`: at every small time, the time-`t` map of such a
  field is `C^(n+1)` in the initial condition.
* `ODE.exists_contDiffAt_localFlow`: a vector field which is `C^(n+1)` on a neighbourhood of a
  point has a local flow through the nearby points which is `C^(n+1)` in time and initial
  condition near that point at time `0`, and which obeys the flow law
  `Φ x (t + u) = Φ (Φ x t) u`.

The local flow produced here is the model-space input to the smooth flow of a vector field on a
manifold, and in particular to the flow of the geodesic spray, whose base curves are the
geodesics of a Riemannian metric.

## References

* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press, 1969, Chapter X.
-/

public section

open Filter Set Topology
open scoped ContDiff NNReal

noncomputable section

universe u

namespace ODE

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Time rescaling.** A curve solving the field `v` sped up by the factor `ε` on the unit
interval reaches, at time `1`, the value of the global solution at time `ε`. Only right
derivatives are required, which is the form in which the parameterized Picard theorem delivers
its solutions. -/
private theorem eq_globalSolution_of_smul [CompleteSpace E] (v : E → E) {K : ℝ≥0}
    (hv : LipschitzWith K v) (x : E) (ε : ℝ) {u : ℝ → E} (hu₀ : u 0 = x)
    (hu : ContinuousOn u (Icc 0 1))
    (hu' : ∀ s ∈ Ico (0 : ℝ) 1, HasDerivWithinAt u (ε • v (u s)) (Ici s) s) :
    u 1 = globalSolution v hv x ε := by
  have hflow : ∀ s : ℝ, HasDerivAt (fun r : ℝ ↦ globalSolution v hv x (ε * r))
      (ε • v (globalSolution v hv x (ε * s))) s := fun s ↦ by
    simpa [Function.comp_def, mul_comm] using
      (hasDerivAt_globalSolution v hv x (ε * s)).scomp s ((hasDerivAt_id s).const_mul ε)
  have heq := ODE_solution_unique (v := fun _ z ↦ ε • v z) (K := ‖ε‖₊ * K)
    (a := 0) (b := 1) (f := u) (g := fun r ↦ globalSolution v hv x (ε * r))
    (fun _ ↦ (lipschitzWith_smul ε).comp hv) hu hu'
    (((continuous_globalSolution_apply v hv x).comp
      (continuous_const.mul continuous_id)).continuousOn)
    (fun s _ ↦ (hflow s).hasDerivWithinAt)
    (by simp [hu₀])
  simpa using heq (right_mem_Icc.2 zero_le_one)

section

variable [CompleteSpace E]

/-- The finite-order form of `ODE.contDiffAt_globalSolution`, which is where the parameterized
Picard theorem applies. -/
private theorem contDiffAt_globalSolution_nat (n : ℕ) (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v)
    (hvs : ContDiff ℝ (n + 1) v) (a : E) :
    ContDiffAt ℝ (n + 1) (fun p : E × ℝ ↦ globalSolution v hv p.1 p.2) (a, 0) := by
  -- The field of the rescaled equation, with the initial condition and the speed as parameters.
  have hf : ContDiff ℝ (n + 1) fun q : (E × ℝ) × E ↦ q.1.2 • v (q.1.1 + q.2) :=
    ContDiff.smul (contDiff_fst.snd) (hvs.comp (contDiff_fst.fst.add contDiff_snd))
  have hzero : ∀ᶠ y in nhds (0 : E),
      (fun q : (E × ℝ) × E ↦ q.1.2 • v (q.1.1 + q.2)) (((a, (0 : ℝ))), y) = 0 :=
    .of_forall fun y ↦ zero_smul ℝ _
  obtain ⟨γ, hγ, -, hprop⟩ :=
    exists_contDiffAt_picard_solution_of_contDiff n
      (fun q : (E × ℝ) × E ↦ q.1.2 • v (q.1.1 + q.2)) (a, (0 : ℝ)) (0 : E) hf hzero
  have hsmooth : ContDiffAt ℝ (n + 1)
      (fun p : E × ℝ ↦ p.1 + γ p ⟨1, by norm_num⟩) (a, 0) := by
    have := ((ContinuousMap.evalCLM (R := ℝ) (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1)).contDiff
      (n := (n + 1 : ℕ))).comp_contDiffAt (a, (0 : ℝ)) hγ
    exact contDiffAt_fst.add (by simpa [Function.comp_def] using this)
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [hprop] with p hp
  obtain ⟨hpicard, -, hright⟩ := hp
  -- The rescaled solution starts at `p.1` and moves with speed `p.2 • v`.
  have hbase : γ p ⟨0, by norm_num⟩ = 0 := by simpa using hpicard ⟨0, by norm_num⟩
  have hcont : ContinuousOn (fun s : ℝ ↦ p.1 + γ p (projIcc 0 1 zero_le_one s)) (Icc 0 1) :=
    Continuous.continuousOn (by fun_prop)
  have hderiv : ∀ s ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun r : ℝ ↦ p.1 + γ p (projIcc 0 1 zero_le_one r))
        (p.2 • v (p.1 + γ p (projIcc 0 1 zero_le_one s))) (Ici s) s :=
    fun s hs ↦ (hright s hs).const_add p.1
  have := eq_globalSolution_of_smul v hv p.1 p.2
    (u := fun s : ℝ ↦ p.1 + γ p (projIcc 0 1 zero_le_one s))
    (by simpa [projIcc_left] using congrArg (fun w : E ↦ p.1 + w) hbase) hcont hderiv
  simpa [projIcc_right] using this.symm

/-- **The global solution of a globally Lipschitz field depends smoothly on time and on its
initial condition**, near time `0`, at the order of the field. -/
theorem contDiffAt_globalSolution {n : ℕ∞} (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v)
    (hvs : ContDiff ℝ (n + 1) v) (a : E) :
    ContDiffAt ℝ (n + 1) (fun p : E × ℝ ↦ globalSolution v hv p.1 p.2) (a, 0) := by
  induction n using ENat.recTopCoe with
  | top =>
    have htop : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = ∞ := by
      norm_cast
    rw [htop] at hvs ⊢
    exact contDiffAt_infty.2 fun m ↦
      (contDiffAt_globalSolution_nat m v hv (hvs.of_le (by exact_mod_cast le_top)) a).of_le
        (by exact_mod_cast Nat.le_succ m)
  | coe m => exact contDiffAt_globalSolution_nat m v hv (by exact_mod_cast hvs) a

/-- **`C^(n+1)` dependence on the initial condition.** For every small time the time-`t` map of a
globally Lipschitz `C^(n+1)` field is `C^(n+1)` at the base point. The order is finite here
because smoothness of infinite order at one point does not propagate to a neighbourhood. -/
theorem eventually_contDiffAt_globalSolution (n : ℕ) (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v)
    (hvs : ContDiff ℝ (n + 1) v) (a : E) :
    ∀ᶠ t in nhds (0 : ℝ), ContDiffAt ℝ (n + 1) (fun x ↦ globalSolution v hv x t) a := by
  have hev := (contDiffAt_globalSolution (n := (n : ℕ∞)) v hv
    (by exact_mod_cast hvs) a).eventually (by simp)
  have hslice := (continuousAt_const.prodMk continuousAt_id).eventually hev
  filter_upwards [hslice] with t ht
  exact ht.comp a (contDiffAt_id.prodMk contDiffAt_const)

end

/-- **The local flow of a smooth vector field.** A field which is `C^(n+1)` on a neighbourhood of
`a` admits a flow `Φ`: a family of curves, one through each point, which start at that point,
obey the flow law `Φ x (t + u) = Φ (Φ x t) u`, depend on the initial condition and the time in a
`C^(n+1)` way near `(a, 0)`, and solve the equation for every initial condition and time in some
neighbourhood of `(a, 0)`. No global hypothesis on the field is needed: a bump function cuts the
field down to a globally Lipschitz one agreeing with it near `a`, and the two fields still agree
along the curves at the times where the equation is claimed. The flow law holds for all times
because `Φ` is the global flow of that cut-off field; only the equation for `v` is local. -/
theorem exists_contDiffAt_localFlow [FiniteDimensional ℝ E] {n : ℕ∞} (v : E → E) {a : E}
    {s : Set E} (hv : ContDiffOn ℝ (n + 1) v s) (hs : s ∈ nhds a) :
    ∃ Φ : E → ℝ → E, ContDiffAt ℝ (n + 1) (fun p : E × ℝ ↦ Φ p.1 p.2) (a, 0) ∧
      (∀ x, Φ x 0 = x) ∧ (∀ x t u, Φ x (t + u) = Φ (Φ x t) u) ∧
      ∀ᶠ p in nhds ((a, 0) : E × ℝ), HasDerivAt (Φ p.1) (v (Φ p.1 p.2)) p.2 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨g, K, hg, hgK, hgv⟩ :=
    hv.exists_lipschitzWith_contDiff_eventuallyEq_of_finiteDimensional hs
  refine ⟨globalSolution g hgK, contDiffAt_globalSolution g hgK hg a,
    fun x ↦ globalSolution_zero g hgK x, fun x t u ↦ globalSolution_add g hgK x t u, ?_⟩
  have htends : Tendsto (fun p : E × ℝ ↦ globalSolution g hgK p.1 p.2) (nhds ((a, 0) : E × ℝ))
      (nhds a) := by
    have hcont : Continuous fun p : E × ℝ ↦ globalSolution g hgK p.1 p.2 :=
      (continuous_globalSolution g hgK).comp (continuous_snd.prodMk continuous_fst)
    have h := hcont.tendsto ((a, 0) : E × ℝ)
    simp only [globalSolution_zero] at h
    exact h
  filter_upwards [htends.eventually hgv] with p hp
  exact hp ▸ hasDerivAt_globalSolution g hgK p.1 p.2

end ODE

end
