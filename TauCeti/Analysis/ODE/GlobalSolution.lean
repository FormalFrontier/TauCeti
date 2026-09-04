/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# The global solution of a globally Lipschitz autonomous ODE

Picard--Lindelöf solves `γ' = v ∘ γ` only on a small time interval, because a solution can escape
to infinity in finite time. When the vector field is *globally* Lipschitz no such escape happens,
and through every initial point there is exactly one solution defined on all of `ℝ`. This file
constructs it, as `ODE.globalSolution`.

The construction is the Picard iteration performed once and for all on the whole line, in the
weighted norm that makes it a contraction there. Writing `w t = cosh (2 k t)` for a Lipschitz
constant `k > 0` of `v`, a curve is presented as `γ t = x + w t • u t` with `u : ℝ →ᵇ E` bounded
continuous, and the Picard operator becomes

`(P u) t = (w t)⁻¹ • ∫ s in 0..t, v (x + w s • u s)`.

Since `∫ s in 0..t, w s = sinh (2 k t) / (2 k)` and `|sinh| ≤ cosh`, the operator `P` maps
`ℝ →ᵇ E` to itself and halves distances, for either sign of `t`, so there is no need to glue local
solutions: `P` has a unique fixed point on the whole line. The associated curve
satisfies `γ t = x + ∫ s in 0..t, v (γ s)`, hence solves the differential equation. Uniqueness is
Mathlib's `ODE_solution_unique_univ`, and the fixed point depends on the initial condition
`1`-Lipschitzly, which gives joint continuity in time and initial condition.

## Main declarations

* `ODE.globalSolution`: the solution of `γ' = v ∘ γ` with `γ 0 = x` on all of `ℝ`.
* `ODE.globalSolution_eq_integral`: it satisfies the integral equation of the initial value
  problem.
* `ODE.globalSolution_zero` and `ODE.hasDerivAt_globalSolution`: it is a solution.
* `ODE.eq_globalSolution`: every global solution with the same initial value is equal to it.
* `ODE.globalSolution_congr`: it does not depend on the chosen Lipschitz bound.
* `ODE.globalSolution_neg`: reversing time solves the negated field.
* `ODE.dist_globalSolution_le`: two solutions drift apart at most exponentially.
* `ODE.continuous_globalSolution`: joint continuity in time and initial condition.

## References

* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press, 1969, Chapter X.
-/

public section

open Filter MeasureTheory Set Topology
open scoped BoundedContinuousFunction NNReal

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The estimate that drives the whole construction: an integrand dominated by `C * cosh (2 k ·)`
has a primitive dominated by `C * cosh (2 k ·) / (2 k)`, with no restriction on the sign of the
upper limit. -/
private theorem norm_integral_le_cosh {k C : ℝ} (hk : 0 < k) (hC : 0 ≤ C) {F : ℝ → E}
    (hF : ∀ s, ‖F s‖ ≤ C * Real.cosh (2 * k * s)) (t : ℝ) :
    ‖∫ s in (0 : ℝ)..t, F s‖ ≤ C * Real.cosh (2 * k * t) / (2 * k) := by
  have hk2 : (0 : ℝ) < 2 * k := by linarith
  have hg : Continuous fun s : ℝ ↦ C * Real.cosh (2 * k * s) := by fun_prop
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ C * Real.sinh (2 * k * s) / (2 * k))
      (C * Real.cosh (2 * k * s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ ↦ 2 * k * s) (2 * k) s := by
      simpa using (hasDerivAt_id s).const_mul (2 * k)
    have h2 : HasDerivAt (fun s : ℝ ↦ Real.sinh (2 * k * s))
        (Real.cosh (2 * k * s) * (2 * k)) s := (Real.hasDerivAt_sinh (2 * k * s)).comp s h1
    have h3 : HasDerivAt (fun s : ℝ ↦ C * Real.sinh (2 * k * s) / (2 * k))
        (C * (Real.cosh (2 * k * s) * (2 * k)) / (2 * k)) s := (h2.const_mul C).div_const (2 * k)
    have hval : C * (Real.cosh (2 * k * s) * (2 * k)) / (2 * k) = C * Real.cosh (2 * k * s) := by
      rw [div_eq_iff hk2.ne']
      ring
    rwa [hval] at h3
  have hcalc : ∫ s in (0 : ℝ)..t, C * Real.cosh (2 * k * s) =
      C * Real.sinh (2 * k * t) / (2 * k) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv s)
      (hg.intervalIntegrable _ _)]
    simp
  calc ‖∫ s in (0 : ℝ)..t, F s‖
      ≤ |∫ s in (0 : ℝ)..t, C * Real.cosh (2 * k * s)| :=
        intervalIntegral.norm_integral_le_abs_of_norm_le (.of_forall fun s ↦ hF s)
          (hg.intervalIntegrable _ _)
    _ = C * |Real.sinh (2 * k * t)| / (2 * k) := by
        rw [hcalc, abs_div, abs_mul, abs_of_nonneg hC, abs_of_pos hk2]
    _ ≤ C * Real.cosh (2 * k * t) / (2 * k) := by
        gcongr
        rw [Real.abs_sinh, ← Real.cosh_abs (2 * k * t)]
        exact (Real.sinh_lt_cosh _).le

/-- The curve carried by a bounded continuous profile `u`, weighted so that the Picard operator
below is a contraction on the whole line. -/
private noncomputable def picardCurve (k : ℝ) (x : E) (u : ℝ →ᵇ E) (t : ℝ) : E :=
  x + Real.cosh (2 * k * t) • u t

private theorem continuous_picardCurve (k : ℝ) (x : E) (u : ℝ →ᵇ E) :
    Continuous (picardCurve k x u) := by
  have hu : Continuous (⇑u) := u.continuous
  unfold picardCurve
  fun_prop

private theorem norm_picardCurve_sub_le (k : ℝ) (x : E) (u : ℝ →ᵇ E) (t : ℝ) :
    ‖picardCurve k x u t - x‖ ≤ Real.cosh (2 * k * t) * ‖u‖ := by
  have h : picardCurve k x u t - x = Real.cosh (2 * k * t) • u t := by
    simp [picardCurve]
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
  exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm t) (Real.cosh_pos _).le

private theorem picardCurve_sub (k : ℝ) (x : E) (u₁ u₂ : ℝ →ᵇ E) (t : ℝ) :
    picardCurve k x u₁ t - picardCurve k x u₂ t = Real.cosh (2 * k * t) • (u₁ t - u₂ t) := by
  simp [picardCurve, smul_sub]

private theorem picardCurve_sub_const (k : ℝ) (x y : E) (u : ℝ →ᵇ E) (t : ℝ) :
    picardCurve k x u t - picardCurve k y u t = x - y := by
  simp [picardCurve]

/-- The Picard operator, as a plain function; it is packaged as a self-map of `ℝ →ᵇ E` below. -/
private noncomputable def picardMap (v : E → E) (k : ℝ) (x : E) (u : ℝ →ᵇ E) (t : ℝ) : E :=
  (Real.cosh (2 * k * t))⁻¹ • ∫ s in (0 : ℝ)..t, v (picardCurve k x u s)

private theorem continuous_picardMap {v : E → E} (hvc : Continuous v) (k : ℝ) (x : E)
    (u : ℝ →ᵇ E) : Continuous (picardMap v k x u) := by
  have hcomp : Continuous fun s ↦ v (picardCurve k x u s) :=
    hvc.comp (continuous_picardCurve k x u)
  have hint : Continuous fun t : ℝ ↦ ∫ s in (0 : ℝ)..t, v (picardCurve k x u s) :=
    intervalIntegral.continuous_primitive (fun a b ↦ hcomp.intervalIntegrable a b) 0
  have hinv : Continuous fun t : ℝ ↦ (Real.cosh (2 * k * t))⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun t ↦ (Real.cosh_pos _).ne'
  exact hinv.smul hint

private theorem norm_picardMap_le {v : E → E} {k : ℝ} (hk : 0 < k)
    (hv : ∀ y z, ‖v y - v z‖ ≤ k * ‖y - z‖) (x : E) (u : ℝ →ᵇ E) (t : ℝ) :
    ‖picardMap v k x u t‖ ≤ (‖v x‖ + k * ‖u‖) / (2 * k) := by
  have hCnn : (0 : ℝ) ≤ ‖v x‖ + k * ‖u‖ := by positivity
  have hbound : ∀ s : ℝ,
      ‖v (picardCurve k x u s)‖ ≤ (‖v x‖ + k * ‖u‖) * Real.cosh (2 * k * s) := by
    intro s
    have h1 : ‖v (picardCurve k x u s) - v x‖ ≤ k * (Real.cosh (2 * k * s) * ‖u‖) :=
      (hv _ _).trans
        (mul_le_mul_of_nonneg_left (norm_picardCurve_sub_le k x u s) hk.le)
    have h2 := norm_sub_norm_le (v (picardCurve k x u s)) (v x)
    have h3 : (1 : ℝ) ≤ Real.cosh (2 * k * s) := Real.one_le_cosh _
    nlinarith [norm_nonneg (v x), norm_nonneg u, hk.le, mul_nonneg hk.le (norm_nonneg u)]
  have hstep : ‖∫ s in (0 : ℝ)..t, v (picardCurve k x u s)‖ ≤
      (‖v x‖ + k * ‖u‖) * Real.cosh (2 * k * t) / (2 * k) :=
    norm_integral_le_cosh hk hCnn hbound t
  have hcosh : (0 : ℝ) < Real.cosh (2 * k * t) := Real.cosh_pos _
  rw [picardMap, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcosh)]
  rw [inv_mul_le_iff₀ hcosh]
  refine hstep.trans_eq ?_
  field_simp

/-- The Picard operator attached to `v`, the initial point `x` and the weight `cosh (2 k ·)`. -/
private noncomputable def picardOp {v : E → E} (hvc : Continuous v) {k : ℝ} (hk : 0 < k)
    (hv : ∀ y z, ‖v y - v z‖ ≤ k * ‖y - z‖) (x : E) (u : ℝ →ᵇ E) : ℝ →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (picardMap v k x u)
    (continuous_picardMap hvc k x u) _ (norm_picardMap_le hk hv x u)

private theorem picardOp_apply {v : E → E} (hvc : Continuous v) {k : ℝ} (hk : 0 < k)
    (hv : ∀ y z, ‖v y - v z‖ ≤ k * ‖y - z‖) (x : E) (u : ℝ →ᵇ E) (t : ℝ) :
    picardOp hvc hk hv x u t = picardMap v k x u t := rfl

/-- The single estimate behind both contraction properties of the Picard operator: a bound on the
carried curves, in the weight `cosh (2 k ·)`, halves to a bound on the values of the operator. -/
private theorem dist_picardOp_le {v : E → E} (hvc : Continuous v) {k : ℝ} (hk : 0 < k)
    (hv : ∀ y z, ‖v y - v z‖ ≤ k * ‖y - z‖) {x y : E} {u₁ u₂ : ℝ →ᵇ E} {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ s, ‖picardCurve k x u₁ s - picardCurve k y u₂ s‖ ≤ D * Real.cosh (2 * k * s)) :
    dist (picardOp hvc hk hv x u₁) (picardOp hvc hk hv y u₂) ≤ D / 2 := by
  rw [BoundedContinuousFunction.dist_le (by linarith)]
  intro t
  have hcosh : (0 : ℝ) < Real.cosh (2 * k * t) := Real.cosh_pos _
  have hi₁ : ∀ a b : ℝ, IntervalIntegrable (fun s ↦ v (picardCurve k x u₁ s)) volume a b :=
    fun a b ↦ (hvc.comp (continuous_picardCurve k x u₁)).intervalIntegrable a b
  have hi₂ : ∀ a b : ℝ, IntervalIntegrable (fun s ↦ v (picardCurve k y u₂ s)) volume a b :=
    fun a b ↦ (hvc.comp (continuous_picardCurve k y u₂)).intervalIntegrable a b
  have hbound : ∀ s : ℝ, ‖v (picardCurve k x u₁ s) - v (picardCurve k y u₂ s)‖ ≤
      k * D * Real.cosh (2 * k * s) := by
    intro s
    refine (hv _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb s) hk.le
  have hsub : ∫ s in (0 : ℝ)..t, (v (picardCurve k x u₁ s) - v (picardCurve k y u₂ s)) =
      (∫ s in (0 : ℝ)..t, v (picardCurve k x u₁ s)) -
        ∫ s in (0 : ℝ)..t, v (picardCurve k y u₂ s) :=
    intervalIntegral.integral_sub (hi₁ 0 t) (hi₂ 0 t)
  have hint := norm_integral_le_cosh (F := fun s ↦
    v (picardCurve k x u₁ s) - v (picardCurve k y u₂ s)) hk (mul_nonneg hk.le hD) hbound t
  rw [hsub] at hint
  rw [dist_eq_norm, picardOp_apply, picardOp_apply, picardMap, picardMap, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcosh), inv_mul_le_iff₀ hcosh]
  refine hint.trans_eq ?_
  field_simp

/-- The Picard operator halves distances, uniformly in the initial point. -/
private theorem contractingWith_picardOp {v : E → E} (hvc : Continuous v) {k : ℝ} (hk : 0 < k)
    (hv : ∀ y z, ‖v y - v z‖ ≤ k * ‖y - z‖) (x : E) :
    ContractingWith (1 / 2 : ℝ≥0) (picardOp hvc hk hv x) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun u₁ u₂ ↦ ?_⟩
  have hcast : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  rw [hcast]
  refine (dist_picardOp_le hvc hk hv dist_nonneg fun s ↦ ?_).trans_eq (by ring)
  rw [picardCurve_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _),
    mul_comm (dist u₁ u₂)]
  gcongr
  rw [← dist_eq_norm]
  exact u₁.dist_coe_le_dist s

variable [CompleteSpace E]

/-- The fixed point of the Picard operator. -/
private noncomputable def picardFixedPoint {v : E → E} (hvc : Continuous v) {k : ℝ} (hk : 0 < k)
    (hv : ∀ y z, ‖v y - v z‖ ≤ k * ‖y - z‖) (x : E) : ℝ →ᵇ E :=
  ContractingWith.fixedPoint _ (contractingWith_picardOp hvc hk hv x)

/-- The curve attached to the Picard fixed point satisfies the integral equation. -/
private theorem picardCurve_fixedPoint {v : E → E} (hvc : Continuous v) {k : ℝ} (hk : 0 < k)
    (hv : ∀ y z, ‖v y - v z‖ ≤ k * ‖y - z‖) (x : E) (t : ℝ) :
    picardCurve k x (picardFixedPoint hvc hk hv x) t =
      x + ∫ s in (0 : ℝ)..t, v (picardCurve k x (picardFixedPoint hvc hk hv x) s) := by
  have hfix : picardOp hvc hk hv x (picardFixedPoint hvc hk hv x) =
      picardFixedPoint hvc hk hv x :=
    ContractingWith.fixedPoint_isFixedPt _
  have hpt := congrArg (fun w : ℝ →ᵇ E ↦ w t) hfix
  simp only [picardOp_apply, picardMap] at hpt
  rw [picardCurve, ← hpt, smul_inv_smul₀ (Real.cosh_pos (2 * k * t)).ne']

private theorem k_pos (K : ℝ≥0) : (0 : ℝ) < (K : ℝ) + 1 := by positivity

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem norm_sub_le_of_lipschitzWith {v : E → E} {K : ℝ≥0} (hv : LipschitzWith K v)
    (y z : E) : ‖v y - v z‖ ≤ ((K : ℝ) + 1) * ‖y - z‖ := by
  have h := hv.dist_le_mul y z
  rw [dist_eq_norm, dist_eq_norm] at h
  nlinarith [norm_nonneg (y - z)]

/-- **The global solution of a globally Lipschitz autonomous ODE.** For a Lipschitz vector field
`v` on a Banach space, `ODE.globalSolution v hv x` is the unique curve `γ : ℝ → E` defined on the
whole line with `γ 0 = x` and `γ' t = v (γ t)` for every `t`. -/
noncomputable def globalSolution (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) : ℝ → E :=
  picardCurve ((K : ℝ) + 1) x
    (picardFixedPoint hv.continuous (k_pos K) (norm_sub_le_of_lipschitzWith hv) x)

/-- The global solution satisfies the integral equation of the initial value problem. -/
theorem globalSolution_eq_integral (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) (t : ℝ) :
    globalSolution v hv x t = x + ∫ s in (0 : ℝ)..t, v (globalSolution v hv x s) :=
  picardCurve_fixedPoint _ _ _ x t

/-- The global solution starts at the prescribed initial point. -/
@[simp]
theorem globalSolution_zero (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) :
    globalSolution v hv x 0 = x := by
  simpa using globalSolution_eq_integral v hv x 0

/-- The global solution is continuous. -/
theorem continuous_globalSolution_apply (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) :
    Continuous (globalSolution v hv x) :=
  continuous_picardCurve _ _ _

/-- **The global solution solves the differential equation** at every time. -/
theorem hasDerivAt_globalSolution (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) (t : ℝ) :
    HasDerivAt (globalSolution v hv x) (v (globalSolution v hv x t)) t := by
  have hcomp : Continuous fun s ↦ v (globalSolution v hv x s) :=
    hv.continuous.comp (continuous_globalSolution_apply v hv x)
  have hprim : HasDerivAt (fun r : ℝ ↦ ∫ s in (0 : ℝ)..r, v (globalSolution v hv x s))
      (v (globalSolution v hv x t)) t :=
    intervalIntegral.integral_hasDerivAt_right (hcomp.intervalIntegrable _ _)
      (hcomp.stronglyMeasurableAtFilter _ _) hcomp.continuousAt
  exact (hprim.const_add x).congr_of_eventuallyEq
    (.of_forall fun r ↦ globalSolution_eq_integral v hv x r)

/-- The global solution is an integral curve of `v`, read as a time-independent vector field. -/
theorem isIntegralCurve_globalSolution (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) :
    IsIntegralCurve (globalSolution v hv x) fun _ y ↦ v y :=
  hasDerivAt_globalSolution v hv x

/-- **Uniqueness.** Any curve defined on the whole line that solves `γ' = v ∘ γ` is the global
solution through its own initial value. -/
theorem eq_globalSolution (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) : γ = globalSolution v hv (γ 0) :=
  ODE_solution_unique_univ (v := fun _ y ↦ v y) (s := fun _ ↦ univ) (t₀ := 0)
    (fun _ ↦ hv.lipschitzOnWith) (fun t ↦ ⟨hγ t, trivial⟩)
    (fun t ↦ ⟨hasDerivAt_globalSolution v hv (γ 0) t, trivial⟩)
    (by rw [globalSolution_zero])

/-- **Independence of the Lipschitz bound.** Two Lipschitz witnesses for the same vector field,
with possibly different constants, produce the same global solution. -/
theorem globalSolution_congr (v : E → E) {K K' : ℝ≥0} (hv : LipschitzWith K v)
    (hv' : LipschitzWith K' v) (x : E) : globalSolution v hv x = globalSolution v hv' x := by
  have h := eq_globalSolution v hv' (γ := globalSolution v hv x) (hasDerivAt_globalSolution v hv x)
  rwa [globalSolution_zero] at h

/-- The Picard fixed point depends on the initial condition `1`-Lipschitzly. -/
private theorem dist_picardFixedPoint_le {v : E → E} (hvc : Continuous v) {k : ℝ} (hk : 0 < k)
    (hv : ∀ y z, ‖v y - v z‖ ≤ k * ‖y - z‖) (x y : E) :
    dist (picardFixedPoint hvc hk hv x) (picardFixedPoint hvc hk hv y) ≤ ‖x - y‖ := by
  have hC : ∀ u : ℝ →ᵇ E,
      dist (picardOp hvc hk hv x u) (picardOp hvc hk hv y u) ≤ ‖x - y‖ / 2 := fun u ↦
    dist_picardOp_le hvc hk hv (norm_nonneg _) fun s ↦ by
      rw [picardCurve_sub_const]
      exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_cosh _)
  have h := ContractingWith.fixedPoint_lipschitz_in_map (contractingWith_picardOp hvc hk hv x)
    (contractingWith_picardOp hvc hk hv y) hC
  have hcast : (1 : ℝ) - ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  rw [hcast] at h
  simpa [picardFixedPoint] using h.trans_eq (by ring)

/-- **Reversing time** turns the global solution of `v` into the global solution of `-v`. -/
theorem globalSolution_neg (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x : E) (t : ℝ) :
    globalSolution v hv x (-t) = globalSolution (fun z ↦ -v z) hv.neg x t := by
  have hγ : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ globalSolution v hv x (-s))
      (-v (globalSolution v hv x (-s))) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ ↦ -s) (-1 : ℝ) s := by simpa using hasDerivAt_neg s
    simpa [Function.comp_def] using (hasDerivAt_globalSolution v hv x (-s)).scomp s h1
  simpa using congrFun (eq_globalSolution (fun z ↦ -v z) hv.neg hγ) t

private theorem dist_globalSolution_le_of_nonneg (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v)
    (x y : E) {t : ℝ} (ht : 0 ≤ t) :
    dist (globalSolution v hv x t) (globalSolution v hv y t) ≤ dist x y * Real.exp (K * t) := by
  have h := dist_le_of_trajectories_ODE (v := fun _ z ↦ v z) (K := K) (a := 0) (b := t)
    (f := globalSolution v hv x) (g := globalSolution v hv y) (δ := dist x y)
    (fun _ ↦ hv) (continuous_globalSolution_apply v hv x).continuousOn
    (fun s _ ↦ (hasDerivAt_globalSolution v hv x s).hasDerivWithinAt)
    (continuous_globalSolution_apply v hv y).continuousOn
    (fun s _ ↦ (hasDerivAt_globalSolution v hv y s).hasDerivWithinAt)
    (by simp) t (by simp [ht])
  simpa using h

/-- **Continuous dependence on the initial condition.** Two global solutions drift apart at most
exponentially, at the rate given by the Lipschitz constant of the vector field, in both time
directions. -/
theorem dist_globalSolution_le (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) (x y : E) (t : ℝ) :
    dist (globalSolution v hv x t) (globalSolution v hv y t) ≤ dist x y * Real.exp (K * |t|) := by
  rcases le_total 0 t with ht | ht
  · simpa [abs_of_nonneg ht] using dist_globalSolution_le_of_nonneg v hv x y ht
  · have h := dist_globalSolution_le_of_nonneg (fun z ↦ -v z) hv.neg x y
      (t := -t) (by linarith)
    rw [← globalSolution_neg, ← globalSolution_neg] at h
    simpa [abs_of_nonpos ht] using h

/-- **Joint continuity** of the global solution in time and initial condition. -/
theorem continuous_globalSolution (v : E → E) {K : ℝ≥0} (hv : LipschitzWith K v) :
    Continuous fun p : ℝ × E ↦ globalSolution v hv p.2 p.1 := by
  have hΦ : Continuous fun x : E ↦
      picardFixedPoint hv.continuous (k_pos K) (norm_sub_le_of_lipschitzWith hv) x := by
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y ↦ ?_)
    simpa [dist_eq_norm] using dist_picardFixedPoint_le hv.continuous (k_pos K)
      (norm_sub_le_of_lipschitzWith hv) x y
  have heval : Continuous fun p : ℝ × E ↦
      (picardFixedPoint hv.continuous (k_pos K) (norm_sub_le_of_lipschitzWith hv) p.2) p.1 :=
    (hΦ.comp continuous_snd).eval continuous_fst
  have hcosh : Continuous fun p : ℝ × E ↦ Real.cosh (2 * ((K : ℝ) + 1) * p.1) := by fun_prop
  have hmain : Continuous fun p : ℝ × E ↦
      p.2 + Real.cosh (2 * ((K : ℝ) + 1) * p.1) •
        (picardFixedPoint hv.continuous (k_pos K) (norm_sub_le_of_lipschitzWith hv) p.2) p.1 :=
    continuous_snd.add (hcosh.smul heval)
  simpa [globalSolution, picardCurve] using hmain

end ODE
