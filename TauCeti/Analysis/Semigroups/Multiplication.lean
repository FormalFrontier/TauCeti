/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.GrowthBound
public import TauCeti.Analysis.Semigroups.Generator.Basic
public import TauCeti.Analysis.Semigroups.Resolvent.Identity
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.SpecialFunctions.Exponential

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.MeasureTheory.Integral.ExpDecay

/-!
# The multiplication semigroup on bounded continuous functions

For a bounded continuous multiplier `m : α →ᵇ ℝ` this file constructs the **multiplication
semigroup** on the Banach space `α →ᵇ ℝ` of bounded continuous real functions:

`S(t) f = e^{-t·m} · f`, acting by pointwise multiplication.

This is the remaining concrete acceptance example for Part A of the one-parameter-semigroups
roadmap, alongside the bounded-operator semigroup `StronglyContinuousSemigroup.ofBounded`
(`TauCeti/Analysis/Semigroups/BoundedGenerator/Basic.lean`).  We develop:

* `StronglyContinuousSemigroup.ofMultiplication m`: the C₀-semigroup `t ↦ multiplication by`
  `e^{-t·m}`, with growth bound `(‖m‖, 1)`;
* its generator: the domain is the whole space and the generator is multiplication by `-m`
  (`ofMultiplication_domain_eq_top`, `ofMultiplication_generator`);
* its resolvent: for `‖m‖ < λ` the Laplace-transform resolvent acts as multiplication by the
  pointwise inverse `(λ + m)⁻¹` (`ofMultiplication_resolvent_eq`), which identifies it with the
  resolvent of the generator through the bridge lemma `generator_resolvent_eq`
  (`ofMultiplication_generator_resolvent_eq`);
* `ContractionSemigroup.ofMultiplication`: when `0 ≤ m` the semigroup is contractive, so the
  abstract bound `‖R(λ)‖ ≤ 1/λ` applies to it concretely.

## References
The multiplication semigroup is the standard first example of a C₀-semigroup; see Engel--Nagel,
*One-Parameter Semigroups for Linear Evolution Equations*, Ch. I, and Pazy, *Semigroups of
Linear Operators*, Ch. 1.
-/

public section

noncomputable section

open scoped NNReal Topology BoundedContinuousFunction

namespace TauCeti.Semigroups

variable {α : Type*} [TopologicalSpace α]

/-! ## One-off exponential estimates

Elementary second-order bounds for `Real.exp`, used to control difference quotients uniformly
over the range of a bounded continuous multiplier. -/

/-- Chain rule specialization: the derivative of `w ↦ exp (-w)` is `-exp (-w)`. -/
private theorem hasDerivAt_exp_neg (u : ℝ) :
    HasDerivAt (fun w : ℝ => Real.exp (-w)) (-(Real.exp (-u))) u :=
  (HasDerivAt.comp (x := u) (Real.hasDerivAt_exp (-u)) ((hasDerivAt_id u).neg)).congr_deriv (by
    ring)

/-- The derivative of the auxiliary function `w ↦ w²/2 - exp (-w) - w + 1`. -/
private theorem deriv_aux_sub (r : ℝ) :
    deriv (fun w : ℝ => w ^ 2 / 2 - Real.exp (-w) - w + 1) r = r + Real.exp (-r) - 1 := by
  have d2 : DifferentiableAt ℝ (fun w : ℝ => w ^ 2 / 2) r := by fun_prop
  have dn : DifferentiableAt ℝ (fun w : ℝ => Real.exp (-w)) r := by fun_prop
  have dc : DifferentiableAt ℝ (fun _ : ℝ => (1:ℝ)) r := by fun_prop
  have dm := (d2.sub dn).sub (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => w) r)
  change deriv ((((fun w : ℝ => w ^ 2 / 2) - fun w : ℝ => Real.exp (-w)) - fun w : ℝ => w)
      + fun _ : ℝ => (1:ℝ)) r = _
  rw [deriv_add dm dc,
    deriv_sub ((d2.sub dn)) (by fun_prop : DifferentiableAt ℝ (fun w : ℝ => w) r),
    deriv_sub d2 dn, (hasDerivAt_exp_neg r).deriv,
    show deriv (fun w : ℝ => w) r = 1 from by simp, deriv_const]
  have hpow2 : deriv (fun w : ℝ => w ^ 2 / 2) r = r := by
    have hv := ((hasDerivAt_pow 2 r).div_const 2).deriv
    linarith [show r ^ (2 - 1) = r from by norm_num]
  rw [hpow2]
  ring

/-- For `s ≥ 0`, `exp (-s) - 1 + s` lies between `0` and `s²/2`. -/
private theorem abs_exp_neg_sub_one_add_self_le {s : ℝ} (hs : 0 ≤ s) :
    |Real.exp (-s) - 1 + s| ≤ s ^ 2 / 2 := by
  have hpos : 0 ≤ Real.exp (-s) - 1 + s := by linarith [Real.add_one_le_exp (-s)]
  calc |Real.exp (-s) - 1 + s| = Real.exp (-s) - 1 + s := abs_of_nonneg hpos
    _ ≤ s ^ 2 / 2 := by
        -- `q r = r²/2 - exp(-r) - r + 1` satisfies `q 0 = 0` and
        -- `q' r = r + exp(-r) - 1 ≥ 0`, hence is nonnegative on `[0, ∞)`.
        have hmono : MonotoneOn (fun w : ℝ => w ^ 2 / 2 - Real.exp (-w) - w + 1)
            (Set.Ici 0) := by
          refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) ?_ ?_ ?_
          · intro x _
            fun_prop
          · intro x _
            fun_prop
          · intro x hx
            rw [interior_Ici] at hx
            rw [deriv_aux_sub x]
            have h := Real.add_one_le_exp (-x)
            linarith
        have hq := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
        norm_num at hq
        linarith

/-- For `s ≥ 0`, `exp s - 1 - s` is at most `s²/2 · exp s`. -/
private theorem exp_sub_one_sub_self_le_sq_div_two_mul_exp {s : ℝ} (hs : 0 ≤ s) :
    Real.exp s - 1 - s ≤ s ^ 2 / 2 * Real.exp s := by
  -- `g r = r²/2 + (r+1)·exp(-r) - 1` satisfies `g 0 = 0` and `g' r = r·(1 - exp(-r)) ≥ 0`.
  have hmono : MonotoneOn (fun w : ℝ => w ^ 2 / 2 + (w + 1) * Real.exp (-w) - 1) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) ?_ ?_ ?_
    · intro x _
      fun_prop
    · intro x _
      fun_prop
    · intro x hx
      rw [interior_Ici] at hx
      have d2 : DifferentiableAt ℝ (fun w : ℝ => w ^ 2 / 2) x := by fun_prop
      have dp : DifferentiableAt ℝ (fun w : ℝ => (w + 1) * Real.exp (-w)) x := by fun_prop
      have dc : DifferentiableAt ℝ (fun _ : ℝ => (1:ℝ)) x := by fun_prop
      have dia : DifferentiableAt ℝ (fun w : ℝ => w + 1) x := by fun_prop
      have de : DifferentiableAt ℝ (fun w : ℝ => Real.exp (-w)) x := by fun_prop
      have dpv : deriv (fun w : ℝ => (w + 1) * Real.exp (-w)) x
          = Real.exp (-x) + (x + 1) * -(Real.exp (-x)) := by
        change deriv (((fun w : ℝ => w + 1)) * fun w : ℝ => Real.exp (-w)) x = _
        rw [deriv_mul dia de,
          show deriv (fun w : ℝ => w + 1) x = 1 from by simp,
          (hasDerivAt_exp_neg x).deriv]
        ring
      have d2v : deriv (fun w : ℝ => w ^ 2 / 2) x = x := by
        have heq : (fun w : ℝ => w ^ 2 / 2) = fun w : ℝ => (1 / 2) * w ^ 2 := by
          funext w; ring
        rw [heq, deriv_const_mul_field (u := 1 / 2)]
        norm_num
        ring
      change 0 ≤ deriv (((fun w : ℝ => w ^ 2 / 2) + fun w : ℝ => (w + 1) * Real.exp (-w))
          - fun _ : ℝ => (1:ℝ)) x
      rw [deriv_sub (d2.add dp) dc, deriv_add d2 dp, dpv, d2v, deriv_const, sub_zero]
      have hx0 : 0 < x := hx
      have hle1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      rw [show x + (Real.exp (-x) + (x + 1) * -(Real.exp (-x)))
            = x * (1 - Real.exp (-x)) from by ring]
      exact mul_nonneg hx0.le (by linarith)
  have hq := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs) hs
  norm_num at hq
  -- `s²/2 + (s+1)e^{-s} ≥ 1`; multiply by `e^s > 0`.
  have hpos : (0 : ℝ) < Real.exp s := Real.exp_pos s
  have h1 : 1 - (s + 1) * Real.exp (-s) ≤ s ^ 2 / 2 := by linarith
  have hE : Real.exp (-s) * Real.exp s = 1 := by
    rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero s)]
  calc Real.exp s - 1 - s = Real.exp s - (s + 1) * 1 := by ring
    _ = Real.exp s - (s + 1) * (Real.exp (-s) * Real.exp s) := by rw [hE]
    _ = (1 - (s + 1) * Real.exp (-s)) * Real.exp s := by
        rw [mul_sub_right_distrib, mul_assoc, hE]
        ring
    _ ≤ s ^ 2 / 2 * Real.exp s := mul_le_mul_of_nonneg_right h1 hpos.le

/-- `|exp w - 1| ≤ |w| · exp |w|` for every real `w`. -/
private theorem abs_exp_sub_one_le_abs_mul_exp_abs (w : ℝ) :
    |Real.exp w - 1| ≤ |w| * Real.exp |w| := by
  rcases le_or_gt 0 w with hw | hw
  · -- from the tangent line `exp (-w) ≥ 1 - w`, multiplied by `exp w`
    have hm : (1 - w) * Real.exp w ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-w)) (Real.exp_nonneg w)
      rw [show (-w + 1 : ℝ) = 1 - w from by ring, Real.exp_neg,
        inv_mul_cancel₀ (Real.exp_ne_zero w)] at h
      exact h
    have hkey : Real.exp w - w * Real.exp w ≤ 1 := by linarith [hm]
    have h2 : Real.exp w - 1 ≤ w * Real.exp w := by linarith
    rw [abs_of_nonneg (a := Real.exp w - 1) (by linarith [Real.add_one_le_exp w]),
      abs_of_nonneg hw]
    exact h2
  · have hle : Real.exp w ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : w + 1 ≤ Real.exp w := Real.add_one_le_exp w
    have h3 : 1 ≤ Real.exp |w| := Real.one_le_exp (abs_nonneg w)
    rw [abs_of_nonpos (a := Real.exp w - 1) (by linarith)]
    have key1 : -(Real.exp w - 1) ≤ -w := by linarith
    have key3 : |w| ≤ |w| * Real.exp |w| := by
      have h4 := mul_le_mul_of_nonneg_left h3 (abs_nonneg w)
      rwa [mul_one] at h4
    calc -(Real.exp w - 1) ≤ -w := key1
      _ = |w| := (abs_of_neg hw).symm
      _ ≤ |w| * Real.exp |w| := key3

/-- The second-order bound in the form used for difference quotients:
`|exp (-u) - 1 + u| ≤ u²/2 · exp |u|`. -/
private theorem abs_exp_neg_sub_one_add_self_le_sq_mul_exp_abs (u : ℝ) :
    |Real.exp (-u) - 1 + u| ≤ u ^ 2 / 2 * Real.exp |u| := by
  have hxpos : 0 ≤ Real.exp (-u) - 1 + u := by
    have h := Real.add_one_le_exp (-u)
    linarith
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hxpos, abs_of_nonneg hu]
    have hb : u ^ 2 / 2 ≤ u ^ 2 / 2 * 1 := le_of_eq (mul_one _).symm
    refine le_trans (le_trans (le_abs_self _) (abs_exp_neg_sub_one_add_self_le hu))
      (le_trans hb (mul_le_mul_of_nonneg_left (Real.one_le_exp hu)
        (by positivity)))
  · rw [abs_of_nonneg hxpos]
    have hv : 0 < -u := by linarith
    have h2 := exp_sub_one_sub_self_le_sq_div_two_mul_exp (le_of_lt hv)
    rw [neg_sq] at h2
    calc Real.exp (-u) - 1 + u
        = Real.exp (-u) - 1 - -u := by ring
      _ ≤ u ^ 2 / 2 * Real.exp (-u) := h2
      _ ≤ u ^ 2 / 2 * Real.exp |u| := by rw [abs_of_neg hu]

/-! ## The exponential multiplier -/

/-- The exponential multiplier `x ↦ exp (-t · m x)` as a bounded continuous function. -/
def expNegMulBcf (t : ℝ) (m : α →ᵇ ℝ) : α →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => Real.exp (-(t * m x)))
    (by fun_prop) (Real.exp (|t| * ‖m‖)) fun x => by
      have hx : |m x| ≤ ‖m‖ := m.norm_coe_le_norm x
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      refine Real.exp_le_exp.mpr (le_trans (le_abs_self _) ?_)
      rw [abs_neg, abs_mul]
      exact mul_le_mul_of_nonneg_left hx (abs_nonneg t)

@[simp]
theorem coe_expNegMulBcf (t : ℝ) (m : α →ᵇ ℝ) :
    ⇑(expNegMulBcf t m) = fun x => Real.exp (-(t * m x)) :=
  BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _

theorem norm_expNegMulBcf_le (t : ℝ) (m : α →ᵇ ℝ) :
    ‖expNegMulBcf t m‖ ≤ Real.exp (|t| * ‖m‖) := by
  refine (BoundedContinuousFunction.norm_le (Real.exp_nonneg _)).mpr fun x => ?_
  have hx : |m x| ≤ ‖m‖ := m.norm_coe_le_norm x
  have hv1 : ‖expNegMulBcf t m x‖ = Real.exp (-(t * m x)) := by
    simp only [coe_expNegMulBcf, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  have hd2 : Real.exp (|t| * |m x|) ≤ Real.exp (|t| * ‖m‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx (abs_nonneg t))
  rw [hv1]
  have h2 : Real.exp (-(t * m x)) ≤ Real.exp (|t| * |m x|) :=
    Real.exp_le_exp.mpr (by
      have h4 := le_abs_self (-(t * m x))
      rw [abs_neg, abs_mul] at h4
      exact h4)
  exact le_trans h2 hd2

/-- Uniform second-order control of the difference quotients of the exponential multiplier:
`(exp (-t·m) - 1) / t` differs from `-m` by at most `t/2 · ‖m‖² · e^{t‖m‖}` in sup norm. -/
private theorem norm_quot_expNegMulBcf_add_le (m : α →ᵇ ℝ) {t : ℝ} (ht : 0 < t) :
    ‖(1 / t) • (expNegMulBcf t m - 1) + m‖ ≤ t / 2 * ‖m‖ ^ 2 * Real.exp (t * ‖m‖) := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun x => ?_
  have hkey := abs_exp_neg_sub_one_add_self_le_sq_mul_exp_abs (t * m x)
  have hx : |m x| ≤ ‖m‖ := m.norm_coe_le_norm x
  have he3 : Real.exp (t * |m x|) ≤ Real.exp (t * ‖m‖) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx ht.le)
  have he2 : (m x) ^ 2 ≤ ‖m‖ ^ 2 := by
    nlinarith [sq_abs (m x), hx, abs_nonneg (m x)]
  have harg : (Real.exp (-(t * m x)) - 1) / t + m x
      = (Real.exp (-(t * m x)) - 1 + t * m x) / t := by
    field_simp
  have hx2 : |(1 / t) • (expNegMulBcf t m - 1) x + m x|
      = |(Real.exp (-(t * m x)) - 1) / t + m x| := by
    congr 1
    simp [coe_expNegMulBcf]
    ring
  have hkey' : |Real.exp (-(t * m x)) - 1 + t * m x|
      ≤ (t * m x) ^ 2 / 2 * Real.exp (t * |m x|) := by
    rw [abs_mul, abs_of_pos ht] at hkey
    exact hkey
  have hstep2 : (t * m x) ^ 2 / 2 * Real.exp (t * |m x|) / t
      = t / 2 * (m x) ^ 2 * Real.exp (t * |m x|) := by
    field_simp
  calc |(1 / t) • (expNegMulBcf t m - 1) x + m x|
      = |(Real.exp (-(t * m x)) - 1) / t + m x| := hx2
    _ = |Real.exp (-(t * m x)) - 1 + t * m x| / t := by
        rw [harg, abs_div, abs_of_pos ht]
    _ ≤ (t * m x) ^ 2 / 2 * Real.exp (t * |m x|) / t :=
        div_le_div_of_nonneg_right hkey' ht.le
    _ = t / 2 * (m x) ^ 2 * Real.exp (t * |m x|) := hstep2
    _ ≤ t / 2 * ‖m‖ ^ 2 * Real.exp (t * ‖m‖) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left he2 (by positivity)) he3
          (Real.exp_nonneg _) (by positivity)

/-- Uniform control of the exponential multiplier near zero time. -/
private theorem norm_expNegMulBcf_sub_one_le {m : α →ᵇ ℝ} {t : ℝ} (ht : 0 ≤ t) :
    ‖expNegMulBcf t m - 1‖ ≤ t * ‖m‖ * Real.exp (t * ‖m‖) := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun x => ?_
  have hkey := abs_exp_sub_one_le_abs_mul_exp_abs (-(t * m x))
  rw [abs_neg] at hkey
  have hx : |m x| ≤ ‖m‖ := m.norm_coe_le_norm x
  have hfac : |t * m x| ≤ t * ‖m‖ := by
    rw [abs_mul, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left hx ht
  have hd : Real.exp (|t * m x|) ≤ Real.exp (t * ‖m‖) := by
    refine Real.exp_le_exp.mpr ?_
    rw [abs_mul, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left hx ht
  calc ‖expNegMulBcf t m x - 1‖ = |Real.exp (-(t * m x)) - 1| := by
        rw [Real.norm_eq_abs]; congr 1
    _ ≤ |t * m x| * Real.exp (|t * m x|) := hkey
    _ ≤ t * ‖m‖ * Real.exp (t * ‖m‖) := mul_le_mul hfac hd
          (Real.exp_nonneg _) (mul_nonneg ht (norm_nonneg _))

/-! ## The multiplication semigroup -/

/-- **The multiplication semigroup**: for a bounded continuous multiplier `m`, the C₀-semigroup
on the Banach space `α →ᵇ ℝ` acting by pointwise multiplication with `exp (-t·m)`,
that is `S(t) f = e^{-t·m} · f`.  Its generator is multiplication by `-m`
(`ofMultiplication_generator`), and for `λ > ‖m‖` its resolvent acts as multiplication by the
pointwise inverse `(λ + m)⁻¹` (`ofMultiplication_resolvent_eq`). -/
def StronglyContinuousSemigroup.ofMultiplication (m : α →ᵇ ℝ) :
    StronglyContinuousSemigroup (α →ᵇ ℝ) where
  toFun t := ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (expNegMulBcf (t : ℝ) m)
  map_zero' := by
    refine ContinuousLinearMap.ext fun f => BoundedContinuousFunction.ext fun x => ?_
    simp only [NNReal.coe_zero, ContinuousLinearMap.mul_apply',
      BoundedContinuousFunction.mul_apply, coe_expNegMulBcf]
    norm_num
  map_add' s t := by
    refine ContinuousLinearMap.ext fun f => BoundedContinuousFunction.ext fun x => ?_
    simp only [NNReal.coe_add, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_apply', BoundedContinuousFunction.mul_apply,
      coe_expNegMulBcf]
    rw [show -(((↑s + ↑t : ℝ)) * m x) = -(↑s * m x) + -(↑t * m x) from by ring,
      ← mul_assoc, ← Real.exp_add]
  continuousAt_zero' f := by
    have h0f : ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (expNegMulBcf (0 : ℝ) m) f = f := by
      ext x; simp
    have key : ∀ t : ℝ≥0,
        dist (ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (expNegMulBcf (t : ℝ) m) f)
          (ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (expNegMulBcf (0 : ℝ) m) f)
          ≤ (t : ℝ) * ‖m‖ * Real.exp ((t : ℝ) * ‖m‖) * ‖f‖ := by
      intro t
      have h1 : ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (expNegMulBcf (t : ℝ) m) f - f
          = ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (expNegMulBcf (t : ℝ) m - 1) f := by
        have hsub := map_sub (ContinuousLinearMap.mul ℝ (α →ᵇ ℝ))
          (expNegMulBcf (t : ℝ) m) (1 : α →ᵇ ℝ)
        rw [hsub]
        congr 1
        simp [one_mul]
      rw [h0f, dist_eq_norm, h1]
      calc ‖ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (expNegMulBcf (t : ℝ) m - 1) f‖
          ≤ ‖expNegMulBcf (t : ℝ) m - 1‖ * ‖f‖ := norm_mul_le _ _
        _ ≤ (t : ℝ) * ‖m‖ * Real.exp ((t : ℝ) * ‖m‖) * ‖f‖ :=
              mul_le_mul_of_nonneg_right (norm_expNegMulBcf_sub_one_le t.coe_nonneg)
                (norm_nonneg _)
    have hbdd : Filter.Tendsto
        (fun t : ℝ≥0 => (t : ℝ) * ‖m‖ * Real.exp ((t : ℝ) * ‖m‖) * ‖f‖)
        (nhds (0:ℝ≥0)) (nhds 0) := by
      have hcont : Continuous
          fun t : ℝ≥0 => (t : ℝ) * ‖m‖ * Real.exp ((t : ℝ) * ‖m‖) * ‖f‖ := by fun_prop
      have h0 : Filter.Tendsto
          (fun t : ℝ≥0 => (t : ℝ) * ‖m‖ * Real.exp ((t : ℝ) * ‖m‖) * ‖f‖)
          (nhds (0:ℝ≥0))
          (nhds ((((0:ℝ≥0) : ℝ) * ‖m‖ * Real.exp (((0:ℝ≥0) : ℝ) * ‖m‖)) * ‖f‖)) :=
        hcont.continuousAt.tendsto
      simpa using h0
    change Filter.Tendsto
      (fun t : ℝ≥0 => ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (expNegMulBcf (t : ℝ) m) f)
      (nhds (0:ℝ≥0))
      (nhds (ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (expNegMulBcf (0 : ℝ) m) f))
    refine (tendsto_iff_dist_tendsto_zero).mpr ?_
    exact squeeze_zero (fun _ => dist_nonneg) (fun t => key t) hbdd

@[simp]
theorem StronglyContinuousSemigroup.ofMultiplication_apply (m : α →ᵇ ℝ) (t : ℝ≥0)
    (f : α →ᵇ ℝ) : ofMultiplication m t f = expNegMulBcf (t : ℝ) m * f := by
  rw [show (ofMultiplication m) t = ContinuousLinearMap.mul ℝ (α →ᵇ ℝ)
    (expNegMulBcf (t : ℝ) m) from rfl]
  rfl

/-- Pointwise action of the multiplication semigroup: `(S(t) f)(x) = e^{-t·m x} · f(x)`. -/
theorem StronglyContinuousSemigroup.ofMultiplication_apply_apply (m : α →ᵇ ℝ) (t : ℝ≥0)
    (f : α →ᵇ ℝ) (x : α) : ofMultiplication m t f x = Real.exp (-((t : ℝ) * m x)) * f x := by
  simp only [ofMultiplication_apply]
  rfl

/-- The multiplication semigroup has growth bound `(‖m‖, 1)`. -/
theorem StronglyContinuousSemigroup.ofMultiplication_hasGrowthBound (m : α →ᵇ ℝ) :
    (ofMultiplication m).HasGrowthBound ‖m‖ 1 :=
  hasGrowthBound_of_bound le_rfl fun t ht => by
    have hu : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht
    have hroe : (ofMultiplication m).realOperator t
        = ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (expNegMulBcf t m) := by
      rw [← hu]
      exact realOperator_coe ..
    rw [hroe]
    refine le_trans (ContinuousLinearMap.opNorm_mul_apply_le ℝ _ _) ?_
    refine le_trans (norm_expNegMulBcf_le _ _) ?_
    rw [abs_of_nonneg ht, one_mul, mul_comm t ‖m‖]

/-! ## The generator -/

/-- Difference quotients of the orbits converge to multiplication by `-m`; this identifies
the generator in `ofMultiplication_generator`. -/
private theorem tendsto_quot_orbit_ofMultiplication (m : α →ᵇ ℝ) (f : α →ᵇ ℝ) :
    Filter.Tendsto
      (fun t : ℝ => (1 / t) •
        ((StronglyContinuousSemigroup.ofMultiplication m).realOperator t f - f))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (-m)) f)) := by
  have hsplit : ∀ t : ℝ, 0 < t →
      ((1 / t) • ((StronglyContinuousSemigroup.ofMultiplication m).realOperator t f - f)
          - (ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (-m)) f)
        = ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) ((1 / t) • (expNegMulBcf t m - 1) + m) f := by
    intro t ht
    rw [StronglyContinuousSemigroup.realOperator_def]
    refine BoundedContinuousFunction.ext fun x => ?_
    have hpt := StronglyContinuousSemigroup.ofMultiplication_apply_apply m
      (t.toNNReal : ℝ≥0) f x
    rw [Real.coe_toNNReal t ht.le] at hpt
    simp only [ContinuousLinearMap.mul_apply', BoundedContinuousFunction.mul_apply,
      BoundedContinuousFunction.coe_smul, BoundedContinuousFunction.coe_sub,
      BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_one,
      BoundedContinuousFunction.neg_apply, Pi.sub_apply, Pi.add_apply,
      Pi.one_apply, smul_eq_mul, coe_expNegMulBcf, hpt]
    ring
  refine (tendsto_iff_dist_tendsto_zero).mpr ?_
  have hbound : ∀ t : ℝ, 0 < t →
      dist
        ((fun t : ℝ => (1 / t) •
            ((StronglyContinuousSemigroup.ofMultiplication m).realOperator t f - f)) t)
        ((ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (-m)) f)
        ≤ (t / 2 * ‖m‖ ^ 2 * Real.exp (t * ‖m‖)) * ‖f‖ := by
    intro t ht
    rw [dist_eq_norm, hsplit t ht]
    calc ‖ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) ((1 / t) • (expNegMulBcf t m - 1) + m) f‖
        ≤ ‖(1 / t) • (expNegMulBcf t m - 1) + m‖ * ‖f‖ := norm_mul_le _ _
      _ ≤ (t / 2 * ‖m‖ ^ 2 * Real.exp (t * ‖m‖)) * ‖f‖ :=
            mul_le_mul_of_nonneg_right (norm_quot_expNegMulBcf_add_le m ht) (norm_nonneg _)
  have hcont : Continuous
      fun t : ℝ => (t / 2 * ‖m‖ ^ 2 * Real.exp (t * ‖m‖)) * ‖f‖ := by fun_prop
  have hz2 : ((0:ℝ) / 2 * ‖m‖ ^ 2 * Real.exp (0 * ‖m‖)) * ‖f‖ = 0 := by simp
  have h0 : Filter.Tendsto
      (fun t : ℝ => (t / 2 * ‖m‖ ^ 2 * Real.exp (t * ‖m‖)) * ‖f‖)
      (nhds 0) (nhds (((0:ℝ) / 2 * ‖m‖ ^ 2 * Real.exp (0 * ‖m‖)) * ‖f‖)) :=
    hcont.continuousAt.tendsto
  rw [hz2] at h0
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_
    (h0.mono_left inf_le_left)
  have hmem : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t ∈ Set.Ioi 0 :=
    eventually_mem_nhdsWithin
  exact hmem.mono fun t ht => hbound t (Set.mem_Ioi.mp ht)

/-- The multiplication semigroup has everywhere-defined generator: its domain is the whole
space. -/
theorem StronglyContinuousSemigroup.ofMultiplication_domain_eq_top (m : α →ᵇ ℝ) :
    (ofMultiplication m).domain = ⊤ ∧
      (ofMultiplication m).generator =
        (ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (-m)).toLinearMap.toPMap ⊤ :=
  generator_eq_toPMap_top_of_forall_tendsto _ _ (tendsto_quot_orbit_ofMultiplication m)

/-- The generator domain of the multiplication semigroup is the whole space. -/
theorem StronglyContinuousSemigroup.ofMultiplication_domain_eq_top' (m : α →ᵇ ℝ) :
    (ofMultiplication m).domain = ⊤ :=
  (ofMultiplication_domain_eq_top m).1

/-- **The generator of the multiplication semigroup** is multiplication by `-m`, on the whole
space. -/
theorem StronglyContinuousSemigroup.ofMultiplication_generator (m : α →ᵇ ℝ) :
    (ofMultiplication m).generator =
      (ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (-m)).toLinearMap.toPMap ⊤ :=
  (ofMultiplication_domain_eq_top m).2


/-! ## The concrete resolvent -/

/-- The basic Laplace integral: `∫₀^∞ e^{-a t} dt = a⁻¹` for `a > 0`. -/
private theorem integral_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ in Set.Ioi 0, Real.exp (-(a * t)) = a⁻¹ := by
  simpa [pow_zero, one_mul] using integral_pow_mul_exp_neg_mul_Ioi 0 ha

/-- Pointwise absolute-value bound for a bounded continuous function. -/
private theorem abs_norm_coe_le (f : α →ᵇ ℝ) (x : α) : |f x| ≤ ‖f‖ := by
  simpa using f.norm_coe_le_norm x

/-- The pointwise inverse `(c + m)⁻¹` of a positive perturbation of a bounded continuous
multiplier, as bounded continuous function.  The hypothesis `‖m‖ < c` guarantees
`c + m x ≥ c - ‖m‖ > 0` for every `x`. -/
def invAddBcf (c : ℝ) (m : α →ᵇ ℝ) (hc : ‖m‖ < c) : α →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (c + m x)⁻¹)
    (by
      refine Continuous.inv₀ (continuous_const.add m.continuous) fun x => ?_
      have h := abs_le.mp (abs_norm_coe_le m x)
      exact ne_of_gt (by linarith))
    (1 / (c - ‖m‖)) fun x => by
      have h := abs_le.mp (abs_norm_coe_le m x)
      have hge : c - ‖m‖ ≤ c + m x := by linarith
      have hpos : (0 : ℝ) < c - ‖m‖ := by linarith
      have hxpos : (0 : ℝ) < c + m x := by linarith
      rw [Real.norm_eq_abs, abs_inv, abs_of_pos hxpos, inv_eq_one_div]
      exact one_div_le_one_div_of_le hpos hge

@[simp]
theorem coe_invAddBcf (c : ℝ) (m : α →ᵇ ℝ) (hc : ‖m‖ < c) :
    ⇑(invAddBcf c m hc) = fun x => (c + m x)⁻¹ :=
  BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _

/-- The sup-norm bound for `invAddBcf`. -/
private theorem norm_invAddBcf_le (c : ℝ) (m : α →ᵇ ℝ) (hc : ‖m‖ < c) :
    ‖invAddBcf c m hc‖ ≤ 1 / (c - ‖m‖) := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun x => ?_
  have h := abs_le.mp (abs_norm_coe_le m x)
  have hge : c - ‖m‖ ≤ c + m x := by linarith
  have hpos : (0 : ℝ) < c - ‖m‖ := by linarith
  have hxpos : (0 : ℝ) < c + m x := by linarith
  simp only [coe_invAddBcf]
  rw [Real.norm_eq_abs, abs_inv, abs_of_pos hxpos, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos hge

/-- Multiplication by the pointwise inverse `(c + m)⁻¹`; this is the resolvent of the
multiplication semigroup for `c > ‖m‖`, see
`StronglyContinuousSemigroup.ofMultiplication_resolvent_eq`. -/
def resolventMulLeft (c : ℝ) (m : α →ᵇ ℝ) (hc : ‖m‖ < c) :
    (α →ᵇ ℝ) →L[ℝ] (α →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (invAddBcf c m hc) f
      map_add' := fun f g => by
        refine BoundedContinuousFunction.ext fun x => ?_
        simp only [ContinuousLinearMap.mul_apply', BoundedContinuousFunction.mul_apply,
          BoundedContinuousFunction.coe_add, Pi.add_apply, coe_invAddBcf]
        ring
      map_smul' := fun r f => by
        refine BoundedContinuousFunction.ext fun x => ?_
        simp only [ContinuousLinearMap.mul_apply', BoundedContinuousFunction.mul_apply,
          BoundedContinuousFunction.coe_smul, smul_eq_mul,
          coe_invAddBcf, RingHom.id_apply]
        ring }
    (1 / (c - ‖m‖)) fun f => by
      calc ‖ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (invAddBcf c m hc) f‖
          ≤ ‖invAddBcf c m hc‖ * ‖f‖ := norm_mul_le _ _
        _ ≤ 1 / (c - ‖m‖) * ‖f‖ :=
              mul_le_mul_of_nonneg_right (norm_invAddBcf_le c m hc) (norm_nonneg _)

@[simp]
theorem resolventMulLeft_apply (c : ℝ) (m : α →ᵇ ℝ) (hc : ‖m‖ < c) (f : α →ᵇ ℝ) :
    resolventMulLeft c m hc f = invAddBcf c m hc * f := by
  simp only [resolventMulLeft, LinearMap.mkContinuous_apply,
    ContinuousLinearMap.mul_apply']
  rfl

/-- Pointwise action of the concrete resolvent:
`(R(λ) f)(x) = (λ + m x)⁻¹ · f(x)` for `λ > ‖m‖`. -/
theorem resolventMulLeft_apply_apply (c : ℝ) (m : α →ᵇ ℝ) (hc : ‖m‖ < c) (f : α →ᵇ ℝ)
    (x : α) : resolventMulLeft c m hc f x = (c + m x)⁻¹ * f x := by
  rw [resolventMulLeft_apply, BoundedContinuousFunction.mul_apply, coe_invAddBcf]

/-- **The resolvent of the multiplication semigroup**: for `‖m‖ < λ`, the Laplace-transform
resolvent acts as multiplication by the pointwise inverse `(λ + m)⁻¹`,
that is `R(λ) f = (λ + m)⁻¹ · f`. -/
theorem StronglyContinuousSemigroup.ofMultiplication_resolvent_eq (m : α →ᵇ ℝ) {c : ℝ}
    (hc : ‖m‖ < c) :
    (ofMultiplication m).resolvent (ofMultiplication_hasGrowthBound m) c hc
      = resolventMulLeft c m hc := by
  refine ContinuousLinearMap.ext fun f => BoundedContinuousFunction.ext fun x => ?_
  have hcomm := ContinuousLinearMap.integral_comp_comm
    (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) x)
    ((ofMultiplication m).integrableOn_resolvent_integrand
      (ofMultiplication_hasGrowthBound m) c hc f).integrable
  have hnorm : ∀ t : ℝ,
      Real.exp (-(c * t)) * Real.exp (-((t : ℝ) * m x)) * f x
        = f x * Real.exp (-((c + m x) * t)) := by
    intro t
    have hexp : -(c * t) + -(t * m x) = -((c + m x) * t) := by ring
    rw [← Real.exp_add, hexp]
    exact mul_comm _ _
  have hpt : ∀ t : ℝ, t ∈ Set.Ioi 0 →
      BoundedContinuousFunction.evalCLM (𝕜 := ℝ) x
          (Real.exp (-(c * t)) •
            (StronglyContinuousSemigroup.ofMultiplication m).realOperator t f)
        = Real.exp (-(c * t)) *
            ((StronglyContinuousSemigroup.ofMultiplication m) (t.toNNReal : ℝ≥0) f) x := by
    intro t ht
    rw [StronglyContinuousSemigroup.realOperator_def]
    rfl
  have hstep1 : ((ofMultiplication m).resolvent (ofMultiplication_hasGrowthBound m) c hc) f x
      = ∫ t : ℝ in Set.Ioi 0,
          Real.exp (-(c * t)) * Real.exp (-((t : ℝ) * m x)) * f x := by
    -- evaluate the Bochner integral at `x` through the continuous-linear evaluator
    change BoundedContinuousFunction.evalCLM (𝕜 := ℝ) x
      ((ofMultiplication m).resolvent (ofMultiplication_hasGrowthBound m) c hc f) = _
    rw [StronglyContinuousSemigroup.resolvent_apply, ← hcomm]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have hu : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.le
    change (BoundedContinuousFunction.evalCLM ℝ x)
        (Real.exp (-(c * t)) • ((StronglyContinuousSemigroup.ofMultiplication m).realOperator t) f)
      = Real.exp (-(c * t)) * Real.exp (-(t * m x)) * f x
    rw [hpt t ht, StronglyContinuousSemigroup.ofMultiplication_apply_apply, hu]
    ring
  rw [resolventMulLeft_apply_apply, hstep1,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      fun t (_ : t ∈ Set.Ioi 0) => hnorm t,
    MeasureTheory.integral_const_mul, integral_exp_neg_mul_Ioi
      (by have h := abs_le.mp (abs_norm_coe_le m x); linarith)]
  ring

/-- Through the bridge lemma `generator_resolvent_eq`, the concrete formula identifies the
resolvent of the generator: it is multiplication by the pointwise inverse `(λ + m)⁻¹`
for `λ > ‖m‖`. -/
theorem StronglyContinuousSemigroup.ofMultiplication_generator_resolvent_eq (m : α →ᵇ ℝ)
    {c : ℝ} (hc : ‖m‖ < c) :
    LinearPMap.resolvent (ofMultiplication m).generator c = resolventMulLeft c m hc := by
  rw [generator_resolvent_eq _ (ofMultiplication_hasGrowthBound m) hc,
    ofMultiplication_resolvent_eq]

/-! ## The contraction case -/

/-- For a nonnegative multiplier `m ≥ 0`, the multiplication semigroup is contractive; in
particular the abstract bound `ContractionSemigroup.resolvent_norm_le` applies to it, giving
the concrete estimate `‖R(λ)‖ ≤ 1/λ` for `λ > 0`. -/
def ContractionSemigroup.ofMultiplication (m : α →ᵇ ℝ) (hm : ∀ x, 0 ≤ m x) :
    ContractionSemigroup (α →ᵇ ℝ) where
  toStronglyContinuousSemigroup := StronglyContinuousSemigroup.ofMultiplication m
  contracting t := by
    calc ‖StronglyContinuousSemigroup.ofMultiplication m t‖
        ≤ ‖expNegMulBcf (t : ℝ) m‖ := ContinuousLinearMap.opNorm_mul_apply_le ℝ _ _
      _ ≤ 1 := by
          refine (BoundedContinuousFunction.norm_le zero_le_one).mpr fun x => ?_
          simp only [coe_expNegMulBcf, Real.norm_eq_abs,
            abs_of_nonneg (Real.exp_nonneg _)]
          exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg t.coe_nonneg (hm x)))

end TauCeti.Semigroups
