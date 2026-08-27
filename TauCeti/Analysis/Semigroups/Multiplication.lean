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

import Mathlib.Analysis.Complex.Exponential
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
  `e^{-t·m}`, with growth bound `(‖m⁻‖, 1)` controlled by the negative part of `m`;
* its generator: the domain is the whole space and the generator is multiplication by `-m`
  (`ofMultiplication_domain_eq_top`, `ofMultiplication_generator`);
* its resolvent: for `‖m⁻‖ < λ` the Laplace-transform resolvent acts as multiplication by the
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

Taylor remainders for `Real.exp`, specialized from `Complex.norm_exp_sub_sum_le_norm_mul_exp`,
used to control difference quotients uniformly over the range of a bounded continuous
multiplier. -/

/-- `|exp w - 1| ≤ |w| · exp |w|` for every real `w`. -/
private theorem abs_exp_sub_one_le_abs_mul_exp_abs (w : ℝ) :
    |Real.exp w - 1| ≤ |w| * Real.exp |w| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (w : ℂ) 1
  have hsum : ∑ m ∈ Finset.range 1, (w : ℂ) ^ m / m.factorial = 1 := by
    rw [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [hsum, pow_one, Complex.norm_real, Real.norm_eq_abs] at h
  rwa [← Real.norm_eq_abs, ← Complex.norm_real (Real.exp w - 1), Complex.ofReal_sub,
    Complex.ofReal_exp, Complex.ofReal_one]

/-- `|exp (-u) - 1 + u| ≤ u² · exp |u|`. -/
private theorem abs_exp_neg_sub_one_add_self_le_sq_mul_exp_abs (u : ℝ) :
    |Real.exp (-u) - 1 + u| ≤ u ^ 2 * Real.exp |u| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp ((-u : ℝ) : ℂ) 2
  have hsum : ∑ m ∈ Finset.range 2, ((-u : ℝ) : ℂ) ^ m / m.factorial = 1 + -(u : ℂ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one, Complex.ofReal_neg]
  rw [hsum, Complex.norm_real, Real.norm_eq_abs, abs_neg, sq_abs] at h
  rw [← Real.norm_eq_abs, ← Complex.norm_real (Real.exp (-u) - 1 + u)]
  convert h
  rw [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_exp, Complex.ofReal_one,
    Complex.ofReal_neg]
  ring

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
    ‖expNegMulBcf t m‖ ≤ Real.exp (|t| * ‖m‖) :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _

/-- Uniform second-order control of the difference quotients of the exponential multiplier:
`(exp (-t·m) - 1) / t` differs from `-m` by at most `t · ‖m‖² · e^{t‖m‖}` in sup norm. -/
private theorem norm_quot_expNegMulBcf_add_le (m : α →ᵇ ℝ) {t : ℝ} (ht : 0 < t) :
    ‖(1 / t) • (expNegMulBcf t m - 1) + m‖ ≤ t * ‖m‖ ^ 2 * Real.exp (t * ‖m‖) := by
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
      ≤ (t * m x) ^ 2 * Real.exp (t * |m x|) := by
    rw [abs_mul, abs_of_pos ht] at hkey
    exact hkey
  have hstep2 : (t * m x) ^ 2 * Real.exp (t * |m x|) / t
      = t * (m x) ^ 2 * Real.exp (t * |m x|) := by
    field_simp
  calc |(1 / t) • (expNegMulBcf t m - 1) x + m x|
      = |(Real.exp (-(t * m x)) - 1) / t + m x| := hx2
    _ = |Real.exp (-(t * m x)) - 1 + t * m x| / t := by
        rw [harg, abs_div, abs_of_pos ht]
    _ ≤ (t * m x) ^ 2 * Real.exp (t * |m x|) / t :=
        div_le_div_of_nonneg_right hkey' ht.le
    _ = t * (m x) ^ 2 * Real.exp (t * |m x|) := hstep2
    _ ≤ t * ‖m‖ ^ 2 * Real.exp (t * ‖m‖) := by
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
(`ofMultiplication_generator`), and for `λ > ‖m⁻‖` its resolvent acts as multiplication by the
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
    rw [add_mul, neg_add, ← mul_assoc, ← Real.exp_add]
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
    refine (tendsto_iff_dist_tendsto_zero).mpr ?_
    exact squeeze_zero (fun _ => dist_nonneg) (fun t => key t) hbdd

@[simp]
theorem StronglyContinuousSemigroup.ofMultiplication_apply (m : α →ᵇ ℝ) (t : ℝ≥0)
    (f : α →ᵇ ℝ) : ofMultiplication m t f = expNegMulBcf (t : ℝ) m * f := by
  rw [ofMultiplication]
  rfl

/-- Pointwise action of the multiplication semigroup: `(S(t) f)(x) = e^{-t·m x} · f(x)`. -/
theorem StronglyContinuousSemigroup.ofMultiplication_apply_apply (m : α →ᵇ ℝ) (t : ℝ≥0)
    (f : α →ᵇ ℝ) (x : α) : ofMultiplication m t f x = Real.exp (-((t : ℝ) * m x)) * f x := by
  simp only [ofMultiplication_apply]
  rfl

/-- For `t ≥ 0`, the exponential multiplier is bounded by `e^{t ‖m⁻‖}`. -/
private theorem norm_expNegMulBcf_le_exp_mul_norm_negPart {t : ℝ} (ht : 0 ≤ t) (m : α →ᵇ ℝ) :
    ‖expNegMulBcf t m‖ ≤ Real.exp (t * ‖m⁻‖) := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun x => ?_
  simp only [coe_expNegMulBcf, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  refine Real.exp_le_exp.mpr ?_
  calc -(t * m x) = t * (-m x) := (mul_neg t (m x)).symm
    _ ≤ t * (m x)⁻ := mul_le_mul_of_nonneg_left (neg_le_negPart (m x)) ht
    _ ≤ t * ‖m⁻‖ :=
        mul_le_mul_of_nonneg_left (by simpa using BoundedContinuousFunction.apply_le_norm (m⁻) x) ht

/-- The multiplication semigroup has growth bound `(‖m⁻‖, 1)`. -/
theorem StronglyContinuousSemigroup.ofMultiplication_hasGrowthBound (m : α →ᵇ ℝ) :
    (ofMultiplication m).HasGrowthBound ‖m⁻‖ 1 :=
  hasGrowthBound_of_bound le_rfl fun t ht => by
    have hu : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht
    have hroe : (ofMultiplication m).realOperator t
        = ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (expNegMulBcf t m) := by
      rw [← hu]
      exact realOperator_coe ..
    rw [hroe]
    refine le_trans (ContinuousLinearMap.opNorm_mul_apply_le ℝ _ _) ?_
    refine le_trans (norm_expNegMulBcf_le_exp_mul_norm_negPart ht _) ?_
    rw [one_mul, mul_comm t]

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
        ≤ (t * ‖m‖ ^ 2 * Real.exp (t * ‖m‖)) * ‖f‖ := by
    intro t ht
    rw [dist_eq_norm, hsplit t ht]
    calc ‖ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) ((1 / t) • (expNegMulBcf t m - 1) + m) f‖
        ≤ ‖(1 / t) • (expNegMulBcf t m - 1) + m‖ * ‖f‖ := norm_mul_le _ _
      _ ≤ (t * ‖m‖ ^ 2 * Real.exp (t * ‖m‖)) * ‖f‖ :=
            mul_le_mul_of_nonneg_right (norm_quot_expNegMulBcf_add_le m ht) (norm_nonneg _)
  have hcont : Continuous
      fun t : ℝ => (t * ‖m‖ ^ 2 * Real.exp (t * ‖m‖)) * ‖f‖ := by fun_prop
  have hz2 : ((0:ℝ) * ‖m‖ ^ 2 * Real.exp (0 * ‖m‖)) * ‖f‖ = 0 := by simp
  have h0 : Filter.Tendsto
      (fun t : ℝ => (t * ‖m‖ ^ 2 * Real.exp (t * ‖m‖)) * ‖f‖)
      (nhds 0) (nhds (((0:ℝ) * ‖m‖ ^ 2 * Real.exp (0 * ‖m‖)) * ‖f‖)) :=
    hcont.continuousAt.tendsto
  rw [hz2] at h0
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_
    (h0.mono_left inf_le_left)
  have hmem : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t ∈ Set.Ioi 0 :=
    eventually_mem_nhdsWithin
  exact hmem.mono fun t ht => hbound t (Set.mem_Ioi.mp ht)

/-- The generator domain of the multiplication semigroup is the whole space. -/
@[simp]
theorem StronglyContinuousSemigroup.ofMultiplication_domain_eq_top (m : α →ᵇ ℝ) :
    (ofMultiplication m).domain = ⊤ :=
  (generator_eq_toPMap_top_of_forall_tendsto _ _ (tendsto_quot_orbit_ofMultiplication m)).1

/-- **The generator of the multiplication semigroup** is multiplication by `-m`, on the whole
space. -/
@[simp]
theorem StronglyContinuousSemigroup.ofMultiplication_generator (m : α →ᵇ ℝ) :
    (ofMultiplication m).generator =
      (ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (-m)).toLinearMap.toPMap ⊤ :=
  (generator_eq_toPMap_top_of_forall_tendsto _ _ (tendsto_quot_orbit_ofMultiplication m)).2


/-! ## The concrete resolvent -/

/-- The hypothesis `‖m⁻‖ < c` guarantees `c + m x > 0` for every `x`. -/
private theorem add_pos_of_norm_negPart_lt {c : ℝ} {m : α →ᵇ ℝ} (hc : ‖m⁻‖ < c) (x : α) :
    0 < c + m x := by
  have hneg : (m x)⁻ ≤ ‖m⁻‖ := by
    simpa using BoundedContinuousFunction.apply_le_norm (m⁻) x
  linarith [neg_le_negPart (m x)]

/-- The pointwise inverse `(c + m)⁻¹` of a positive perturbation of a bounded continuous
multiplier, as bounded continuous function.  The hypothesis `‖m⁻‖ < c` guarantees
`c + m x ≥ c - ‖m⁻‖ > 0` for every `x`. -/
def invAddBcf (c : ℝ) (m : α →ᵇ ℝ) (hc : ‖m⁻‖ < c) : α →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (c + m x)⁻¹)
    (by
      refine Continuous.inv₀ (continuous_const.add m.continuous) fun x => ?_
      exact ne_of_gt (add_pos_of_norm_negPart_lt hc x))
    (1 / (c - ‖m⁻‖)) fun x => by
      have hge : c - ‖m⁻‖ ≤ c + m x := by
        have hneg : (m x)⁻ ≤ ‖m⁻‖ := by
          simpa using BoundedContinuousFunction.apply_le_norm (m⁻) x
        linarith [neg_le_negPart (m x)]
      have hpos : (0 : ℝ) < c - ‖m⁻‖ := by linarith
      have hxpos : (0 : ℝ) < c + m x := add_pos_of_norm_negPart_lt hc x
      rw [Real.norm_eq_abs, abs_inv, abs_of_pos hxpos, inv_eq_one_div]
      exact one_div_le_one_div_of_le hpos hge

@[simp]
theorem coe_invAddBcf (c : ℝ) (m : α →ᵇ ℝ) (hc : ‖m⁻‖ < c) :
    ⇑(invAddBcf c m hc) = fun x => (c + m x)⁻¹ :=
  BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _

/-- Multiplication by the pointwise inverse `(c + m)⁻¹`; this is the resolvent of the
multiplication semigroup for `c > ‖m⁻‖`, see
`StronglyContinuousSemigroup.ofMultiplication_resolvent_eq`. -/
def resolventMulLeft (c : ℝ) (m : α →ᵇ ℝ) (hc : ‖m⁻‖ < c) :
    (α →ᵇ ℝ) →L[ℝ] (α →ᵇ ℝ) :=
  ContinuousLinearMap.mul ℝ (α →ᵇ ℝ) (invAddBcf c m hc)

@[simp]
theorem resolventMulLeft_apply (c : ℝ) (m : α →ᵇ ℝ) (hc : ‖m⁻‖ < c) (f : α →ᵇ ℝ) :
    resolventMulLeft c m hc f = invAddBcf c m hc * f := by
  rw [resolventMulLeft]
  rfl

/-- Pointwise action of the concrete resolvent:
`(R(λ) f)(x) = (λ + m x)⁻¹ · f(x)` for `λ > ‖m⁻‖`. -/
theorem resolventMulLeft_apply_apply (c : ℝ) (m : α →ᵇ ℝ) (hc : ‖m⁻‖ < c) (f : α →ᵇ ℝ)
    (x : α) : resolventMulLeft c m hc f x = (c + m x)⁻¹ * f x := by
  rw [resolventMulLeft_apply, BoundedContinuousFunction.mul_apply, coe_invAddBcf]

/-- **The resolvent of the multiplication semigroup**: for `‖m⁻‖ < λ`, the Laplace-transform
resolvent acts as multiplication by the pointwise inverse `(λ + m)⁻¹`,
that is `R(λ) f = (λ + m)⁻¹ · f`. -/
theorem StronglyContinuousSemigroup.ofMultiplication_resolvent_eq (m : α →ᵇ ℝ) {c : ℝ}
    (hc : ‖m⁻‖ < c) :
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
    rw [← BoundedContinuousFunction.evalCLM_apply (𝕜 := ℝ)]
    rw [StronglyContinuousSemigroup.resolvent_apply, ← hcomm]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have hu : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.le
    dsimp
    rw [hpt t ht, StronglyContinuousSemigroup.ofMultiplication_apply_apply, hu]
    ring
  rw [resolventMulLeft_apply_apply, hstep1,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      fun t (_ : t ∈ Set.Ioi 0) => hnorm t,
    MeasureTheory.integral_const_mul]
  have hint : ∫ t : ℝ in Set.Ioi 0, Real.exp (-((c + m x) * t)) = (c + m x)⁻¹ := by
    simpa [pow_zero, one_mul] using
      integral_pow_mul_exp_neg_mul_Ioi 0 (add_pos_of_norm_negPart_lt hc x)
  rw [hint]
  ring

/-- Through the bridge lemma `generator_resolvent_eq`, the concrete formula identifies the
resolvent of the generator: it is multiplication by the pointwise inverse `(λ + m)⁻¹`
for `λ > ‖m⁻‖`. -/
theorem StronglyContinuousSemigroup.ofMultiplication_generator_resolvent_eq (m : α →ᵇ ℝ)
    {c : ℝ} (hc : ‖m⁻‖ < c) :
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

/-- The C₀-semigroup underlying the multiplication contraction semigroup is the multiplication
semigroup. -/
@[simp]
theorem ContractionSemigroup.ofMultiplication_toStronglyContinuousSemigroup
    (m : α →ᵇ ℝ) (hm : ∀ x, 0 ≤ m x) :
    (ContractionSemigroup.ofMultiplication m hm).toStronglyContinuousSemigroup =
      StronglyContinuousSemigroup.ofMultiplication m := by
  rw [ContractionSemigroup.ofMultiplication]

end TauCeti.Semigroups
