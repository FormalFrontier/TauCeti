/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Semigroups.Generation.HilleYosida.Convergence
public import TauCeti.Analysis.Semigroups.Generation.LimitSemigroup

/-!
# The exponent-zero Hille--Yosida limit semigroup

Let `A` be a densely defined operator on a real Banach space. Suppose every positive real number
belongs to its resolvent set and, for some `M ≥ 1`,

`‖R(lambda, A) ^ n‖ ≤ M / lambda ^ n`

for every `n ≥ 1` and `lambda > 0`. The Yosida exponentials `exp (t A_lambda) x` are uniformly
Cauchy on compact nonnegative time intervals. This file turns their pointwise limits into a
strongly continuous semigroup and proves its exponent-zero growth bound `‖S(t)‖ ≤ M`.

The underlying limit is `TauCeti.Semigroups.yosidaLimit`, shared with the Lumer--Phillips
construction. The proof of the semigroup law uses the exact law for each bounded exponential. In
passing to the limit, the first error is multiplied by an approximating exponential, whose norm is
bounded by `M`; this is the only change from the contraction case.

This is the limit stage of the Hille--Yosida generation theorem. Identifying the generator with
`A`, and then undoing the scalar shift, remain separate steps.

## Main results

* `TauCeti.Semigroups.tendsto_yosidaLimit_of_norm_resolvent_pow_le`: the Yosida exponentials
  converge pointwise to `yosidaLimit`.
* `TauCeti.Semigroups.hilleYosidaLimitSemigroup`: the resulting strongly continuous semigroup.
* `TauCeti.Semigroups.hilleYosidaLimitSemigroup_hasGrowthBound`: its growth bound `(0, M)`.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Theorem II.3.5.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Chapter 1, Theorem 3.1.
-/

public section

noncomputable section

open scoped NNReal Topology

open Filter NormedSpace

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {A : X →ₗ.[ℝ] X} {M : ℝ}

section

variable (hM : 1 ≤ M)
variable (hres : ∀ lambda : ℝ, 0 < lambda → lambda ∈ LinearPMap.resolventSet A)
variable (hpow : ∀ n : ℕ, 1 ≤ n → ∀ lambda : ℝ, 0 < lambda →
  ‖LinearPMap.resolvent A lambda ^ n‖ ≤ M / lambda ^ n)
variable (hdense : Dense (A.domain : Set X))

private theorem exp_add_smul_apply (B : X →L[ℝ] X) (s t : ℝ) (x : X) :
    exp ((s + t) • B) x = exp (s • B) (exp (t • B) x) := by
  let +nondep : NormedAlgebra ℚ (X →L[ℝ] X) := .restrictScalars ℚ ℝ _
  rw [add_smul, exp_add_of_commute (((Commute.refl B).smul_left s).smul_right t),
    ContinuousLinearMap.mul_def]
  rfl

include hM hres hpow hdense

/-! ## Convergence and the vector-space structure -/

/-- Under the exponent-zero Hille--Yosida bounds, the Yosida exponentials converge to the chosen
Yosida limit at every nonnegative time. -/
theorem tendsto_yosidaLimit_of_norm_resolvent_pow_le {t : ℝ} (ht : 0 ≤ t) (x : X) :
    Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
      (𝓝 (yosidaLimit A t x)) :=
  tendsto_yosidaLimit_of_cauchySeq A t x <|
    (exp_yosidaApproximation_uniformCauchySeqOn_compact_of_norm_resolvent_pow_le hM hres hpow
      hdense x ht).cauchySeq (Set.right_mem_Icc.mpr ht)

/-- Convergence of the Hille--Yosida approximations is uniform on every compact nonnegative time
interval. -/
theorem tendstoUniformlyOn_exp_yosidaApproximation_of_norm_resolvent_pow_le
    (x : X) {T : ℝ} (hT : 0 ≤ T) :
    TendstoUniformlyOn (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) x)
      (fun t : ℝ => yosidaLimit A t x) atTop (Set.Icc 0 T) :=
  (exp_yosidaApproximation_uniformCauchySeqOn_compact_of_norm_resolvent_pow_le hM hres hpow
    hdense x hT).tendstoUniformlyOn_of_tendsto fun _t ht =>
      tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht.1 x

/-- The Hille--Yosida limit is additive in the vector variable. -/
theorem yosidaLimit_add_of_norm_resolvent_pow_le {t : ℝ} (ht : 0 ≤ t) (x y : X) :
    yosidaLimit A t (x + y) = yosidaLimit A t x + yosidaLimit A t y := by
  refine tendsto_nhds_unique
    (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht (x + y)) ?_
  simpa only [map_add] using
    (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht x).add
      (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht y)

/-- The Hille--Yosida limit is homogeneous in the vector variable. -/
theorem yosidaLimit_smul_of_norm_resolvent_pow_le {t : ℝ} (ht : 0 ≤ t) (c : ℝ) (x : X) :
    yosidaLimit A t (c • x) = c • yosidaLimit A t x := by
  refine tendsto_nhds_unique
    (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht (c • x)) ?_
  simpa only [map_smul] using
    (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht x).const_smul c

/-- The Hille--Yosida limit has operator bound `M` at every nonnegative time. -/
theorem norm_yosidaLimit_le_of_norm_resolvent_pow_le {t : ℝ} (ht : 0 ≤ t) (x : X) :
    ‖yosidaLimit A t x‖ ≤ M * ‖x‖ := by
  refine le_of_tendsto
    (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht x).norm ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with lambda hlambda
  calc
    ‖exp (t • yosidaApproximation A lambda) x‖
        ≤ ‖exp (t • yosidaApproximation A lambda)‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ ≤ M * ‖x‖ := by
      gcongr
      exact norm_exp_smul_yosidaApproximation_le hM hlambda ht
        fun n hn => hpow n hn lambda hlambda

/-! ## The semigroup law and continuity -/

/-- The Hille--Yosida limit satisfies the semigroup law at nonnegative times. -/
theorem yosidaLimit_time_add_of_norm_resolvent_pow_le {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (x : X) :
    yosidaLimit A (s + t) x = yosidaLimit A s (yosidaLimit A t x) := by
  set y := yosidaLimit A t x with hy
  set z := yosidaLimit A s y with hz
  have hstep : Tendsto (fun lambda : ℝ => exp ((s + t) • yosidaApproximation A lambda) x - z)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun lambda : ℝ =>
      M * ‖exp (t • yosidaApproximation A lambda) x - y‖ +
        ‖exp (s • yosidaApproximation A lambda) y - z‖) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with lambda hlambda
      have hbound : ‖exp (s • yosidaApproximation A lambda)‖ ≤ M :=
        norm_exp_smul_yosidaApproximation_le hM hlambda hs
          fun n hn => hpow n hn lambda hlambda
      have hsplit : exp ((s + t) • yosidaApproximation A lambda) x - z =
          exp (s • yosidaApproximation A lambda)
              (exp (t • yosidaApproximation A lambda) x - y) +
            (exp (s • yosidaApproximation A lambda) y - z) := by
        rw [map_sub, exp_add_smul_apply]
        abel
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ?_ le_rfl
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))
    · have h1 : Tendsto
          (fun lambda : ℝ => ‖exp (t • yosidaApproximation A lambda) x - y‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.mp
          (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht x)
      have h2 : Tendsto
          (fun lambda : ℝ => ‖exp (s • yosidaApproximation A lambda) y - z‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.mp
          (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense hs y)
      simpa using (h1.const_mul M).add h2
  refine tendsto_nhds_unique
    (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense (add_nonneg hs ht) x) ?_
  simpa using hstep.add_const z

/-- The Hille--Yosida limit is continuous in time on every compact nonnegative interval. -/
theorem continuousOn_yosidaLimit_Icc_of_norm_resolvent_pow_le
    (x : X) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t : ℝ => yosidaLimit A t x) (Set.Icc 0 T) :=
  (tendstoUniformlyOn_exp_yosidaApproximation_of_norm_resolvent_pow_le
    hM hres hpow hdense x hT).continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun lambda =>
      (((differentiable_exp_smul_const ℝ (yosidaApproximation A lambda)).continuous).clm_apply
        continuous_const).continuousOn))

/-- The Hille--Yosida limit is continuous on the nonnegative half-line. -/
theorem continuousOn_yosidaLimit_of_norm_resolvent_pow_le (x : X) :
    ContinuousOn (fun t : ℝ => yosidaLimit A t x) (Set.Ici 0) := by
  intro t ht
  have ht' : (0 : ℝ) ≤ t := ht
  have hmem : Set.Icc 0 (t + 1) ∈ 𝓝[Set.Ici (0 : ℝ)] t := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Set.Iio (t + 1), Iio_mem_nhds (by linarith), ?_⟩
    rintro u ⟨hu₁, hu₂⟩
    exact ⟨hu₂, le_of_lt hu₁⟩
  exact (continuousOn_yosidaLimit_Icc_of_norm_resolvent_pow_le
    hM hres hpow hdense x (by linarith : (0 : ℝ) ≤ t + 1) t
      ⟨ht', by linarith⟩).mono_of_mem_nhdsWithin hmem

private theorem continuousAt_yosidaLimit_zero_of_norm_resolvent_pow_le (x : X) :
    ContinuousAt (fun t : ℝ≥0 => yosidaLimit A t x) 0 := by
  have hIci : ContinuousWithinAt (fun t : ℝ => yosidaLimit A t x) (Set.Ici 0)
      (((0 : ℝ≥0) : ℝ)) := by
    simpa using continuousOn_yosidaLimit_of_norm_resolvent_pow_le
      hM hres hpow hdense x 0 (Set.mem_Ici.mpr le_rfl)
  have hcoe : ContinuousWithinAt (fun t : ℝ≥0 => (t : ℝ)) Set.univ 0 :=
    NNReal.continuous_coe.continuousWithinAt
  exact continuousWithinAt_univ _ _ |>.mp
    (hIci.comp hcoe fun t _ => t.coe_nonneg)

/-! ## The limit semigroup -/

private def hilleYosidaLimitCLM (t : ℝ≥0) : X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := fun x => yosidaLimit A t x
      map_add' := yosidaLimit_add_of_norm_resolvent_pow_le hM hres hpow hdense t.coe_nonneg
      map_smul' := yosidaLimit_smul_of_norm_resolvent_pow_le hM hres hpow hdense t.coe_nonneg }
    M fun x => by
      simpa using norm_yosidaLimit_le_of_norm_resolvent_pow_le
        hM hres hpow hdense t.coe_nonneg x

@[simp]
private theorem hilleYosidaLimitCLM_apply (t : ℝ≥0) (x : X) :
    hilleYosidaLimitCLM hM hres hpow hdense t x = yosidaLimit A t x :=
  (rfl)

private theorem norm_hilleYosidaLimitCLM_le (t : ℝ≥0) :
    ‖hilleYosidaLimitCLM hM hres hpow hdense t‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _ (zero_le_one.trans hM) _

/-- The strongly continuous semigroup obtained as the strong limit of the exponent-zero
Hille--Yosida approximating semigroups. -/
def hilleYosidaLimitSemigroup : StronglyContinuousSemigroup X where
  toFun := hilleYosidaLimitCLM hM hres hpow hdense
  map_zero' := by
    ext x
    simp [hilleYosidaLimitCLM_apply]
  map_add' s t := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, hilleYosidaLimitCLM_apply, NNReal.coe_add]
    exact yosidaLimit_time_add_of_norm_resolvent_pow_le
      hM hres hpow hdense s.coe_nonneg t.coe_nonneg x
  continuousAt_zero' x := by
    simpa only [hilleYosidaLimitCLM_apply] using
      continuousAt_yosidaLimit_zero_of_norm_resolvent_pow_le hM hres hpow hdense x

@[simp]
theorem hilleYosidaLimitSemigroup_apply (t : ℝ≥0) (x : X) :
    hilleYosidaLimitSemigroup hM hres hpow hdense t x = yosidaLimit A t x :=
  (rfl)

/-- The exponent-zero Hille--Yosida limit semigroup has growth bound `(0, M)`. -/
theorem hilleYosidaLimitSemigroup_hasGrowthBound :
    (hilleYosidaLimitSemigroup hM hres hpow hdense).HasGrowthBound 0 M := by
  refine StronglyContinuousSemigroup.hasGrowthBound_of_bound hM fun t ht => ?_
  rw [zero_mul, Real.exp_zero, mul_one, StronglyContinuousSemigroup.realOperator_def]
  have heq : hilleYosidaLimitSemigroup hM hres hpow hdense t.toNNReal =
      hilleYosidaLimitCLM hM hres hpow hdense t.toNNReal := (rfl)
  rw [heq]
  exact norm_hilleYosidaLimitCLM_le hM hres hpow hdense t.toNNReal

/-- The orbits of the exponent-zero Hille--Yosida limit semigroup are the limits of the Yosida
exponentials. -/
theorem tendsto_hilleYosidaLimitSemigroup (t : ℝ≥0) (x : X) :
    Tendsto (fun lambda : ℝ => exp ((t : ℝ) • yosidaApproximation A lambda) x) atTop
      (𝓝 (hilleYosidaLimitSemigroup hM hres hpow hdense t x)) := by
  rw [hilleYosidaLimitSemigroup_apply]
  exact tendsto_yosidaLimit_of_norm_resolvent_pow_le
    hM hres hpow hdense t.coe_nonneg x

/-- Exponent-zero Hille--Yosida bounds produce a strongly continuous semigroup with growth bound
`(0, M)`, whose orbits are the strong limits of the Yosida exponentials. -/
theorem exists_semigroup_hasGrowthBound_of_norm_resolvent_pow_le :
    ∃ S : StronglyContinuousSemigroup X,
      S.HasGrowthBound 0 M ∧ ∀ (t : ℝ≥0) (x : X),
        Tendsto (fun lambda : ℝ => exp ((t : ℝ) • yosidaApproximation A lambda) x) atTop
          (𝓝 (S t x)) :=
  ⟨hilleYosidaLimitSemigroup hM hres hpow hdense,
    hilleYosidaLimitSemigroup_hasGrowthBound hM hres hpow hdense,
    tendsto_hilleYosidaLimitSemigroup hM hres hpow hdense⟩

end

end TauCeti.Semigroups

end
