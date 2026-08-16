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
construction. The semigroup packaging is obtained from the shared constructor
`TauCeti.Semigroups.yosidaLimitSemigroupOfTendsto` in `LimitSemigroup.lean`.

This is the limit stage of the Hille--Yosida generation theorem. The generator identification and
the scalar unshift are carried out in
`TauCeti/Analysis/Semigroups/Generation/HilleYosida/Generation.lean`.

## Main results

* `TauCeti.Semigroups.tendsto_yosidaLimit_of_norm_resolvent_pow_le`: the Yosida exponentials
  converge pointwise to `yosidaLimit`.
* `TauCeti.Semigroups.tendstoUniformlyOn_exp_yosidaApproximation_of_norm_resolvent_pow_le`: uniform
  convergence on compact nonnegative intervals.
* `TauCeti.Semigroups.norm_yosidaLimit_le_of_norm_resolvent_pow_le`: each limit vector satisfies
  `‖yosidaLimit A t x‖ ≤ M * ‖x‖`.
* `TauCeti.Semigroups.hilleYosidaLimitSemigroup`: the resulting strongly continuous semigroup.
* `TauCeti.Semigroups.hilleYosidaLimitSemigroup_apply`: evaluating the limit semigroup.
* `TauCeti.Semigroups.hilleYosidaLimitSemigroup_realOperator_apply_of_nonneg`: evaluating the
  real-time operator at nonnegative times.
* `TauCeti.Semigroups.hasGrowthBound_hilleYosidaLimitSemigroup`: its growth bound `(0, M)`.
* `TauCeti.Semigroups.tendsto_hilleYosidaLimitSemigroup`: convergence of approximating orbits to the
  semigroup orbits.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Theorem II.3.8.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Chapter 1, Theorem 5.3.
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

include hM hres hpow hdense

/-! ## Convergence of the approximating exponentials -/

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

omit hres hdense in
private theorem eventually_norm_exp_smul_yosidaApproximation_le_of_norm_resolvent_pow_le
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᶠ lambda in atTop, ‖exp (t • yosidaApproximation A lambda)‖ ≤ M := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with lambda hlambda
  exact norm_exp_smul_yosidaApproximation_le hM hlambda ht
    fun n hn => hpow n hn lambda hlambda

/-- Under the exponent-zero Hille--Yosida bounds, each limit vector satisfies
`‖yosidaLimit A t x‖ ≤ M * ‖x‖` at nonnegative times. -/
theorem norm_yosidaLimit_le_of_norm_resolvent_pow_le {t : ℝ} (ht : 0 ≤ t) (x : X) :
    ‖yosidaLimit A t x‖ ≤ M * ‖x‖ :=
  norm_yosidaLimit_le_of_tendsto_of_norm_le
    (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht x)
    (eventually_norm_exp_smul_yosidaApproximation_le_of_norm_resolvent_pow_le hM hpow ht)

/-! ## The limit semigroup -/

/-- The strongly continuous semigroup obtained as the strong limit of the exponent-zero
Hille--Yosida approximating semigroups. -/
def hilleYosidaLimitSemigroup : StronglyContinuousSemigroup X :=
  yosidaLimitSemigroupOfTendsto
    (fun _t ht x => tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht x)
    (fun x _T hT => tendstoUniformlyOn_exp_yosidaApproximation_of_norm_resolvent_pow_le
      hM hres hpow hdense x hT)
    (fun _t ht =>
      eventually_norm_exp_smul_yosidaApproximation_le_of_norm_resolvent_pow_le hM hpow ht)

/-- Evaluating the exponent-zero Hille--Yosida limit semigroup at `t` on `x` yields
`yosidaLimit A t x`. -/
@[simp]
theorem hilleYosidaLimitSemigroup_apply (t : ℝ≥0) (x : X) :
    hilleYosidaLimitSemigroup hM hres hpow hdense t x = yosidaLimit A t x :=
  yosidaLimitSemigroupOfTendsto_apply _ _ _ t x

/-- Evaluating the real-time operator of the exponent-zero Hille--Yosida limit semigroup at a
nonnegative time `t` yields `yosidaLimit A t x`. -/
@[simp]
theorem hilleYosidaLimitSemigroup_realOperator_apply_of_nonneg {t : ℝ} (ht : 0 ≤ t) (x : X) :
    (hilleYosidaLimitSemigroup hM hres hpow hdense).realOperator t x = yosidaLimit A t x :=
  yosidaLimitSemigroupOfTendsto_realOperator_apply_of_nonneg _ _ _ ht x

/-- The exponent-zero Hille--Yosida limit semigroup has growth bound `(0, M)`. -/
theorem hasGrowthBound_hilleYosidaLimitSemigroup :
    (hilleYosidaLimitSemigroup hM hres hpow hdense).HasGrowthBound 0 M :=
  hasGrowthBound_yosidaLimitSemigroupOfTendsto hM _ _ _

/-- The orbits of the exponent-zero Hille--Yosida limit semigroup are the limits of the Yosida
exponentials. -/
theorem tendsto_hilleYosidaLimitSemigroup (t : ℝ≥0) (x : X) :
    Tendsto (fun lambda : ℝ => exp ((t : ℝ) • yosidaApproximation A lambda) x) atTop
      (𝓝 (hilleYosidaLimitSemigroup hM hres hpow hdense t x)) :=
  tendsto_yosidaLimitSemigroupOfTendsto _ _ _ t x

end

end TauCeti.Semigroups

end
