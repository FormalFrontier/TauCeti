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
bounded by `M`; this is factored through the shared limit construction in
`TauCeti.Semigroups.yosidaLimitSemigroupOf`.

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
    yosidaLimit A t (x + y) = yosidaLimit A t x + yosidaLimit A t y :=
  yosidaLimit_add_of_tendsto
    (fun u => tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht u) x y

/-- The Hille--Yosida limit is homogeneous in the vector variable. -/
theorem yosidaLimit_smul_of_norm_resolvent_pow_le {t : ℝ} (ht : 0 ≤ t) (c : ℝ) (x : X) :
    yosidaLimit A t (c • x) = c • yosidaLimit A t x :=
  yosidaLimit_smul_of_tendsto
    (fun u => tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht u) c x

omit hres hdense in
private theorem eventually_exp_smul_yosidaApproximation_norm_le_of_norm_resolvent_pow_le
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᶠ lambda in atTop, ‖exp (t • yosidaApproximation A lambda)‖ ≤ M := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with lambda hlambda
  exact norm_exp_smul_yosidaApproximation_le hM hlambda ht
    fun n hn => hpow n hn lambda hlambda

/-- The Hille--Yosida limit has operator bound `M` at every nonnegative time. -/
theorem norm_yosidaLimit_le_of_norm_resolvent_pow_le {t : ℝ} (ht : 0 ≤ t) (x : X) :
    ‖yosidaLimit A t x‖ ≤ M * ‖x‖ :=
  norm_yosidaLimit_le_of_tendsto_of_norm_le
    (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht x)
    (eventually_exp_smul_yosidaApproximation_norm_le_of_norm_resolvent_pow_le hM hpow ht)

/-! ## The semigroup law and continuity -/

/-- The Hille--Yosida limit satisfies the semigroup law at nonnegative times. -/
theorem yosidaLimit_time_add_of_norm_resolvent_pow_le {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (x : X) :
    yosidaLimit A (s + t) x = yosidaLimit A s (yosidaLimit A t x) :=
  yosidaLimit_time_add_of_tendsto x
    (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht x)
    (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense hs (yosidaLimit A t x))
    (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense (add_nonneg hs ht) x)
    (eventually_exp_smul_yosidaApproximation_norm_le_of_norm_resolvent_pow_le hM hpow hs)

/-- The Hille--Yosida limit is continuous in time on every compact nonnegative interval. -/
theorem continuousOn_yosidaLimit_Icc_of_norm_resolvent_pow_le
    (x : X) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t : ℝ => yosidaLimit A t x) (Set.Icc 0 T) :=
  continuousOn_yosidaLimit_Icc_of_tendstoUniformlyOn A x
    (tendstoUniformlyOn_exp_yosidaApproximation_of_norm_resolvent_pow_le hM hres hpow hdense x hT)

/-- The Hille--Yosida limit is continuous on the nonnegative half-line. -/
theorem continuousOn_yosidaLimit_of_norm_resolvent_pow_le (x : X) :
    ContinuousOn (fun t : ℝ => yosidaLimit A t x) (Set.Ici 0) :=
  continuousOn_yosidaLimit_of_continuousOn_Icc A x fun _T hT =>
    continuousOn_yosidaLimit_Icc_of_norm_resolvent_pow_le hM hres hpow hdense x hT

private theorem continuousAt_yosidaLimit_zero_of_norm_resolvent_pow_le (x : X) :
    ContinuousAt (fun t : ℝ≥0 => yosidaLimit A t x) 0 :=
  continuousAt_yosidaLimit_zero_of_continuousOn_Ici A x
    (continuousOn_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense x)

/-! ## The limit semigroup -/

/-- The strongly continuous semigroup obtained as the strong limit of the exponent-zero
Hille--Yosida approximating semigroups. -/
def hilleYosidaLimitSemigroup : StronglyContinuousSemigroup X :=
  yosidaLimitSemigroupOf A M hM
    (fun _t ht _x => tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht _)
    (fun _x _T hT =>
      tendstoUniformlyOn_exp_yosidaApproximation_of_norm_resolvent_pow_le hM hres hpow hdense _ hT)
    (fun _t ht =>
      eventually_exp_smul_yosidaApproximation_norm_le_of_norm_resolvent_pow_le hM hpow ht)

@[simp]
theorem hilleYosidaLimitSemigroup_apply (t : ℝ≥0) (x : X) :
    hilleYosidaLimitSemigroup hM hres hpow hdense t x = yosidaLimit A t x :=
  yosidaLimitSemigroupOf_apply A M hM _ _ _ t x

/-- The exponent-zero Hille--Yosida limit semigroup has growth bound `(0, M)`. -/
theorem hilleYosidaLimitSemigroup_hasGrowthBound :
    (hilleYosidaLimitSemigroup hM hres hpow hdense).HasGrowthBound 0 M :=
  yosidaLimitSemigroupOf_hasGrowthBound A M hM
    (fun _t ht _x => tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht _)
    (fun _x _T hT =>
      tendstoUniformlyOn_exp_yosidaApproximation_of_norm_resolvent_pow_le hM hres hpow hdense _ hT)
    (fun _t ht =>
      eventually_exp_smul_yosidaApproximation_norm_le_of_norm_resolvent_pow_le hM hpow ht)

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
