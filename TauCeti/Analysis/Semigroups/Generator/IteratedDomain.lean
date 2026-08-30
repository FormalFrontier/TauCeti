/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Dense
public import TauCeti.Analysis.Normed.Operator.Resolvent.DomainPow
public import TauCeti.Analysis.Semigroups.Generator.Invariance
public import TauCeti.Analysis.Semigroups.Resolvent.Identity
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# The iterated generator domains of a strongly continuous semigroup are dense

`StronglyContinuousSemigroup.dense_domain` says that the domain `D(A)` of the infinitesimal
generator is dense. This file proves the same for every iterate: the domain `D(Aⁿ)` of the
`n`-th iterate of the generator is dense as well, and is preserved by every semigroup operator.

The regularising maps are the powers of the resolvent. `R(lambda)ⁿ` lands in `D(Aⁿ)`
(`TauCeti.resolvent_pow_mem_domainPow`), and `lambdaⁿ R(lambda)ⁿ` converges strongly to the
identity as `lambda → ∞`, so every vector is a limit of vectors of `D(Aⁿ)`. The convergence is
proved here at a general growth exponent: the exponent-zero statement
`TauCeti.Semigroups.tendsto_smul_resolvent_apply_atTop` asks for `‖R(lambda)‖ ≤ M / lambda`,
which a semigroup only satisfies once its growth exponent is at most `0`.

## Main results

* `TauCeti.Semigroups.StronglyContinuousSemigroup.realOperator_mem_domainPow`: every `S t`
  preserves `D(Aⁿ)`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.tendsto_smul_resolventFun_apply`:
  `lambda R(lambda) x → x` as `lambda → ∞`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.dense_domainPow`: `D(Aⁿ)` is dense.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Lemma II.1.3 and
Theorem II.1.10; Pazy, *Semigroups of Linear Operators and Applications to Partial Differential
Equations*, Theorem 1.2.7.
-/

public section

noncomputable section

open Filter
open scoped NNReal Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

variable (S : StronglyContinuousSemigroup X) {omega M : ℝ}

omit [CompleteSpace X] in
/-- Every semigroup operator preserves each iterated generator domain `D(Aⁿ)`. -/
theorem realOperator_mem_domainPow {t : ℝ} (ht : 0 ≤ t) {n : ℕ} {x : X}
    (hx : x ∈ domainPow S.generator n) :
    S.realOperator t x ∈ domainPow S.generator n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      obtain ⟨hxd, hAx⟩ := mem_domainPow_succ.mp hx
      have hxd' : x ∈ S.domain := by rwa [S.generator_domain] at hxd
      have hmem : S.realOperator t x ∈ S.generator.domain := by
        rw [S.generator_domain]
        exact S.realOperator_mem_domain ht hxd'
      refine mem_domainPow_succ.mpr ⟨hmem, ?_⟩
      have hcomm : S.generator ⟨S.realOperator t x, hmem⟩
          = S.realOperator t (S.generator ⟨x, hxd⟩) :=
        S.realOperator_generator_map ht ⟨x, hxd'⟩
      rw [hcomm]
      exact ih hAx

/-! ## Strong convergence of the scaled resolvents -/

/-- On the generator domain the scaled resolvent differs from the identity by the resolvent of
`A x`: `lambda R(lambda) x - x = R(lambda) (A x)`. -/
private theorem smul_resolventFun_sub_self (hb : S.HasGrowthBound omega M) {lambda : ℝ}
    (hlt : omega < lambda) {x : X} (hxd : x ∈ S.generator.domain) :
    lambda • S.resolventFun hb lambda x - x = S.resolventFun hb lambda (S.generator ⟨x, hxd⟩) := by
  have hres : lambda ∈ LinearPMap.resolventSet S.generator := S.mem_resolventSet_generator hb hlt
  have heq : LinearPMap.resolvent S.generator lambda = S.resolventFun hb lambda := by
    rw [S.generator_resolvent_eq hb hlt, S.resolventFun_of_lt hb hlt]
  rw [← heq, LinearPMap.resolvent_apply_comm hres ⟨x, hxd⟩, LinearPMap.apply_resolvent hres x]

/-- Beyond `2 |omega| + 1` the scaled resolvent `lambda R(lambda)` is bounded by `2 M`. The
factor `2` absorbs the difference between `lambda` and `lambda - omega`. -/
private theorem norm_smul_resolventFun_le (hb : S.HasGrowthBound omega M) {lambda : ℝ}
    (hlambda : 2 * |omega| + 1 ≤ lambda) :
    ‖lambda • S.resolventFun hb lambda‖ ≤ 2 * M := by
  have hM : (0 : ℝ) ≤ M := zero_le_one.trans hb.one_le
  have habs : omega ≤ |omega| := le_abs_self omega
  have habs0 : (0 : ℝ) ≤ |omega| := abs_nonneg omega
  have hpos : (0 : ℝ) < lambda := by linarith
  have hlt : omega < lambda := by linarith
  have hd : (0 : ℝ) < lambda - omega := by linarith
  have hhalf : lambda ≤ 2 * (lambda - omega) := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
  calc lambda * ‖S.resolventFun hb lambda‖
      ≤ lambda * (M / (lambda - omega)) := by
        gcongr
        exact S.resolventFun_norm_le hb hlt
    _ ≤ 2 * M := by
        rw [mul_div_assoc', div_le_iff₀ hd]
        nlinarith [mul_le_mul_of_nonneg_right hhalf hM]

private theorem tendsto_smul_resolventFun_apply_of_mem (hb : S.HasGrowthBound omega M)
    {x : X} (hxd : x ∈ S.generator.domain) :
    Tendsto (fun lambda : ℝ => lambda • S.resolventFun hb lambda x) atTop (nhds x) := by
  have hbnd : ∀ᶠ lambda : ℝ in atTop, ‖lambda • S.resolventFun hb lambda x - x‖
      ≤ M / (lambda - omega) * ‖S.generator ⟨x, hxd⟩‖ := by
    filter_upwards [eventually_gt_atTop omega] with lambda hlt
    rw [S.smul_resolventFun_sub_self hb hlt hxd]
    refine ((S.resolventFun hb lambda).le_opNorm _).trans ?_
    gcongr
    exact S.resolventFun_norm_le hb hlt
  have hzero : Tendsto
      (fun lambda : ℝ => M / (lambda - omega) * ‖S.generator ⟨x, hxd⟩‖) atTop (nhds 0) := by
    have hshift : Tendsto (fun lambda : ℝ => lambda - omega) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-omega) tendsto_id
    have hdiv : Tendsto (fun lambda : ℝ => M / (lambda - omega)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hshift
    simpa using hdiv.mul_const ‖S.generator ⟨x, hxd⟩‖
  simpa using (squeeze_zero_norm' hbnd hzero).add_const x

/-- **The scaled resolvents converge strongly to the identity.** For a C₀-semigroup with growth
bound `(omega, M)`, `lambda R(lambda) x → x` as `lambda → ∞`, for every `x`. -/
theorem tendsto_smul_resolventFun_apply (hb : S.HasGrowthBound omega M) (x : X) :
    Tendsto (fun lambda : ℝ => lambda • S.resolventFun hb lambda x) atTop (nhds x) := by
  have hbound : ∀ᶠ lambda : ℝ in atTop, ‖lambda • S.resolventFun hb lambda‖ ≤ 2 * M := by
    filter_upwards [eventually_ge_atTop (2 * |omega| + 1)] with lambda hlambda
    exact S.norm_smul_resolventFun_le hb hlambda
  have htend : ∀ y ∈ (S.generator.domain : Set X),
      Tendsto (fun lambda : ℝ => (lambda • S.resolventFun hb lambda) y) atTop
        (nhds ((1 : X →L[ℝ] X) y)) := fun y hy => by
    simpa using S.tendsto_smul_resolventFun_apply_of_mem hb hy
  have hdense : Dense (S.generator.domain : Set X) := by
    rw [S.generator_domain]
    exact S.dense_domain
  simpa using ContinuousLinearMap.tendsto_apply_of_dense (𝕜 := ℝ) (l := atTop)
    (f := fun lambda : ℝ => lambda • S.resolventFun hb lambda) (g := 1) (C := 2 * M)
    hdense hbound htend x

/-- If `f lambda → x`, then applying the scaled resolvent along the way does not change the
limit. This is the induction step behind the convergence of `lambdaⁿ R(lambda)ⁿ`. -/
private theorem tendsto_smul_resolventFun_comp (hb : S.HasGrowthBound omega M) {f : ℝ → X} {x : X}
    (hf : Tendsto f atTop (nhds x)) :
    Tendsto (fun lambda : ℝ => lambda • S.resolventFun hb lambda (f lambda)) atTop (nhds x) := by
  have hbound : ∀ᶠ lambda : ℝ in atTop, ‖lambda • S.resolventFun hb lambda‖ ≤ 2 * M := by
    filter_upwards [eventually_ge_atTop (2 * |omega| + 1)] with lambda hlambda
    exact S.norm_smul_resolventFun_le hb hlambda
  simpa only [smul_apply] using
    (TauCeti.ContinuousLinearMap.tendsto_apply_of_eventually_norm_le hbound
      (S.tendsto_smul_resolventFun_apply hb x) hf)

/-- **The iterated scaled resolvents converge strongly to the identity**:
`lambdaⁿ R(lambda)ⁿ x → x` as `lambda → ∞`. -/
theorem tendsto_pow_smul_resolventFun_pow_apply (hb : S.HasGrowthBound omega M) (n : ℕ) (x : X) :
    Tendsto (fun lambda : ℝ => (lambda ^ n) • ((S.resolventFun hb lambda ^ n) x)) atTop
      (nhds x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      refine (S.tendsto_smul_resolventFun_comp hb ih).congr fun lambda => ?_
      simp only [map_smul, smul_smul, pow_succ', mul_apply_eq_comp]

/-- Density of `D(Aⁿ)` at a prescribed growth bound; the growth bound is only a device for
naming the resolvent, and `StronglyContinuousSemigroup.dense_domainPow` drops it. -/
private theorem dense_domainPow_of (hb : S.HasGrowthBound omega M) (n : ℕ) :
    Dense (domainPow S.generator n : Set X) := by
  intro x
  refine mem_closure_of_tendsto (S.tendsto_pow_smul_resolventFun_pow_apply hb n x) ?_
  filter_upwards [eventually_gt_atTop omega] with lambda hlt
  refine Submodule.smul_mem _ _ ?_
  have heq : S.resolventFun hb lambda = LinearPMap.resolvent S.generator lambda := by
    rw [S.generator_resolvent_eq hb hlt, S.resolventFun_of_lt hb hlt]
  rw [heq]
  exact resolvent_pow_mem_domainPow (S.mem_resolventSet_generator hb hlt) n x

/-- **The iterated generator domains are dense.** For every `n`, the domain `D(Aⁿ)` of the
`n`-th iterate of the infinitesimal generator of a C₀-semigroup is dense in the whole space.

For `n = 1` this is `StronglyContinuousSemigroup.dense_domain`. -/
theorem dense_domainPow (n : ℕ) :
    Dense (domainPow S.generator n : Set X) := by
  obtain ⟨omega, M, hb⟩ := S.existsGrowthBound
  exact S.dense_domainPow_of hb n

end StronglyContinuousSemigroup

end TauCeti.Semigroups

end

end
