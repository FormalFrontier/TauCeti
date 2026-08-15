/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.BoundedGenerator.Perturbation
public import TauCeti.Analysis.Semigroups.Dissipative.Basic
import TauCeti.Analysis.Normed.Operator.Dense
import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# Yosida approximations

This file constructs the bounded approximations used in the generation theorems for strongly
continuous semigroups. For an operator `A` whose resolvent at `lambda > 0` satisfies the
contraction bound, its Yosida approximation is

`A_lambda = lambda ^ 2 R(lambda, A) - lambda I = lambda A R(lambda, A)`.

The resolvent estimate `lambda ‖R(lambda, A)‖ ≤ 1` makes `lambda R(lambda, A)` a contraction.
Splitting the exponential of `t A_lambda` into the commuting scalar and resolvent parts then proves
that `exp (t A_lambda)` is a contraction for every `t ≥ 0`. Thus each approximation generates a
uniformly continuous contraction semigroup. This is the bounded stage of the Yosida construction.

The convergence stage follows. It is stated against a resolvent bound
`‖R(lambda, A)‖ ≤ M / lambda` rather than against dissipativity, because the Hille--Yosida
generation theorem needs the same estimates at a growth constant larger than one: for a densely
defined operator with that bound, `lambda R(lambda, A)` converges strongly to the identity, hence
`A_lambda x` converges to `A x` on `D(A)`.

The compact-time Cauchy property of the associated semigroups needs a second, independent
hypothesis: a uniform bound `‖exp (s A_lambda)‖ ≤ M` on the Yosida exponentials, which the
Duhamel comparison contributes squared, as the factor `M ^ 2`. Those two statements therefore
carry two constants, the resolvent constant, written `K` there, and the exponential constant `M`.
An m-dissipative operator supplies both hypotheses with `K = M = 1`, its exponential bound being
the contraction estimate
`TauCeti.Semigroups.norm_exp_smul_yosidaApproximation_le_one`; under the Hille--Yosida bounds on
all resolvent powers the exponential bound is instead
`TauCeti.Semigroups.norm_exp_smul_yosidaApproximation_le`. The later generation argument defines
the limit of the approximating semigroups.

## Main results

* `TauCeti.Semigroups.yosidaApproximation`: the bounded operator `A_lambda`.
* `TauCeti.Semigroups.yosidaApproximation_apply_eq_smul_apply_resolvent`: the identity
  `A_lambda x = lambda A R(lambda, A) x`.
* `TauCeti.Semigroups.yosidaSemigroup`: the uniformly continuous contraction semigroup generated
  by `A_lambda`.
* `TauCeti.Semigroups.tendsto_smul_resolvent_apply_atTop`: the strong convergence
  `lambda R(lambda, A) x -> x` for a densely defined operator obeying the resolvent bound.
* `TauCeti.Semigroups.tendsto_yosidaApproximation_apply_atTop`: the convergence
  `A_lambda x -> A x` on the domain of `A`.
* `TauCeti.Semigroups.exp_yosidaApproximation_uniformCauchySeqOn_compact` and
  `TauCeti.Semigroups.exp_yosidaApproximation_uniformCauchySeqOn_compact_of_mem`: the Yosida
  semigroups are uniformly Cauchy on compact time intervals, on every vector and on domain
  vectors.
* `TauCeti.Semigroups.IsMDissipative.tendsto_smul_resolvent_apply_atTop`,
  `TauCeti.Semigroups.IsMDissipative.tendsto_yosidaApproximation_apply_atTop` and
  `TauCeti.Semigroups.IsMDissipative.exp_yosidaApproximation_uniformCauchySeqOn_compact`: the
  three convergence statements for an m-dissipative operator, the case `K = M = 1`.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section II.3.5;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Chapter 1.
-/

public section

noncomputable section

namespace TauCeti.Semigroups

open NormedSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The **Yosida approximation** of an unbounded operator `A` at `lambda`:
`A_lambda = lambda ^ 2 R(lambda, A) - lambda I`.

The definition is meaningful when `lambda` belongs to the resolvent set of `A`; its algebraic API
carries that membership explicitly, while the norm estimates carry the resolvent bound they use. -/
def yosidaApproximation (A : X →ₗ.[ℝ] X) (lambda : ℝ) : X →L[ℝ] X :=
  lambda ^ 2 • LinearPMap.resolvent A lambda - lambda • 1

omit [CompleteSpace X] in
/-- Pointwise form of the definition of the Yosida approximation. -/
@[simp]
theorem yosidaApproximation_apply (A : X →ₗ.[ℝ] X) (lambda : ℝ) (x : X) :
    yosidaApproximation A lambda x =
      lambda ^ 2 • LinearPMap.resolvent A lambda x - lambda • x := by
  simp [yosidaApproximation]

omit [CompleteSpace X] in
/-- At a point of the resolvent set, the Yosida approximation is `lambda A R(lambda, A)`
pointwise. -/
theorem yosidaApproximation_apply_eq_smul_apply_resolvent {A : X →ₗ.[ℝ] X} {lambda : ℝ}
    (hlambda : lambda ∈ LinearPMap.resolventSet A) (x : X) :
    yosidaApproximation A lambda x = lambda • A ⟨LinearPMap.resolvent A lambda x,
      LinearPMap.resolvent_mem_domain hlambda x⟩ := by
  rw [yosidaApproximation_apply, LinearPMap.apply_resolvent hlambda]
  module

omit [CompleteSpace X] in
/-- Yosida approximations at two resolvent points commute. -/
theorem yosidaApproximation_comm {A : X →ₗ.[ℝ] X} {lambda mu : ℝ}
    (hlambda : lambda ∈ LinearPMap.resolventSet A)
    (hmu : mu ∈ LinearPMap.resolventSet A) :
    Commute (yosidaApproximation A lambda) (yosidaApproximation A mu) := by
  have hRR : Commute
      (lambda ^ 2 • LinearPMap.resolvent A lambda)
      (mu ^ 2 • LinearPMap.resolvent A mu) :=
    let h : Commute (LinearPMap.resolvent A lambda) (LinearPMap.resolvent A mu) :=
      LinearPMap.resolvent_comm hlambda hmu
    h.smul_left (lambda ^ 2) |>.smul_right (mu ^ 2)
  have hR_one : Commute
      (lambda ^ 2 • LinearPMap.resolvent A lambda)
      (mu • (1 : X →L[ℝ] X)) :=
    (Commute.one_right _).smul_right mu
  have hone_R : Commute
      (lambda • (1 : X →L[ℝ] X))
      (mu ^ 2 • LinearPMap.resolvent A mu) :=
    (Commute.one_left _).smul_left lambda
  have hone_one : Commute
      (lambda • (1 : X →L[ℝ] X))
      (mu • (1 : X →L[ℝ] X)) :=
    (Commute.refl (1 : X →L[ℝ] X)).smul_left lambda |>.smul_right mu
  rw [yosidaApproximation, yosidaApproximation]
  exact (hRR.sub_left hone_R).sub_right (hR_one.sub_left hone_one)

omit [CompleteSpace X] in
/-- The Yosida approximation has the elementary bound `‖A_lambda‖ ≤ 2 lambda`. -/
theorem norm_yosidaApproximation_le {A : X →ₗ.[ℝ] X} {lambda : ℝ}
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) :
    ‖yosidaApproximation A lambda‖ ≤ 2 * lambda := by
  have hscaled : ‖lambda • (lambda • LinearPMap.resolvent A lambda)‖ ≤ lambda := by
    calc
      ‖lambda • (lambda • LinearPMap.resolvent A lambda)‖
          = lambda * ‖lambda • LinearPMap.resolvent A lambda‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
      _ ≤ lambda * 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
        gcongr
      _ = lambda := mul_one _
  have hone : ‖lambda • (1 : X →L[ℝ] X)‖ ≤ lambda := by
    calc
      ‖lambda • (1 : X →L[ℝ] X)‖ = lambda * ‖(1 : X →L[ℝ] X)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
      _ ≤ lambda * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ = lambda := mul_one _
  calc
    ‖yosidaApproximation A lambda‖
        = ‖lambda • (lambda • LinearPMap.resolvent A lambda) - lambda • (1 : X →L[ℝ] X)‖ := by
      rw [yosidaApproximation, smul_smul, pow_two]
    _ ≤ ‖lambda • (lambda • LinearPMap.resolvent A lambda)‖ + ‖lambda • (1 : X →L[ℝ] X)‖ :=
      norm_sub_le _ _
    _ ≤ lambda + lambda := add_le_add hscaled hone
    _ = 2 * lambda := (two_mul lambda).symm

/-- Split the exponential of a Yosida approximation into its commuting scalar and resolvent
factors:
`exp (t A_lambda) = exp (-t lambda I) exp (t lambda² R(lambda, A))`. -/
theorem exp_yosidaApproximation {A : X →ₗ.[ℝ] X} (lambda t : ℝ) :
    exp (t • yosidaApproximation A lambda) =
      exp ((-(t * lambda)) • (1 : X →L[ℝ] X)) *
        exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda) := by
  have hsplit : t • yosidaApproximation A lambda =
      (-(t * lambda)) • (1 : X →L[ℝ] X) +
        (t * lambda ^ 2) • LinearPMap.resolvent A lambda := by
    rw [yosidaApproximation, smul_sub]
    module
  rw [hsplit]
  let +nondep : NormedAlgebra ℚ (X →L[ℝ] X) := .restrictScalars ℚ ℝ _
  exact exp_add_of_commute (Commute.one_left _ |>.smul_left _ |>.smul_right _)

/-- The exponential of a positive-time multiple of a Yosida approximation is contractive. -/
theorem norm_exp_smul_yosidaApproximation_le_one {A : X →ₗ.[ℝ] X} {lambda t : ℝ}
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) (ht : 0 ≤ t) :
    ‖exp (t • yosidaApproximation A lambda)‖ ≤ 1 := by
  let +nondep : NormedAlgebra ℚ (X →L[ℝ] X) := .restrictScalars ℚ ℝ _
  calc
    ‖exp (t • yosidaApproximation A lambda)‖ =
        ‖exp ((-(t * lambda)) • (1 : X →L[ℝ] X)) *
          exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)‖ := by
      rw [exp_yosidaApproximation]
    _ ≤ ‖exp ((-(t * lambda)) • (1 : X →L[ℝ] X))‖ *
          ‖exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)‖ := norm_mul_le _ _
    _ ≤ Real.exp (-(t * lambda)) *
          Real.exp ‖(t * lambda ^ 2) • LinearPMap.resolvent A lambda‖ := by
      gcongr
      · exact ContinuousLinearMap.norm_exp_smul_one_le _
      · exact TauCeti.norm_exp_le_exp_norm ContinuousLinearMap.norm_id_le _
    _ ≤ Real.exp (-(t * lambda)) * Real.exp (t * lambda) := by
      gcongr
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ t * lambda ^ 2)]
      calc
        t * lambda ^ 2 * ‖LinearPMap.resolvent A lambda‖
            = t * lambda * (lambda * ‖LinearPMap.resolvent A lambda‖) := by ring
        _ ≤ t * lambda * 1 := by gcongr
        _ = t * lambda := mul_one _
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The uniformly continuous contraction semigroup generated by the Yosida approximation. -/
def yosidaSemigroup (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1)
    (hlambda : 0 < lambda) : ContractionSemigroup X where
  toStronglyContinuousSemigroup := StronglyContinuousSemigroup.ofBounded
    (yosidaApproximation A lambda)
  contracting t := by
    -- The `contracting` field exposes the raw `toFun`; it is definitionally the same function
    -- as the semigroup coercion used by `ofBounded_apply`.
    calc
      ‖(StronglyContinuousSemigroup.ofBounded (yosidaApproximation A lambda)).toFun t‖ =
          ‖exp ((t : ℝ) • yosidaApproximation A lambda)‖ :=
        congrArg norm (StronglyContinuousSemigroup.ofBounded_apply _ t)
      _ ≤ 1 := norm_exp_smul_yosidaApproximation_le_one hres hlambda t.property

/-- The C₀-semigroup underlying the Yosida semigroup is the bounded-generator semigroup of the
Yosida approximation. -/
@[simp]
theorem yosidaSemigroup_toStronglyContinuousSemigroup (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) :
    (yosidaSemigroup A lambda hres hlambda).toStronglyContinuousSemigroup =
      StronglyContinuousSemigroup.ofBounded (yosidaApproximation A lambda) := by
  simp [yosidaSemigroup]

/-- The Yosida semigroup is the exponential of the Yosida approximation. -/
@[simp]
theorem yosidaSemigroup_apply (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) (t : NNReal) :
    yosidaSemigroup A lambda hres hlambda t = exp ((t : ℝ) • yosidaApproximation A lambda) := by
  rw [← ContractionSemigroup.toStronglyContinuousSemigroup_apply,
    yosidaSemigroup_toStronglyContinuousSemigroup, StronglyContinuousSemigroup.ofBounded_apply]

/-- The Yosida semigroup is continuous in operator norm, not merely strongly continuous. -/
theorem continuous_yosidaSemigroup (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) :
    Continuous fun t : NNReal => yosidaSemigroup A lambda hres hlambda t := by
  refine (StronglyContinuousSemigroup.ofBounded_continuous
    (yosidaApproximation A lambda)).congr fun t => ?_
  exact (StronglyContinuousSemigroup.ofBounded_apply _ t).trans
    (yosidaSemigroup_apply A lambda hres hlambda t).symm

/-- The generator of the Yosida semigroup is the everywhere-defined Yosida approximation. -/
theorem yosidaSemigroup_generator (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) :
    (yosidaSemigroup A lambda hres hlambda).toStronglyContinuousSemigroup.generator =
      (yosidaApproximation A lambda : X →ₗ[ℝ] X).toPMap ⊤ := by
  rw [yosidaSemigroup_toStronglyContinuousSemigroup,
    StronglyContinuousSemigroup.ofBounded_generator]

/-! ## Strong convergence of the approximations

The estimates of this section carry the resolvent bound `‖R(lambda, A)‖ ≤ M / lambda` as an
explicit hypothesis rather than assuming dissipativity, since the Hille--Yosida generation theorem
needs them at a growth constant `M` larger than one. An m-dissipative operator is the case
`M = 1`, recorded by the `IsMDissipative` specializations at the end of the file. -/

omit [CompleteSpace X] in
/-- On the domain of `A`, the scaled resolvent differs from the identity by at most
`M ‖A x‖ / lambda`:

`‖lambda R(lambda, A) x - x‖ ≤ M ‖A x‖ / lambda`,

whenever `lambda` is a resolvent point with `‖R(lambda, A)‖ ≤ M / lambda`. This is the
quantitative core of the strong convergence `lambda R(lambda, A) -> I`. -/
theorem norm_smul_resolvent_apply_sub_self_le {A : X →ₗ.[ℝ] X} {lambda M : ℝ}
    (hlambda : lambda ∈ LinearPMap.resolventSet A)
    (hbound : ‖LinearPMap.resolvent A lambda‖ ≤ M / lambda) (x : A.domain) :
    ‖lambda • LinearPMap.resolvent A lambda (x : X) - (x : X)‖ ≤ M * ‖A x‖ / lambda := by
  have hresolvent :
      lambda • LinearPMap.resolvent A lambda (x : X) - (x : X) =
        LinearPMap.resolvent A lambda (A x) := by
    have hleft := LinearPMap.resolvent_smul_sub_apply hlambda x
    rw [map_sub, map_smul] at hleft
    rw [sub_eq_iff_eq_add] at hleft
    rw [hleft]
    abel
  rw [hresolvent]
  calc
    ‖LinearPMap.resolvent A lambda (A x)‖
        ≤ ‖LinearPMap.resolvent A lambda‖ * ‖A x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ M / lambda * ‖A x‖ := by gcongr
    _ = M * ‖A x‖ / lambda := by ring

omit [CompleteSpace X] in
/-- On `D(A)`, `lambda R(lambda, A) x` tends to `x` as `lambda -> +∞` under the resolvent bound
`‖R(lambda, A)‖ ≤ M / lambda`. Density of the domain is not needed for this domain-restricted
form. -/
theorem tendsto_smul_resolvent_apply_atTop_of_mem {A : X →ₗ.[ℝ] X} {M : ℝ}
    (hres : ∀ lambda : ℝ, 0 < lambda → lambda ∈ LinearPMap.resolventSet A)
    (hbound : ∀ lambda : ℝ, 0 < lambda → ‖LinearPMap.resolvent A lambda‖ ≤ M / lambda)
    (x : A.domain) :
    Filter.Tendsto (fun lambda : ℝ => lambda • LinearPMap.resolvent A lambda (x : X))
      Filter.atTop (nhds (x : X)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  have hquotient : Filter.Tendsto (fun lambda : ℝ => M * ‖A x‖ / lambda)
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  rw [Metric.tendsto_atTop] at hquotient
  obtain ⟨N, hN⟩ := hquotient epsilon hepsilon
  refine ⟨max N 1, fun lambda hlambda => ?_⟩
  have hlambda_pos : 0 < lambda := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hlambda)
  rw [dist_eq_norm]
  refine (norm_smul_resolvent_apply_sub_self_le (hres lambda hlambda_pos)
    (hbound lambda hlambda_pos) x).trans_lt ?_
  have hquotient_lt := hN lambda (le_trans (le_max_left _ _) hlambda)
  rw [Real.dist_eq, sub_zero] at hquotient_lt
  exact lt_of_le_of_lt (le_abs_self _) hquotient_lt

omit [CompleteSpace X] in
/-- Under the resolvent bound `‖R(lambda, A)‖ ≤ M / lambda` at a positive `lambda`, the scaled
resolvent `lambda R(lambda, A)` has norm at most `M`. -/
theorem norm_smul_resolvent_le {A : X →ₗ.[ℝ] X} {lambda M : ℝ} (hlambda : 0 < lambda)
    (hbound : ‖LinearPMap.resolvent A lambda‖ ≤ M / lambda) :
    ‖lambda • LinearPMap.resolvent A lambda‖ ≤ M := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
  calc
    lambda * ‖LinearPMap.resolvent A lambda‖ ≤ lambda * (M / lambda) := by gcongr
    _ = M := by field_simp

omit [CompleteSpace X] in
/-- For a densely defined operator obeying the resolvent bound `‖R(lambda, A)‖ ≤ M / lambda`, the
scaled resolvents converge strongly to the identity on the whole Banach space:

`lambda R(lambda, A) x -> x` as `lambda -> +∞`.

The uniform bound `‖lambda R(lambda, A)‖ ≤ M` extends the domain estimate to all vectors by
density. -/
theorem tendsto_smul_resolvent_apply_atTop {A : X →ₗ.[ℝ] X} {M : ℝ}
    (hres : ∀ lambda : ℝ, 0 < lambda → lambda ∈ LinearPMap.resolventSet A)
    (hbound : ∀ lambda : ℝ, 0 < lambda → ‖LinearPMap.resolvent A lambda‖ ≤ M / lambda)
    (hdense : Dense (A.domain : Set X)) (x : X) :
    Filter.Tendsto (fun lambda : ℝ => lambda • LinearPMap.resolvent A lambda x)
      Filter.atTop (nhds x) := by
  refine ContinuousLinearMap.tendsto_apply_of_dense (𝕜 := ℝ)
    (f := fun lambda => lambda • LinearPMap.resolvent A lambda)
    (g := (1 : X →L[ℝ] X)) (C := M) hdense ?_ ?_ x
  · filter_upwards [Filter.eventually_gt_atTop 0] with lambda hlambda
    exact norm_smul_resolvent_le hlambda (hbound lambda hlambda)
  · intro y hy
    simpa only [smul_apply, one_apply_eq_self] using
      tendsto_smul_resolvent_apply_atTop_of_mem hres hbound (⟨y, hy⟩ : A.domain)

omit [CompleteSpace X] in
/-- At a resolvent point, the Yosida approximation acts on `x ∈ D(A)` as
`A_lambda x = lambda R(lambda, A) (A x)`. -/
theorem yosidaApproximation_apply_eq_smul_resolvent_apply {A : X →ₗ.[ℝ] X} {lambda : ℝ}
    (hlambda : lambda ∈ LinearPMap.resolventSet A) (x : A.domain) :
    yosidaApproximation A lambda (x : X) =
      lambda • LinearPMap.resolvent A lambda (A x) := by
  rw [yosidaApproximation_apply_eq_smul_apply_resolvent hlambda]
  exact congrArg (lambda • ·) (LinearPMap.resolvent_apply_comm hlambda x).symm

omit [CompleteSpace X] in
/-- Under the resolvent bound `‖R(lambda, A)‖ ≤ M / lambda` and density of the domain, the Yosida
approximations converge strongly to the original operator on its domain: `A_lambda x -> A x` for
every `x ∈ D(A)`. -/
theorem tendsto_yosidaApproximation_apply_atTop {A : X →ₗ.[ℝ] X} {M : ℝ}
    (hres : ∀ lambda : ℝ, 0 < lambda → lambda ∈ LinearPMap.resolventSet A)
    (hbound : ∀ lambda : ℝ, 0 < lambda → ‖LinearPMap.resolvent A lambda‖ ≤ M / lambda)
    (hdense : Dense (A.domain : Set X)) (x : A.domain) :
    Filter.Tendsto (fun lambda : ℝ => yosidaApproximation A lambda (x : X))
      Filter.atTop (nhds (A x)) := by
  refine (tendsto_smul_resolvent_apply_atTop hres hbound hdense (A x)).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with lambda hlambda
  exact (yosidaApproximation_apply_eq_smul_resolvent_apply (hres lambda hlambda) x).symm

/-! ## Compact-time Cauchy convergence of the approximating semigroups

The two statements below take independent resolvent and exponential bounds, with constants `K`
and `M` respectively. For a dissipative operator the exponential bound is the contraction estimate
`TauCeti.Semigroups.norm_exp_smul_yosidaApproximation_le_one`; under the Hille--Yosida resolvent
power bounds for a general growth constant it is
`TauCeti.Semigroups.norm_exp_smul_yosidaApproximation_le`. -/

/-- The bounded Yosida semigroups are Cauchy on domain vectors, uniformly on every compact time
interval. Explicitly, for `T ≥ 0`, the vectors `exp (t A_lambda) x` are uniformly Cauchy for
`0 ≤ t ≤ T` as `lambda -> +∞`, whenever `x ∈ D(A)`.

The resolvent bound has constant `K`, while the independent exponential bound has constant `M`.
The comparison estimate reduces the result to the convergence `A_lambda x -> A x` proved above,
at the cost of the factor `M ^ 2` from the two exponential factors of the Duhamel formula. -/
theorem exp_yosidaApproximation_uniformCauchySeqOn_compact_of_mem {A : X →ₗ.[ℝ] X} {K M : ℝ}
    (hres : ∀ lambda : ℝ, 0 < lambda → lambda ∈ LinearPMap.resolventSet A)
    (hbound : ∀ lambda : ℝ, 0 < lambda → ‖LinearPMap.resolvent A lambda‖ ≤ K / lambda)
    (hexp : ∀ lambda : ℝ, 0 < lambda → ∀ s : ℝ, 0 ≤ s →
      ‖exp (s • yosidaApproximation A lambda)‖ ≤ M)
    (hdense : Dense (A.domain : Set X)) (x : A.domain) {T : ℝ} (hT : 0 ≤ T) :
    UniformCauchySeqOn
      (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) (x : X))
      Filter.atTop (Set.Icc 0 T) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro epsilon hepsilon
  let C : ℝ := M * M * (T + 1) + 1
  have hC : 0 < C := by
    have : 0 ≤ M * M * (T + 1) := mul_nonneg (mul_self_nonneg M) (by linarith)
    dsimp only [C]
    linarith
  let delta : ℝ := epsilon / (2 * C)
  have hdelta : 0 < delta := div_pos hepsilon (mul_pos zero_lt_two hC)
  have hconv := tendsto_yosidaApproximation_apply_atTop hres hbound hdense x
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv delta hdelta
  refine ⟨max N 1, fun lambda hlambda mu hmu t ht => ?_⟩
  rw [dist_eq_norm]
  have hlambda_pos : 0 < lambda :=
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hlambda)
  have hmu_pos : 0 < mu :=
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hmu)
  have hlambda_close := hN lambda (le_trans (le_max_left _ _) hlambda)
  have hmu_close := hN mu (le_trans (le_max_left _ _) hmu)
  have hdiff :
      ‖(yosidaApproximation A lambda - yosidaApproximation A mu) (x : X)‖ < 2 * delta := by
    rw [sub_apply, ← dist_eq_norm]
    exact (dist_triangle_right
      (yosidaApproximation A lambda (x : X))
      (yosidaApproximation A mu (x : X)) (A x)).trans_lt (by linarith)
  have hcompare := norm_exp_smul_sub_exp_smul_apply_le_of_commute
    (yosidaApproximation A lambda) (yosidaApproximation A mu)
    (yosidaApproximation_comm (hres lambda hlambda_pos) (hres mu hmu_pos))
    (fun s hs => hexp lambda hlambda_pos s hs) (fun s hs => hexp mu hmu_pos s hs)
    ht.1 (x : X)
  calc
    ‖exp (t • yosidaApproximation A lambda) (x : X) -
        exp (t • yosidaApproximation A mu) (x : X)‖
        ≤ M * M * t * ‖(yosidaApproximation A lambda - yosidaApproximation A mu) (x : X)‖ :=
      hcompare
    _ ≤ C * ‖(yosidaApproximation A lambda - yosidaApproximation A mu) (x : X)‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have hmono : M * M * t ≤ M * M * (T + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [ht.2]) (mul_self_nonneg M)
      dsimp only [C]
      linarith
    _ < C * (2 * delta) := mul_lt_mul_of_pos_left hdiff hC
    _ = epsilon := by
      dsimp only [delta]
      field_simp

/-- The bounded Yosida semigroups are Cauchy uniformly on every compact time interval, on every
vector of the Banach space.

This is the compact-time Cauchy estimate from which a candidate pointwise limit family is defined;
later arguments establish its semigroup structure and identify its generator as `A`. The domain
case is `TauCeti.Semigroups.exp_yosidaApproximation_uniformCauchySeqOn_compact_of_mem`; the uniform
bound `‖exp (s A_lambda)‖ ≤ M` extends it to the whole space by density of `D(A)`, independently
of the resolvent-bound constant `K`. -/
theorem exp_yosidaApproximation_uniformCauchySeqOn_compact {A : X →ₗ.[ℝ] X} {K M : ℝ}
    (hres : ∀ lambda : ℝ, 0 < lambda → lambda ∈ LinearPMap.resolventSet A)
    (hbound : ∀ lambda : ℝ, 0 < lambda → ‖LinearPMap.resolvent A lambda‖ ≤ K / lambda)
    (hexp : ∀ lambda : ℝ, 0 < lambda → ∀ s : ℝ, 0 ≤ s →
      ‖exp (s • yosidaApproximation A lambda)‖ ≤ M)
    (hdense : Dense (A.domain : Set X)) (x : X) {T : ℝ} (hT : 0 ≤ T) :
    UniformCauchySeqOn
      (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) x)
      Filter.atTop (Set.Icc 0 T) := by
  refine ContinuousLinearMap.uniformCauchySeqOn_apply_of_dense (𝕜 := ℝ)
    (f := fun lambda t => exp (t • yosidaApproximation A lambda)) (C := M) hdense ?_ ?_ x
  · filter_upwards [Filter.eventually_gt_atTop 0] with lambda hlambda t ht
    exact hexp lambda hlambda t ht.1
  · intro y hy
    exact exp_yosidaApproximation_uniformCauchySeqOn_compact_of_mem hres hbound hexp hdense
      (⟨y, hy⟩ : A.domain) hT

/-! ## The m-dissipative case

An m-dissipative operator has every positive `lambda` in its resolvent set with
`‖R(lambda, A)‖ ≤ 1 / lambda`, and its Yosida exponentials are contractions, so it supplies the
hypotheses of the results above with both constants equal to one. -/

namespace IsMDissipative

variable {A : X →ₗ.[ℝ] X}

/-- For a densely defined m-dissipative operator, the scaled resolvents converge strongly to the
identity on the whole Banach space: `lambda R(lambda, A) x -> x` as `lambda -> +∞`. -/
theorem tendsto_smul_resolvent_apply_atTop (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) (x : X) :
    Filter.Tendsto (fun lambda : ℝ => lambda • LinearPMap.resolvent A lambda x)
      Filter.atTop (nhds x) :=
  _root_.TauCeti.Semigroups.tendsto_smul_resolvent_apply_atTop (M := 1)
    (fun _ h => hA.mem_resolventSet h)
    (fun _ h => by simpa [one_div] using hA.norm_resolvent_le h) hdense x

/-- For a densely defined m-dissipative operator, the Yosida approximations converge strongly to
the original operator on its domain: `A_lambda x -> A x` for every `x ∈ D(A)`. -/
theorem tendsto_yosidaApproximation_apply_atTop (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) (x : A.domain) :
    Filter.Tendsto (fun lambda : ℝ => yosidaApproximation A lambda (x : X))
      Filter.atTop (nhds (A x)) :=
  _root_.TauCeti.Semigroups.tendsto_yosidaApproximation_apply_atTop (M := 1)
    (fun _ h => hA.mem_resolventSet h)
    (fun _ h => by simpa [one_div] using hA.norm_resolvent_le h) hdense x

/-- For a densely defined m-dissipative operator, the bounded Yosida semigroups are Cauchy
uniformly on every compact time interval, on every vector of the Banach space. This is the
compact-time Cauchy estimate from which the contraction semigroup generated by `A` is built. -/
theorem exp_yosidaApproximation_uniformCauchySeqOn_compact (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) (x : X) {T : ℝ} (hT : 0 ≤ T) :
    UniformCauchySeqOn
      (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) x)
      Filter.atTop (Set.Icc 0 T) :=
  _root_.TauCeti.Semigroups.exp_yosidaApproximation_uniformCauchySeqOn_compact (K := 1) (M := 1)
    (fun _ h => hA.mem_resolventSet h)
    (fun _ h => by simpa [one_div] using hA.norm_resolvent_le h)
    (fun _ h _ hs => norm_exp_smul_yosidaApproximation_le_one
      (hA.mul_norm_resolvent_le_one h) h hs)
    hdense x hT

end IsMDissipative

end TauCeti.Semigroups

end
