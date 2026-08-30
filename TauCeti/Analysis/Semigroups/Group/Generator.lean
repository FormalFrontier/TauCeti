/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.Basic
public import TauCeti.Analysis.Semigroups.BoundedGenerator.Basic
-- Non-public: the exponential norm bound supplies the growth bound of `ofBounded`.
import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# The generator of a strongly continuous group

The generator of a C₀-group `U` is the generator of its forward semigroup. What is new on a
group is that the difference quotient converges from *both* sides: the time-reversed group
`U.reflect` has the same generator domain and the negated generator
(`TauCeti.Semigroups.StronglyContinuousGroup.reflect_generator`), and combining the two
one-sided limits upgrades the right derivative of an orbit to a genuine two-sided derivative on
all of `ℝ`. So for `x ∈ D(A)` the orbit `u (t) = U t x` is a classical solution of `u' = A u`
on the whole line, not just on `[0, ∞)`.

Because a semigroup is determined by its generator, so is a group: the generator fixes the
forward half directly and the backward half through `U.reflect`.

## Main results

* `TauCeti.Semigroups.StronglyContinuousGroup.reflect_generator`: the generator of the
  time-reversed group is `-A`, on the same domain.
* `TauCeti.Semigroups.StronglyContinuousGroup.hasDerivAt`: for `x ∈ D(A)` the orbit
  `t ↦ U t x` is differentiable at every real time, with derivative `U t (A x)`.
* `TauCeti.Semigroups.StronglyContinuousGroup.map_mem_domain` and
  `TauCeti.Semigroups.StronglyContinuousGroup.generator_map`: `D(A)` is invariant under the
  whole group and `A` commutes with it.
* `TauCeti.Semigroups.StronglyContinuousGroup.eq_of_generator_eq`: a C₀-group is determined by
  its generator.
* `TauCeti.Semigroups.StronglyContinuousGroup.ofBounded`: the C₀-group `t ↦ exp (t • A)` of a
  bounded operator, with generator `A`; every C₀-group whose generator is `A` on all of `X` is of
  this form.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section II.3.11;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Section 1.6.
-/

public section

noncomputable section

open scoped Topology NNReal
open Filter NormedSpace

namespace TauCeti.Semigroups

namespace StronglyContinuousGroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The domain `D(A)` of the generator of a C₀-group: the generator domain of its forward
semigroup. -/
def domain (U : StronglyContinuousGroup X) : Submodule ℝ X := U.toSemigroup.domain

/-- The infinitesimal generator of a C₀-group, as an unbounded operator: the generator of its
forward semigroup. The two-sided law makes the defining limit two-sided as well
(`TauCeti.Semigroups.StronglyContinuousGroup.hasDerivAt`). -/
def generator (U : StronglyContinuousGroup X) : X →ₗ.[ℝ] X := U.toSemigroup.generator

theorem domain_def (U : StronglyContinuousGroup X) : U.domain = U.toSemigroup.domain := (rfl)

theorem generator_def (U : StronglyContinuousGroup X) :
    U.generator = U.toSemigroup.generator := (rfl)

@[simp]
theorem generator_domain (U : StronglyContinuousGroup X) : U.generator.domain = U.domain := by
  rw [generator_def, domain_def, StronglyContinuousSemigroup.generator_domain]

/-! ## The defining limit -/

/-- On positive times the forward semigroup's difference quotient is the group's. -/
private theorem genQuot_eventuallyEq (U : StronglyContinuousGroup X) (x : X) :
    (fun t : ℝ => (1 / t) • (U.toSemigroup.realOperator t x - x))
      =ᶠ[𝓝[>] (0 : ℝ)] fun t : ℝ => (1 / t) • (U t x - x) := by
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [U.toSemigroup_realOperator_of_nonneg (le_of_lt ht)]

/-- A vector lies in the generator domain iff its difference quotient `(U t x - x)/t` converges
as `t → 0⁺`. -/
theorem mem_domain_iff_tendsto (U : StronglyContinuousGroup X) (x : X) :
    x ∈ U.domain ↔ ∃ y, Tendsto (fun t : ℝ => (1 / t) • (U t x - x))
      (𝓝[>] (0 : ℝ)) (𝓝 y) := by
  rw [domain_def, U.toSemigroup.mem_domain_iff_tendsto]
  exact exists_congr fun y => tendsto_congr' (U.genQuot_eventuallyEq x)

/-- Characteristic property of the generator: for `x ∈ D(A)` the difference quotient converges
to `A x` as `t → 0⁺`. -/
theorem generator_tendsto (U : StronglyContinuousGroup X) (x : U.domain) :
    Tendsto (fun t : ℝ => (1 / t) • (U t (x : X) - (x : X))) (𝓝[>] (0 : ℝ))
      (𝓝 (U.generator ⟨(x : X), by rw [U.generator_domain]; exact x.property⟩)) :=
  (tendsto_congr' (U.genQuot_eventuallyEq (x : X))).mp (U.toSemigroup.generator_tendsto x)

/-- Eliminator for the generator: if the difference quotient of an `x ∈ D(A)` converges to `y`,
then `A x = y`. -/
theorem generator_eq_of_tendsto (U : StronglyContinuousGroup X) {x : X} (hx : x ∈ U.domain)
    {y : X} (h : Tendsto (fun t : ℝ => (1 / t) • (U t x - x)) (𝓝[>] (0 : ℝ)) (𝓝 y)) :
    U.generator ⟨x, by rw [U.generator_domain]; exact hx⟩ = y :=
  U.toSemigroup.generator_eq_of_tendsto hx ((tendsto_congr' (U.genQuot_eventuallyEq x)).mpr h)

/-- The difference quotient based at `U r x` is `U r` applied to the difference quotient based
at `x`. -/
private theorem tendsto_genQuot_map (U : StronglyContinuousGroup X) (r : ℝ) {x y : X}
    (h : Tendsto (fun t : ℝ => (1 / t) • (U t x - x)) (𝓝[>] (0 : ℝ)) (𝓝 y)) :
    Tendsto (fun t : ℝ => (1 / t) • (U t (U r x) - U r x))
      (𝓝[>] (0 : ℝ)) (𝓝 (U r y)) := by
  refine ((U r).continuous.continuousAt.tendsto.comp h).congr' ?_
  filter_upwards with t
  simp only [Function.comp_apply, U.map_comm t r x, map_smul, map_sub]

/-- **The generator domain is invariant under the whole group**, at negative times as well as
positive ones. -/
theorem map_mem_domain (U : StronglyContinuousGroup X) (x : U.domain) (t : ℝ) :
    U t (x : X) ∈ U.domain := by
  obtain ⟨y, hy⟩ := (U.mem_domain_iff_tendsto (x : X)).mp x.property
  exact (U.mem_domain_iff_tendsto _).mpr ⟨U t y, U.tendsto_genQuot_map t hy⟩

/-- **The generator commutes with the group.** -/
theorem generator_map (U : StronglyContinuousGroup X) (x : U.domain) (t : ℝ) :
    U.generator ⟨U t (x : X), by
      rw [U.generator_domain]; exact U.map_mem_domain x t⟩
      = U t (U.generator ⟨(x : X), by rw [U.generator_domain]; exact x.property⟩) :=
  U.generator_eq_of_tendsto (U.map_mem_domain x t)
    (U.tendsto_genQuot_map t (U.generator_tendsto x))

/-- The positive-time difference quotient at `0` extracted from a two-sided derivative of an
orbit. -/
theorem tendsto_of_hasDerivAt_zero (U : StronglyContinuousGroup X) {y c : X}
    (h : HasDerivAt (fun s : ℝ => U s y) c 0) :
    Tendsto (fun t : ℝ => (1 / t) • (U t y - y)) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  rw [hasDerivAt_iff_tendsto_slope] at h
  have hmono : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono _ fun z hz => ne_of_gt hz
  refine (h.mono_left hmono).congr fun t => ?_
  rw [slope_def_module, sub_zero, U.map_zero_apply, one_div]

/-- A vector whose orbit is differentiable at `0` belongs to the generator domain. -/
theorem mem_domain_of_hasDerivAt_zero (U : StronglyContinuousGroup X) {x y : X}
    (h : HasDerivAt (fun t : ℝ => U t x) y 0) : x ∈ U.domain :=
  (U.mem_domain_iff_tendsto x).mpr ⟨y, U.tendsto_of_hasDerivAt_zero h⟩

/-- The generator value is the derivative at `0` of the orbit. -/
theorem generator_eq_of_hasDerivAt_zero (U : StronglyContinuousGroup X) {x y : X}
    (h : HasDerivAt (fun t : ℝ => U t x) y 0) :
    U.generator ⟨x, by rw [U.generator_domain]; exact U.mem_domain_of_hasDerivAt_zero h⟩ = y :=
  U.generator_eq_of_tendsto (U.mem_domain_of_hasDerivAt_zero h)
    (U.tendsto_of_hasDerivAt_zero h)

variable [CompleteSpace X]

/-! ## Time reversal -/

/-- The difference quotient of the time-reversed group converges to the negative of the limit
for `U`: on positive times the two quotients differ by the operator `U (-t)` and a sign, while the
operator converges strongly to the identity. -/
private theorem tendsto_reflect_genQuot (U : StronglyContinuousGroup X) {x y : X}
    (h : Tendsto (fun t : ℝ => (1 / t) • (U t x - x)) (𝓝[>] (0 : ℝ)) (𝓝 y)) :
    Tendsto (fun t : ℝ => (1 / t) • (U.reflect t x - x)) (𝓝[>] (0 : ℝ)) (𝓝 (-y)) := by
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hjoint := U.tendsto_apply hneg h.neg
  rw [U.map_zero_apply] at hjoint
  refine hjoint.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t _
  rw [reflect_apply, map_neg, ContinuousLinearMap.map_smul, map_sub,
    U.map_neg_apply_map_apply, ← smul_neg, neg_sub]

/-- **The generator domain is invariant under time reversal.** -/
@[simp]
theorem reflect_domain (U : StronglyContinuousGroup X) : U.reflect.domain = U.domain := by
  have key : ∀ V : StronglyContinuousGroup X, ∀ x ∈ V.domain, x ∈ V.reflect.domain := by
    intro V x hx
    obtain ⟨y, hy⟩ := (V.mem_domain_iff_tendsto x).mp hx
    exact (V.reflect.mem_domain_iff_tendsto x).mpr ⟨-y, V.tendsto_reflect_genQuot hy⟩
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxx := key U.reflect x hx
    rwa [reflect_reflect] at hxx
  · intro x hx
    exact key U x hx

/-- **The generator of the time-reversed group is the negative of the generator**, on the same
domain. This is the two-sided statement that makes the backward half of a C₀-group accessible
to the semigroup API. -/
@[simp]
theorem reflect_generator (U : StronglyContinuousGroup X) :
    U.reflect.generator = -U.generator := by
  refine LinearPMap.ext ?_ ?_
  · rw [LinearPMap.neg_domain, U.generator_domain, U.reflect.generator_domain, U.reflect_domain]
  · intro x _ hg
    rw [LinearPMap.neg_domain, U.generator_domain] at hg
    rw [LinearPMap.neg_apply]
    exact U.reflect.generator_eq_of_tendsto (by rw [U.reflect_domain]; exact hg)
      (U.tendsto_reflect_genQuot (U.generator_tendsto ⟨x, hg⟩))

/-! ## Two-sided differentiability of the orbits -/

/-- For a domain vector the difference quotient converges from the left as well, to the same
limit: the left quotient is minus the reversed group's right quotient, which converges to
`-A x`. -/
theorem generator_tendsto_nhdsLT (U : StronglyContinuousGroup X) (x : U.domain) :
    Tendsto (fun t : ℝ => (1 / t) • (U t (x : X) - (x : X))) (𝓝[<] (0 : ℝ))
      (𝓝 (U.generator ⟨(x : X), by rw [U.generator_domain]; exact x.property⟩)) := by
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Set.mem_Ioi.mpr (neg_pos.mpr (Set.mem_Iio.mp ht))
  have h := ((U.tendsto_reflect_genQuot (U.generator_tendsto x)).comp hneg).neg
  rw [neg_neg] at h
  refine h.congr fun t => ?_
  simp only [Function.comp_apply, reflect_apply, neg_neg]
  rw [one_div, one_div, inv_neg, neg_smul, neg_neg]

/-- **The orbit of a domain vector is two-sidedly differentiable at `0`.** -/
theorem hasDerivAt_zero (U : StronglyContinuousGroup X) (x : U.domain) :
    HasDerivAt (fun t : ℝ => U t (x : X))
      (U.generator ⟨(x : X), by rw [U.generator_domain]; exact x.property⟩) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hslope : slope (fun t : ℝ => U t (x : X)) 0
      = fun t : ℝ => (1 / t) • (U t (x : X) - (x : X)) := by
    funext t
    rw [slope_def_module, sub_zero, U.map_zero_apply, one_div]
  rw [hslope, ← nhdsLT_sup_nhdsGT, tendsto_sup]
  exact ⟨U.generator_tendsto_nhdsLT x, U.generator_tendsto x⟩

/-- **The abstract Cauchy problem on the whole line.** For `x ∈ D(A)` the orbit `t ↦ U t x` is
differentiable at every real time, with derivative `U t (A x)`. -/
theorem hasDerivAt (U : StronglyContinuousGroup X) (x : U.domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => U s (x : X))
      (U t (U.generator ⟨(x : X), by rw [U.generator_domain]; exact x.property⟩)) t := by
  have hsub : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have hinner : HasDerivAt (fun s : ℝ => U (s - t) (x : X))
      (U.generator ⟨(x : X), by rw [U.generator_domain]; exact x.property⟩) t := by
    simpa [Function.comp_def] using
      (U.hasDerivAt_zero x).scomp_of_eq t hsub (sub_self t).symm
  have h := ((U t).hasFDerivAt).comp_hasDerivAt t hinner
  have hfun : (fun s : ℝ => U s (x : X)) = (U t) ∘ fun s : ℝ => U (s - t) (x : X) := by
    funext s
    have hts : t + (s - t) = s := by ring
    rw [Function.comp_apply, ← U.map_add_apply, hts]
  rw [hfun]
  exact h

/-! ## Uniqueness -/

/-- **A C₀-group is determined by its generator.** The generator fixes the forward semigroup by
uniqueness for semigroups, and it fixes the backward half through the reversed group, whose
generator is `-A`. -/
theorem eq_of_generator_eq {U V : StronglyContinuousGroup X} (h : U.generator = V.generator) :
    U = V := by
  have hfwd : U.toSemigroup = V.toSemigroup :=
    StronglyContinuousSemigroup.eq_of_generator_eq h
  have hrefl : U.reflect.generator = V.reflect.generator := by
    rw [U.reflect_generator, V.reflect_generator, h]
  have hbwd : U.reflect.toSemigroup = V.reflect.toSemigroup :=
    StronglyContinuousSemigroup.eq_of_generator_eq hrefl
  refine ext fun t => ?_
  rcases le_or_gt 0 t with ht | ht
  · rw [← U.toSemigroup_realOperator_of_nonneg ht,
      ← V.toSemigroup_realOperator_of_nonneg ht, hfwd]
  · have hnt : (0 : ℝ) ≤ -t := by linarith
    have hst := congrArg (fun S : StronglyContinuousSemigroup X => S.realOperator (-t)) hbwd
    simpa only [U.reflect_toSemigroup_realOperator_of_nonneg hnt,
      V.reflect_toSemigroup_realOperator_of_nonneg hnt, neg_neg] using hst

/-- Injectivity form of `TauCeti.Semigroups.StronglyContinuousGroup.eq_of_generator_eq`. -/
theorem generator_injective :
    Function.Injective (generator : StronglyContinuousGroup X → X →ₗ.[ℝ] X) :=
  fun _ _ h => eq_of_generator_eq h

/-! ## The group generated by a bounded operator -/

/-- The uniformly continuous C₀-group `U(t) = exp (t • A)` of a bounded operator `A`. Unlike the
semigroup `TauCeti.Semigroups.StronglyContinuousSemigroup.ofBounded`, this runs in both time
directions: `exp (-t • A)` inverts `exp (t • A)`. -/
def ofBounded (A : X →L[ℝ] X) : StronglyContinuousGroup X where
  toFun t := exp (t • A)
  map_zero' := by rw [zero_smul, exp_zero, ContinuousLinearMap.one_def]
  map_add' s t := by
    rw [TauCeti.exp_add_smul]
  continuousAt_zero' x :=
    (((differentiable_exp_smul_const ℝ A).continuous).clm_apply continuous_const).continuousAt

/-- The operator of `ofBounded A` at time `t` is `exp (t • A)`. -/
@[simp]
theorem ofBounded_apply (A : X →L[ℝ] X) (t : ℝ) : ofBounded A t = exp (t • A) := by
  rw [ofBounded]
  rfl

/-- The forward semigroup of `ofBounded A` is the bounded-generator semigroup of `A`. -/
@[simp]
theorem ofBounded_toSemigroup (A : X →L[ℝ] X) :
    (ofBounded A).toSemigroup = StronglyContinuousSemigroup.ofBounded A := by
  ext t
  rw [toSemigroup_apply, ofBounded_apply, StronglyContinuousSemigroup.ofBounded_apply]

/-- Time reversal of `ofBounded A` is the group of `-A`. -/
@[simp]
theorem ofBounded_reflect (A : X →L[ℝ] X) : (ofBounded A).reflect = ofBounded (-A) := by
  ext t
  rw [reflect_apply, ofBounded_apply, ofBounded_apply, neg_smul, smul_neg]

/-- The generator domain of `ofBounded A` is the whole space. -/
@[simp]
theorem ofBounded_domain_eq_top (A : X →L[ℝ] X) : (ofBounded A).domain = ⊤ := by
  rw [domain_def, ofBounded_toSemigroup, StronglyContinuousSemigroup.ofBounded_domain_eq_top]

/-- The generator of `ofBounded A` is `A` itself, viewed as a total unbounded operator. -/
@[simp]
theorem ofBounded_generator (A : X →L[ℝ] X) :
    (ofBounded A).generator = (A : X →ₗ[ℝ] X).toPMap ⊤ := by
  rw [generator_def, ofBounded_toSemigroup, StronglyContinuousSemigroup.ofBounded_generator]

/-- `ofBounded A` has the two-sided growth bound `(‖A‖, 1)`: `‖exp (t • A)‖ ≤ e^{‖A‖ |t|}`. -/
theorem ofBounded_hasGrowthBound (A : X →L[ℝ] X) : (ofBounded A).HasGrowthBound ‖A‖ 1 := by
  refine hasGrowthBound_of_bound le_rfl fun t => ?_
  rw [one_mul, ofBounded_apply]
  exact TauCeti.norm_exp_smul_le A t

/-- A C₀-group whose generator is the bounded operator `A`, defined on all of `X`, is the
operator exponential `t ↦ exp (t • A)`. -/
theorem eq_ofBounded_of_generator_eq {U : StronglyContinuousGroup X} (A : X →L[ℝ] X)
    (h : U.generator = (A : X →ₗ[ℝ] X).toPMap ⊤) : U = ofBounded A :=
  eq_of_generator_eq (h.trans (ofBounded_generator A).symm)

end StronglyContinuousGroup

end TauCeti.Semigroups

end
