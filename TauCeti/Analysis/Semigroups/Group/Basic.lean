/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.GrowthBound

/-!
# Strongly continuous one-parameter groups

A **C₀-group** on a real normed space `X` is a family `U : ℝ → X →L[ℝ] X` indexed by *all* of `ℝ`
with `U 0 = 1`, `U (s + t) = U s ∘ U t`, and `t ↦ U t x` continuous at `0`. It is not reached by
the C₀-semigroup API: the two-sided law makes every `U t` invertible, with inverse `U (-t)`, and
forces the orbits to be continuous on the whole line rather than only on `[0, ∞)`. The unitary
group `e^{itH}` of a Schrödinger evolution is the motivating example.

This file sets up the object and the two ways of viewing it through the existing
`StronglyContinuousSemigroup` theory:

* the **forward semigroup** `U.toSemigroup`, the restriction of `U` to `[0, ∞)`;
* the **time reversal** `U.reflect`, the C₀-group `t ↦ U (-t)`, whose forward semigroup is the
  backward half of `U`.

The growth bound is obtained by applying semigroup results to both halves. The generator API in
`TauCeti.Analysis.Semigroups.Group.Generator`, including generator uniqueness, similarly uses
`U.reflect` for the backward half.

## Main definitions

* `TauCeti.Semigroups.StronglyContinuousGroup`: the C₀-group structure.
* `TauCeti.Semigroups.StronglyContinuousGroup.toContinuousLinearEquiv`: `U t` as a continuous
  linear equivalence, with inverse `U (-t)`.
* `TauCeti.Semigroups.StronglyContinuousGroup.reflect`: the time-reversed group `t ↦ U (-t)`.
* `TauCeti.Semigroups.StronglyContinuousGroup.toSemigroup`: the forward C₀-semigroup.
* `TauCeti.Semigroups.StronglyContinuousGroup.HasGrowthBound`: the two-sided growth bound
  `‖U t‖ ≤ M * exp (ω * |t|)`.

## Main results

* `TauCeti.Semigroups.StronglyContinuousGroup.continuous_orbit`: the orbits of a C₀-group are
  continuous on all of `ℝ`, not merely at `0`.
* `TauCeti.Semigroups.StronglyContinuousGroup.existsGrowthBound`: every C₀-group has a finite
  two-sided exponential growth bound.
* `TauCeti.Semigroups.StronglyContinuousGroup.isometry_of_forall_norm_le_one`: a C₀-group that
  contracts in both time directions is a group of isometries.
* `TauCeti.Semigroups.StronglyContinuousGroup.tendsto_apply`: joint strong continuity
  `U (f i) (g i) → U r z`, at every real time and without a sign restriction.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section II.3.11;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Section 1.6.
-/

public section

noncomputable section

open scoped Topology NNReal
open Filter

namespace TauCeti.Semigroups

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A strongly continuous one-parameter group (C₀-group) on a real normed space.

The family is indexed by all of `ℝ`; the axioms are `U 0 = Id`, `U (s + t) = U s ∘ U t` at every
pair of real times, and strong continuity at `0`. Completeness is imposed separately on results
that require it, such as `existsGrowthBound`. -/
structure StronglyContinuousGroup where
  /-- The group operator at time `t : ℝ`. -/
  toFun : ℝ → X →L[ℝ] X
  /-- `U 0 = Id`. -/
  map_zero' : toFun 0 = ContinuousLinearMap.id ℝ X
  /-- `U (s + t) = U s ∘ U t`, at every pair of real times. -/
  map_add' : ∀ s t : ℝ, toFun (s + t) = (toFun s).comp (toFun t)
  /-- Strong continuity at `0`. -/
  continuousAt_zero' : ∀ x : X, ContinuousAt (fun t : ℝ => toFun t x) 0

variable {X}

namespace StronglyContinuousGroup

instance instFunLike : FunLike (StronglyContinuousGroup X) ℝ (X →L[ℝ] X) where
  coe := toFun
  coe_injective := by
    intro U V h
    cases U
    cases V
    congr

@[ext]
theorem ext {U V : StronglyContinuousGroup X} (h : ∀ t, U t = V t) : U = V :=
  DFunLike.ext _ _ h

/-- The group operator at time `0` is the identity. -/
@[simp]
theorem map_zero (U : StronglyContinuousGroup X) : U 0 = ContinuousLinearMap.id ℝ X :=
  U.map_zero'

/-- Pointwise form of `StronglyContinuousGroup.map_zero`. -/
theorem map_zero_apply (U : StronglyContinuousGroup X) (x : X) : U 0 x = x := by
  rw [U.map_zero]
  rfl

/-- The two-sided group law. -/
@[simp]
theorem map_add (U : StronglyContinuousGroup X) (s t : ℝ) : U (s + t) = (U s).comp (U t) :=
  U.map_add' s t

/-- Pointwise form of `StronglyContinuousGroup.map_add`. -/
theorem map_add_apply (U : StronglyContinuousGroup X) (s t : ℝ) (x : X) :
    U (s + t) x = U s (U t x) := by
  rw [U.map_add]
  rfl

/-- Operators at different times commute. -/
theorem map_comm (U : StronglyContinuousGroup X) (s t : ℝ) (x : X) :
    U s (U t x) = U t (U s x) := by
  rw [← U.map_add_apply, add_comm, U.map_add_apply]

/-! ## Invertibility -/

/-- `U (-t)` is a left inverse of `U t`. -/
@[simp]
theorem map_neg_apply_map_apply (U : StronglyContinuousGroup X) (t : ℝ) (x : X) :
    U (-t) (U t x) = x := by
  rw [← U.map_add_apply, neg_add_cancel, U.map_zero_apply]

/-- `U (-t)` is a right inverse of `U t`. -/
@[simp]
theorem map_apply_map_neg_apply (U : StronglyContinuousGroup X) (t : ℝ) (x : X) :
    U t (U (-t) x) = x := by
  rw [← U.map_add_apply, add_neg_cancel, U.map_zero_apply]

/-- The group operator at time `t`, packaged as a continuous linear equivalence whose inverse is
the operator at time `-t`. -/
def toContinuousLinearEquiv (U : StronglyContinuousGroup X) (t : ℝ) : X ≃L[ℝ] X :=
  ContinuousLinearEquiv.equivOfInverse (U t) (U (-t)) (U.map_neg_apply_map_apply t)
    (U.map_apply_map_neg_apply t)

@[simp]
theorem toContinuousLinearEquiv_apply (U : StronglyContinuousGroup X) (t : ℝ) (x : X) :
    U.toContinuousLinearEquiv t x = U t x := by
  rw [toContinuousLinearEquiv]
  rfl

@[simp]
theorem toContinuousLinearEquiv_symm_apply (U : StronglyContinuousGroup X) (t : ℝ) (x : X) :
    (U.toContinuousLinearEquiv t).symm x = U (-t) x := by
  rw [toContinuousLinearEquiv]
  rfl

/-- Every operator of a C₀-group is bijective. -/
theorem bijective (U : StronglyContinuousGroup X) (t : ℝ) : Function.Bijective (U t) :=
  (U.toContinuousLinearEquiv t).bijective

/-! ## Strong continuity on the whole line -/

/-- **The orbits of a C₀-group are continuous on all of `ℝ`.** The two-sided group law turns the
increment at `t₀` into an increment at `0`, where continuity is assumed. -/
theorem continuous_orbit (U : StronglyContinuousGroup X) (x : X) :
    Continuous fun t : ℝ => U t x := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hshift : ContinuousAt (fun t : ℝ => t - t₀) t₀ := by
    fun_prop
  have hinner : ContinuousAt (fun t : ℝ => U (t - t₀) x) t₀ :=
    ContinuousAt.comp_of_eq (U.continuousAt_zero' x) hshift (sub_self t₀)
  have hfun : (fun t : ℝ => U t x) = fun t : ℝ => U t₀ (U (t - t₀) x) := by
    funext t
    have ht : t₀ + (t - t₀) = t := by ring
    rw [← U.map_add_apply, ht]
  rw [hfun]
  exact (U t₀).continuous.continuousAt.comp hinner

/-! ## Time reversal and the forward semigroup -/

/-- The time-reversed C₀-group `t ↦ U (-t)`. -/
def reflect (U : StronglyContinuousGroup X) : StronglyContinuousGroup X where
  toFun t := U (-t)
  map_zero' := by rw [neg_zero, U.map_zero]
  map_add' s t := by rw [← U.map_add, ← neg_add]
  continuousAt_zero' x :=
    ContinuousAt.comp_of_eq (U.continuousAt_zero' x) (by fun_prop) neg_zero

@[simp]
theorem reflect_apply (U : StronglyContinuousGroup X) (t : ℝ) : U.reflect t = U (-t) := by
  rw [reflect]
  rfl

@[simp]
theorem reflect_reflect (U : StronglyContinuousGroup X) : U.reflect.reflect = U := by
  ext t
  rw [reflect_apply, reflect_apply, neg_neg]

/-- The forward C₀-semigroup of a C₀-group: the restriction of `U` to nonnegative times. -/
def toSemigroup (U : StronglyContinuousGroup X) : StronglyContinuousSemigroup X where
  toFun t := U t
  map_zero' := by rw [NNReal.coe_zero, U.map_zero]
  map_add' s t := by rw [NNReal.coe_add, U.map_add]
  continuousAt_zero' x :=
    ContinuousAt.comp_of_eq (U.continuousAt_zero' x)
      (NNReal.continuous_coe.continuousAt (x := 0)) NNReal.coe_zero

@[simp]
theorem toSemigroup_apply (U : StronglyContinuousGroup X) (t : ℝ≥0) :
    U.toSemigroup t = U (t : ℝ) := by
  rw [toSemigroup]
  rfl

/-- At a nonnegative real time the forward semigroup's real-time shim is the group operator. -/
@[simp]
theorem toSemigroup_realOperator_of_nonneg (U : StronglyContinuousGroup X) {t : ℝ} (ht : 0 ≤ t) :
    U.toSemigroup.realOperator t = U t := by
  rw [StronglyContinuousSemigroup.realOperator_def, toSemigroup_apply, Real.coe_toNNReal t ht]

/-- At a nonnegative real time the reversed group's forward semigroup runs `U` backwards.

Not a `simp` lemma: `simp` already reaches this form through
`toSemigroup_realOperator_of_nonneg` and `reflect_apply`, so tagging it duplicates a rule
`simp` derives anyway. -/
theorem reflect_toSemigroup_realOperator_of_nonneg
    (U : StronglyContinuousGroup X) {t : ℝ} (ht : 0 ≤ t) :
    U.reflect.toSemigroup.realOperator t = U (-t) := by
  rw [U.reflect.toSemigroup_realOperator_of_nonneg ht, reflect_apply]

/-! ## Two-sided growth bounds -/

/-- A C₀-group has exponential growth bound `(ω, M)`, with `M ≥ 1`, if `‖U t‖ ≤ M e^{ω |t|}` at
every real time. The absolute value is what distinguishes this from the semigroup bound: a
C₀-group grows at most exponentially in *both* time directions. -/
def HasGrowthBound (U : StronglyContinuousGroup X) (ω M : ℝ) : Prop :=
  1 ≤ M ∧ ∀ t : ℝ, ‖U t‖ ≤ M * Real.exp (ω * |t|)

/-- The multiplicative constant in a growth bound is at least one. -/
theorem HasGrowthBound.one_le {U : StronglyContinuousGroup X} {ω M : ℝ}
    (hb : U.HasGrowthBound ω M) : 1 ≤ M :=
  hb.1

/-- The operator-norm estimate supplied by a growth bound. -/
theorem HasGrowthBound.bound {U : StronglyContinuousGroup X} {ω M : ℝ}
    (hb : U.HasGrowthBound ω M) (t : ℝ) : ‖U t‖ ≤ M * Real.exp (ω * |t|) :=
  hb.2 t

/-- A two-sided growth bound can be weakened by increasing both the exponential rate and the
multiplicative constant. -/
theorem HasGrowthBound.mono {U : StronglyContinuousGroup X} {ω M ω' M' : ℝ}
    (hb : U.HasGrowthBound ω M) (hω : ω ≤ ω') (hM : M ≤ M') :
    U.HasGrowthBound ω' M' := by
  refine ⟨hb.one_le.trans hM, fun t => ?_⟩
  have hM_nonneg : 0 ≤ M := zero_le_one.trans hb.one_le
  have hexp : Real.exp (ω * |t|) ≤ Real.exp (ω' * |t|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hω (abs_nonneg t))
  exact (hb.bound t).trans
    (mul_le_mul hM hexp (Real.exp_nonneg _) (hM_nonneg.trans hM))

/-- A two-sided growth bound can be weakened by increasing the exponential rate. -/
theorem HasGrowthBound.mono_omega {U : StronglyContinuousGroup X} {ω M ω' : ℝ}
    (hb : U.HasGrowthBound ω M) (hω : ω ≤ ω') : U.HasGrowthBound ω' M :=
  hb.mono hω le_rfl

/-- A two-sided growth bound can be weakened by increasing the multiplicative constant. -/
theorem HasGrowthBound.mono_const {U : StronglyContinuousGroup X} {ω M M' : ℝ}
    (hb : U.HasGrowthBound ω M) (hM : M ≤ M') : U.HasGrowthBound ω M' :=
  hb.mono le_rfl hM

/-- Constructor for a two-sided growth bound from the multiplicative lower bound and the
operator-norm estimate. -/
theorem hasGrowthBound_of_bound {U : StronglyContinuousGroup X} {ω M : ℝ} (hM : 1 ≤ M)
    (hbound : ∀ t : ℝ, ‖U t‖ ≤ M * Real.exp (ω * |t|)) : U.HasGrowthBound ω M :=
  ⟨hM, hbound⟩

/-- A two-sided growth bound restricts to a growth bound for the forward semigroup. -/
theorem HasGrowthBound.toSemigroup {U : StronglyContinuousGroup X} {ω M : ℝ}
    (hb : U.HasGrowthBound ω M) : U.toSemigroup.HasGrowthBound ω M := by
  refine StronglyContinuousSemigroup.hasGrowthBound_of_bound hb.one_le fun t ht => ?_
  rw [U.toSemigroup_realOperator_of_nonneg ht]
  simpa [abs_of_nonneg ht] using hb.bound t

/-- A two-sided growth bound is invariant under time reversal. -/
theorem HasGrowthBound.reflect {U : StronglyContinuousGroup X} {ω M : ℝ}
    (hb : U.HasGrowthBound ω M) : U.reflect.HasGrowthBound ω M :=
  ⟨hb.one_le, fun t => by simpa [abs_neg] using hb.bound (-t)⟩

/-- Growth bound `(0, 1)` is exactly contractivity at every real time. -/
theorem hasGrowthBound_zero_one_iff (U : StronglyContinuousGroup X) :
    U.HasGrowthBound 0 1 ↔ ∀ t : ℝ, ‖U t‖ ≤ 1 := by
  refine ⟨fun hb t => by simpa using hb.bound t, fun h => hasGrowthBound_of_bound le_rfl ?_⟩
  intro t
  simpa using h t

/-! ## Contraction groups are groups of isometries -/

/-- **A C₀-group that contracts in both time directions preserves norms.** A strict contraction
at time `t` would have to be undone by an expansion at time `-t`, which contractivity forbids.
This is the norm preservation behind unitary groups such as `e^{itH}`. -/
theorem norm_map_apply_eq_of_norm_le_one (U : StronglyContinuousGroup X) (t : ℝ)
    (ht : ‖U t‖ ≤ 1) (ht' : ‖U (-t)‖ ≤ 1) (x : X) : ‖U t x‖ = ‖x‖ := by
  have key (s : ℝ) (hs : ‖U s‖ ≤ 1) (y : X) : ‖U s y‖ ≤ ‖y‖ :=
    ((U s).le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg y) hs)
  refine le_antisymm (key t ht x) ?_
  calc ‖x‖ = ‖U (-t) (U t x)‖ := by rw [U.map_neg_apply_map_apply]
    _ ≤ ‖U t x‖ := key (-t) ht' _

/-- Every operator of a contractive C₀-group is an isometry. -/
theorem isometry_of_forall_norm_le_one (U : StronglyContinuousGroup X)
    (h : ∀ t : ℝ, ‖U t‖ ≤ 1) (t : ℝ) : Isometry (U t) :=
  AddMonoidHomClass.isometry_of_norm _ (U.norm_map_apply_eq_of_norm_le_one t (h t) (h (-t)))

variable [CompleteSpace X]

/-- **Every C₀-group has a finite two-sided exponential growth bound.** The forward and backward
halves are C₀-semigroups, so each has a growth bound; taking the larger exponent and the larger
constant covers both time directions at once. -/
theorem existsGrowthBound (U : StronglyContinuousGroup X) :
    ∃ ω M : ℝ, U.HasGrowthBound ω M := by
  obtain ⟨ω₁, M₁, hb₁⟩ := U.toSemigroup.existsGrowthBound
  obtain ⟨ω₂, M₂, hb₂⟩ := U.reflect.toSemigroup.existsGrowthBound
  have hb₁' := hb₁.mono (le_max_left ω₁ ω₂) (le_max_left M₁ M₂)
  have hb₂' := hb₂.mono (le_max_right ω₁ ω₂) (le_max_right M₁ M₂)
  refine ⟨max ω₁ ω₂, max M₁ M₂, le_max_of_le_left hb₁.one_le, fun t => ?_⟩
  rcases le_or_gt 0 t with ht | ht
  · rw [← U.toSemigroup_realOperator_of_nonneg ht, abs_of_nonneg ht]
    exact hb₁'.bound t ht
  · have hnt : 0 ≤ -t := by linarith
    rw [← neg_neg t, ← U.reflect_toSemigroup_realOperator_of_nonneg hnt, abs_neg,
      abs_of_nonneg hnt]
    exact hb₂'.bound (-t) hnt

/-- **Joint strong continuity of a C₀-group**: if `f i → r` and `g i → z`, then
`U (f i) (g i) → U r z`.

This is the two-sided counterpart of
`TauCeti.Semigroups.StronglyContinuousSemigroup.tendsto_realOperator_apply`, and needs no sign
hypothesis on the times: the group has a growth bound valid on the whole line, which supplies
the uniform operator bound that strong continuity alone does not. -/
theorem tendsto_apply {ι : Type*} {l : Filter ι} (U : StronglyContinuousGroup X) {f : ι → ℝ}
    {g : ι → X} {r : ℝ} {z : X} (hf : Tendsto f l (𝓝 r)) (hg : Tendsto g l (𝓝 z)) :
    Tendsto (fun i => U (f i) (g i)) l (𝓝 (U r z)) := by
  obtain ⟨ω, M, hb⟩ := U.existsGrowthBound
  have hM : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hb.one_le
  -- One operator-norm bound valid at every time eventually visited by `f`.
  have hbound : ∀ᶠ i in l, ‖U (f i)‖ ≤ M * Real.exp (|ω| * (|r| + 1)) := by
    filter_upwards [hf.eventually (eventually_abs_sub_lt r one_pos)] with i hi
    have habs : |f i| ≤ |r| + 1 := by
      have := abs_sub_abs_le_abs_sub (f i) r
      linarith
    refine (hb.bound (f i)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM.le)
    calc ω * |f i| ≤ |ω| * |f i| := mul_le_mul_of_nonneg_right (le_abs_self ω) (abs_nonneg _)
      _ ≤ |ω| * (|r| + 1) := mul_le_mul_of_nonneg_left habs (abs_nonneg ω)
  -- The time moves: this is continuity of the orbit of the fixed vector `z`.
  have h2 : Tendsto (fun i => U (f i) z) l (𝓝 (U r z)) :=
    ((U.continuous_orbit z).tendsto r).comp hf
  exact TauCeti.ContinuousLinearMap.tendsto_apply_of_eventually_norm_le hbound h2 hg

end StronglyContinuousGroup

end TauCeti.Semigroups

end
