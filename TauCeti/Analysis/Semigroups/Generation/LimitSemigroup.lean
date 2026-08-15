/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Generation.Yosida.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Limits of Yosida semigroups

For an unbounded operator `A` on a real Banach space whose Yosida approximations
`A_lambda = lambda ^ 2 R(lambda, A) - lambda I` generate approximating exponentials
`exp (t A_lambda) x` that form a Cauchy family as `lambda -> +∞`, this file defines the chosen
candidate limit vector `yosidaLimit A t x` and provides the shared scaffolding for assembling such
limits into strongly continuous semigroups.

Completeness of the Banach space turns the Cauchy estimate into a limit vector
`yosidaLimit A t x`. The definition is the chosen value `limUnder atTop` of
`exp (t A_lambda) x`, so it makes sense for every real `t`, but it is only *proved* to be the
limit when `A` is m-dissipative with dense domain (or satisfies the Hille--Yosida bounds) and
`t ≥ 0`. For the densely defined m-dissipative case, convergence is established below in
`TauCeti.Semigroups.IsMDissipative.tendsto_yosidaLimit`; for the general-`M` Hille--Yosida case,
convergence is proved in `TauCeti.Semigroups.tendsto_yosidaLimit_of_norm_resolvent_pow_le`
in `TauCeti/Analysis/Semigroups/Generation/HilleYosida/Limit.lean`.

On the range `t ≥ 0`, the limit is linear in `x`, satisfies `S(0) = I` and `S(s + t) = S(s) S(t)`,
and — because the convergence is uniform on compact time intervals — depends continuously on `t`.
Under m-dissipativity it is contractive and yields a genuine contraction semigroup
`yosidaLimitSemigroup`, while under general Hille--Yosida bounds with parameter `M ≥ 1` it satisfies
`‖yosidaLimit A t x‖ ≤ M * ‖x‖`.

This file also provides the general limit-semigroup constructor `yosidaLimitSemigroupOfTendsto`
parameterized by pointwise and uniform convergence and an eventual norm bound, shared between the
Lumer--Phillips and Hille--Yosida constructions.

## Main definitions

* `TauCeti.Semigroups.yosidaLimit`: the value chosen from the family `exp (t A_lambda) x` as
  `lambda -> ∞`, which is its limit at nonnegative times.
* `TauCeti.Semigroups.yosidaLimitSemigroupOfTendsto`: the strongly continuous semigroup obtained
  from pointwise and uniform convergence and an eventual norm bound `M`.
* `TauCeti.Semigroups.IsMDissipative.yosidaLimitSemigroup`: the resulting contraction semigroup.

## Main results

* `TauCeti.Semigroups.norm_yosidaLimit_le_of_tendsto_of_norm_le`: passing an operator bound to the
  limit.
* `TauCeti.Semigroups.yosidaLimitSemigroupOfTendsto_apply`: evaluating the limit semigroup.
* `TauCeti.Semigroups.yosidaLimitSemigroupOfTendsto_realOperator_apply_of_nonneg`: evaluating the
  real-time operator at nonnegative times.
* `TauCeti.Semigroups.hasGrowthBound_yosidaLimitSemigroupOfTendsto`: growth bound `(0, M)` of the
  limit semigroup.
* `TauCeti.Semigroups.tendsto_yosidaLimitSemigroupOfTendsto`: convergence of approximating orbits.
* `TauCeti.Semigroups.IsMDissipative.tendsto_yosidaLimit`: the defining convergence
  `exp (t A_lambda) x -> yosidaLimit A t x`.
* `TauCeti.Semigroups.IsMDissipative.tendstoUniformlyOn_exp_yosidaApproximation`: that
  convergence is uniform on compact time intervals.
* `TauCeti.Semigroups.IsMDissipative.yosidaLimit_time_add`: the semigroup law
  `yosidaLimit A (s + t) = yosidaLimit A s ∘ yosidaLimit A t` at nonnegative times.
* `TauCeti.Semigroups.IsMDissipative.exists_contractionSemigroup`: a densely defined
  m-dissipative operator gives rise to a contraction semigroup whose orbits are the limits of
  the Yosida exponentials.

This is the limit stage of the Yosida construction; the generator of `yosidaLimitSemigroup` is
identified with `A` — the Lumer--Phillips generation theorem — in
`TauCeti/Analysis/Semigroups/Generation/LumerPhillips.lean`.

## References

* Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Sections II.3.5 and II.3.8;
* Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Chapter 1, Theorems 4.3 and 5.3.
-/

public section

noncomputable section

open scoped NNReal Topology

open Filter NormedSpace

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The **Yosida limit** of an unbounded operator `A` at time `t`, applied to `x`: the value
`limUnder atTop` chooses from the family `exp (t A_lambda) x`.

Being a `limUnder`, this is a total definition: it names a candidate value for every operator
`A` and every real `t`, but it is a junk value unless that family actually converges. It is
proved to be the limit at nonnegative times in the two supported cases: when `A` is
m-dissipative with dense domain (established below in
`TauCeti.Semigroups.IsMDissipative.tendsto_yosidaLimit`), or when `A` has dense domain and satisfies
the Hille--Yosida resolvent-power bounds (proved in
`TauCeti.Semigroups.tendsto_yosidaLimit_of_norm_resolvent_pow_le` in
`TauCeti/Analysis/Semigroups/Generation/HilleYosida/Limit.lean`). In both cases the compact-time
Cauchy estimate gives convergence. Every lemma below that appeals to the limit property carries
the relevant hypotheses explicitly. -/
def yosidaLimit (A : X →ₗ.[ℝ] X) (t : ℝ) (x : X) : X :=
  limUnder atTop fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x

/-- A Cauchy family of Yosida exponentials converges to `yosidaLimit`, its chosen
`limUnder` value. This exposes the convergence property to downstream modules while keeping the
implementation of `yosidaLimit` hidden. -/
theorem tendsto_yosidaLimit_of_cauchySeq (A : X →ₗ.[ℝ] X) (t : ℝ) (x : X)
    (h : CauchySeq fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) :
    Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
      (𝓝 (yosidaLimit A t x)) := by
  rw [yosidaLimit]
  exact h.tendsto_limUnder

omit [CompleteSpace X] in
/-- At time `0` every Yosida exponential is the identity, so the limit is too. -/
@[simp]
theorem yosidaLimit_zero (A : X →ₗ.[ℝ] X) (x : X) : yosidaLimit A 0 x = x := by
  have hconst : (fun lambda : ℝ => exp ((0 : ℝ) • yosidaApproximation A lambda) x) =
      fun _ : ℝ => x := by
    funext lambda
    rw [zero_smul, exp_zero]
    rfl
  simp only [yosidaLimit, hconst]
  exact tendsto_const_nhds.limUnder_eq

/-- Splitting the exponential of a sum of commuting times: `exp ((s + t) B) = exp (s B) exp (t B)`
pointwise, for a bounded operator `B`. -/
private theorem exp_add_smul_apply (B : X →L[ℝ] X) (s t : ℝ) (x : X) :
    exp ((s + t) • B) x = exp (s • B) (exp (t • B) x) := by
  let +nondep : NormedAlgebra ℚ (X →L[ℝ] X) := .restrictScalars ℚ ℝ _
  rw [add_smul, exp_add_of_commute (((Commute.refl B).smul_left s).smul_right t),
    ContinuousLinearMap.mul_def]
  rfl

/-! ## Shared limit-semigroup scaffolding -/

omit [CompleteSpace X] in
/-- Pointwise convergence of the Yosida exponentials implies additivity of the limit. -/
private theorem yosidaLimit_add_of_tendsto {A : X →ₗ.[ℝ] X} {t : ℝ}
    (htend : ∀ x : X, Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
      (𝓝 (yosidaLimit A t x))) (x y : X) :
    yosidaLimit A t (x + y) = yosidaLimit A t x + yosidaLimit A t y := by
  refine tendsto_nhds_unique (htend (x + y)) ?_
  simpa only [map_add] using (htend x).add (htend y)

omit [CompleteSpace X] in
/-- Pointwise convergence of the Yosida exponentials implies homogeneity of the limit. -/
private theorem yosidaLimit_smul_of_tendsto {A : X →ₗ.[ℝ] X} {t : ℝ}
    (htend : ∀ x : X, Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
      (𝓝 (yosidaLimit A t x))) (c : ℝ) (x : X) :
    yosidaLimit A t (c • x) = c • yosidaLimit A t x := by
  refine tendsto_nhds_unique (htend (c • x)) ?_
  simpa only [map_smul] using (htend x).const_smul c

omit [CompleteSpace X] in
/-- An eventual operator bound on the Yosida exponentials passes to the limit. -/
theorem norm_yosidaLimit_le_of_tendsto_of_norm_le {A : X →ₗ.[ℝ] X} {t : ℝ} {M : ℝ} {x : X}
    (htend : Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
      (𝓝 (yosidaLimit A t x)))
    (hbound : ∀ᶠ lambda in atTop, ‖exp (t • yosidaApproximation A lambda)‖ ≤ M) :
    ‖yosidaLimit A t x‖ ≤ M * ‖x‖ := by
  refine le_of_tendsto htend.norm ?_
  filter_upwards [hbound] with lambda hl
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right hl (norm_nonneg _))

/-- The semigroup law for `yosidaLimit` under pointwise convergence and an eventual norm bound. -/
private theorem yosidaLimit_time_add_of_tendsto_of_norm_le {A : X →ₗ.[ℝ] X} {s t : ℝ} {M : ℝ}
    (x : X)
    (htend_t : Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
      (𝓝 (yosidaLimit A t x)))
    (htend_s : Tendsto (fun lambda : ℝ =>
        exp (s • yosidaApproximation A lambda) (yosidaLimit A t x)) atTop
      (𝓝 (yosidaLimit A s (yosidaLimit A t x))))
    (htend_st : Tendsto (fun lambda : ℝ => exp ((s + t) • yosidaApproximation A lambda) x) atTop
      (𝓝 (yosidaLimit A (s + t) x)))
    (hbound_s : ∀ᶠ lambda in atTop, ‖exp (s • yosidaApproximation A lambda)‖ ≤ M) :
    yosidaLimit A (s + t) x = yosidaLimit A s (yosidaLimit A t x) := by
  set y := yosidaLimit A t x with hy
  set z := yosidaLimit A s y with hz
  have hstep : Tendsto (fun lambda : ℝ => exp ((s + t) • yosidaApproximation A lambda) x - z)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun lambda : ℝ =>
      M * ‖exp (t • yosidaApproximation A lambda) x - y‖ +
        ‖exp (s • yosidaApproximation A lambda) y - z‖) ?_ ?_
    · filter_upwards [hbound_s] with lambda hbound
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
        tendsto_iff_norm_sub_tendsto_zero.mp htend_t
      have h2 : Tendsto
          (fun lambda : ℝ => ‖exp (s • yosidaApproximation A lambda) y - z‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.mp htend_s
      simpa using (h1.const_mul M).add h2
  refine tendsto_nhds_unique htend_st ?_
  simpa using hstep.add_const z

/-- The Yosida limit is continuous in time on a compact interval whenever the approximating
exponentials converge uniformly there. -/
private theorem continuousOn_yosidaLimit_Icc_of_tendstoUniformlyOn (A : X →ₗ.[ℝ] X)
    (x : X) {T : ℝ}
    (hunif : TendstoUniformlyOn (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) x)
      (fun t : ℝ => yosidaLimit A t x) atTop (Set.Icc 0 T)) :
    ContinuousOn (fun t : ℝ => yosidaLimit A t x) (Set.Icc 0 T) :=
  hunif.continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun lambda =>
      (((differentiable_exp_smul_const ℝ (yosidaApproximation A lambda)).continuous).clm_apply
        continuous_const).continuousOn))

omit [CompleteSpace X] in
/-- Continuity on `[0, ∞)` from continuity on every compact interval `[0, T]`. -/
private theorem continuousOn_Ici_of_forall_continuousOn_Icc {Y : Type*} [TopologicalSpace Y]
    {f : ℝ → Y} (hIcc : ∀ T : ℝ, 0 ≤ T → ContinuousOn f (Set.Icc 0 T)) :
    ContinuousOn f (Set.Ici 0) := by
  intro t ht
  have ht' : (0 : ℝ) ≤ t := ht
  have hmem : Set.Icc 0 (t + 1) ∈ 𝓝[Set.Ici (0 : ℝ)] t := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Set.Iio (t + 1), Iio_mem_nhds (by linarith), ?_⟩
    rintro u ⟨hu₁, hu₂⟩
    exact ⟨hu₂, le_of_lt hu₁⟩
  exact (hIcc (t + 1) (by linarith) t ⟨ht', by linarith⟩).mono_of_mem_nhdsWithin hmem

omit [CompleteSpace X] in
/-- Strong continuity at time zero on `ℝ≥0` from continuity on the nonnegative half-line. -/
private theorem continuousAt_nnreal_zero_of_continuousOn_Ici {Y : Type*} [TopologicalSpace Y]
    {f : ℝ → Y} (hcont : ContinuousOn f (Set.Ici 0)) :
    ContinuousAt (fun t : ℝ≥0 => f t) 0 := by
  have hIci : ContinuousWithinAt f (Set.Ici 0) (((0 : ℝ≥0) : ℝ)) := by
    simpa using hcont 0 (Set.mem_Ici.mpr le_rfl)
  have hcoe : ContinuousWithinAt (fun t : ℝ≥0 => (t : ℝ)) Set.univ 0 :=
    NNReal.continuous_coe.continuousWithinAt
  exact continuousWithinAt_univ _ _ |>.mp
    (hIci.comp hcoe fun t _ => t.coe_nonneg)

/-! ## Shared limit-semigroup constructor -/

section SharedConstruction

/-- The limit operator at a nonnegative time, packaged as a bounded operator on `X`. -/
private def yosidaLimitCLMOfTendsto {A : X →ₗ.[ℝ] X} (M : ℝ)
    (htend : ∀ t : ℝ, 0 ≤ t → ∀ x : X,
      Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
        (𝓝 (yosidaLimit A t x)))
    (hbound : ∀ t : ℝ, 0 ≤ t →
      ∀ᶠ lambda in atTop, ‖exp (t • yosidaApproximation A lambda)‖ ≤ M)
    (t : ℝ≥0) : X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := fun x => yosidaLimit A t x
      map_add' := fun x y =>
        yosidaLimit_add_of_tendsto (htend t.1 t.coe_nonneg) x y
      map_smul' := fun c x =>
        yosidaLimit_smul_of_tendsto (htend t.1 t.coe_nonneg) c x }
    M fun x =>
      norm_yosidaLimit_le_of_tendsto_of_norm_le
        (htend t.1 t.coe_nonneg x)
        (hbound t.1 t.coe_nonneg)

/-
The characteristic equations for `yosidaLimitCLMOfTendsto` and `yosidaLimitSemigroupOfTendsto`
are proved by `(rfl)`, not `rfl`: the underlying definitions are not marked `@[expose]`, and the
parenthesised form avoids emitting definitional-equality theorems that expose implementation
details to the simplifier or exported interface.
-/

omit [CompleteSpace X] in
@[simp]
private theorem yosidaLimitCLMOfTendsto_apply {A : X →ₗ.[ℝ] X} (M : ℝ)
    (htend : ∀ t : ℝ, 0 ≤ t → ∀ x : X,
      Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
        (𝓝 (yosidaLimit A t x)))
    (hbound : ∀ t : ℝ, 0 ≤ t →
      ∀ᶠ lambda in atTop, ‖exp (t • yosidaApproximation A lambda)‖ ≤ M)
    (t : ℝ≥0) (x : X) :
    yosidaLimitCLMOfTendsto M htend hbound t x = yosidaLimit A t x :=
  (rfl)

omit [CompleteSpace X] in
/-- Each limit operator satisfies `‖T(t)‖ ≤ M`. -/
private theorem norm_yosidaLimitCLMOfTendsto_le {A : X →ₗ.[ℝ] X} {M : ℝ} (hM : 1 ≤ M)
    (htend : ∀ t : ℝ, 0 ≤ t → ∀ x : X,
      Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
        (𝓝 (yosidaLimit A t x)))
    (hbound : ∀ t : ℝ, 0 ≤ t →
      ∀ᶠ lambda in atTop, ‖exp (t • yosidaApproximation A lambda)‖ ≤ M)
    (t : ℝ≥0) :
    ‖yosidaLimitCLMOfTendsto M htend hbound t‖ ≤ M :=
  LinearMap.mkContinuous_norm_le _ (zero_le_one.trans hM) _

/-- The strongly continuous semigroup obtained from pointwise and uniform convergence of the
approximating Yosida semigroups together with an eventual norm bound `M`. -/
def yosidaLimitSemigroupOfTendsto {A : X →ₗ.[ℝ] X} {M : ℝ}
    (htend : ∀ t : ℝ, 0 ≤ t → ∀ x : X,
      Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
        (𝓝 (yosidaLimit A t x)))
    (hunif : ∀ (x : X) (T : ℝ), 0 ≤ T →
      TendstoUniformlyOn (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) x)
        (fun t : ℝ => yosidaLimit A t x) atTop (Set.Icc 0 T))
    (hbound : ∀ t : ℝ, 0 ≤ t →
      ∀ᶠ lambda in atTop, ‖exp (t • yosidaApproximation A lambda)‖ ≤ M) :
    StronglyContinuousSemigroup X where
  toFun := yosidaLimitCLMOfTendsto M htend hbound
  map_zero' := by
    ext x
    exact yosidaLimit_zero A x
  map_add' s t := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, yosidaLimitCLMOfTendsto_apply]
    exact yosidaLimit_time_add_of_tendsto_of_norm_le x
      (htend t.1 t.coe_nonneg x)
      (htend s.1 s.coe_nonneg (yosidaLimit A t x))
      (htend (s + t).1 (add_nonneg s.coe_nonneg t.coe_nonneg) x)
      (hbound s.1 s.coe_nonneg)
  continuousAt_zero' x := by
    simpa only [yosidaLimitCLMOfTendsto_apply] using
      continuousAt_nnreal_zero_of_continuousOn_Ici
        (continuousOn_Ici_of_forall_continuousOn_Icc fun T hT =>
          continuousOn_yosidaLimit_Icc_of_tendstoUniformlyOn A x (hunif x T hT))

private theorem yosidaLimitSemigroupOfTendsto_coe {A : X →ₗ.[ℝ] X} {M : ℝ}
    (htend : ∀ t : ℝ, 0 ≤ t → ∀ x : X,
      Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
        (𝓝 (yosidaLimit A t x)))
    (hunif : ∀ (x : X) (T : ℝ), 0 ≤ T →
      TendstoUniformlyOn (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) x)
        (fun t : ℝ => yosidaLimit A t x) atTop (Set.Icc 0 T))
    (hbound : ∀ t : ℝ, 0 ≤ t →
      ∀ᶠ lambda in atTop, ‖exp (t • yosidaApproximation A lambda)‖ ≤ M)
    (t : ℝ≥0) :
    yosidaLimitSemigroupOfTendsto htend hunif hbound t =
      yosidaLimitCLMOfTendsto M htend hbound t :=
  (rfl)

/-- Evaluating the limit semigroup at `t` on `x` yields `yosidaLimit A t x`. -/
@[simp]
theorem yosidaLimitSemigroupOfTendsto_apply {A : X →ₗ.[ℝ] X} {M : ℝ}
    (htend : ∀ t : ℝ, 0 ≤ t → ∀ x : X,
      Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
        (𝓝 (yosidaLimit A t x)))
    (hunif : ∀ (x : X) (T : ℝ), 0 ≤ T →
      TendstoUniformlyOn (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) x)
        (fun t : ℝ => yosidaLimit A t x) atTop (Set.Icc 0 T))
    (hbound : ∀ t : ℝ, 0 ≤ t →
      ∀ᶠ lambda in atTop, ‖exp (t • yosidaApproximation A lambda)‖ ≤ M)
    (t : ℝ≥0) (x : X) :
    yosidaLimitSemigroupOfTendsto htend hunif hbound t x = yosidaLimit A t x := by
  rw [yosidaLimitSemigroupOfTendsto_coe, yosidaLimitCLMOfTendsto_apply]

/-- Evaluating the real-time operator of the limit semigroup at a nonnegative time `t` yields
`yosidaLimit A t x`. -/
@[simp]
theorem yosidaLimitSemigroupOfTendsto_realOperator_apply_of_nonneg {A : X →ₗ.[ℝ] X} {M : ℝ}
    (htend : ∀ t : ℝ, 0 ≤ t → ∀ x : X,
      Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
        (𝓝 (yosidaLimit A t x)))
    (hunif : ∀ (x : X) (T : ℝ), 0 ≤ T →
      TendstoUniformlyOn (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) x)
        (fun t : ℝ => yosidaLimit A t x) atTop (Set.Icc 0 T))
    (hbound : ∀ t : ℝ, 0 ≤ t →
      ∀ᶠ lambda in atTop, ‖exp (t • yosidaApproximation A lambda)‖ ≤ M)
    {t : ℝ} (ht : 0 ≤ t) (x : X) :
    (yosidaLimitSemigroupOfTendsto htend hunif hbound).realOperator t x = yosidaLimit A t x := by
  rw [StronglyContinuousSemigroup.realOperator_def, yosidaLimitSemigroupOfTendsto_apply,
    Real.coe_toNNReal t ht]

/-- The limit semigroup has growth bound `(0, M)`. -/
theorem hasGrowthBound_yosidaLimitSemigroupOfTendsto {A : X →ₗ.[ℝ] X} {M : ℝ} (hM : 1 ≤ M)
    (htend : ∀ t : ℝ, 0 ≤ t → ∀ x : X,
      Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
        (𝓝 (yosidaLimit A t x)))
    (hunif : ∀ (x : X) (T : ℝ), 0 ≤ T →
      TendstoUniformlyOn (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) x)
        (fun t : ℝ => yosidaLimit A t x) atTop (Set.Icc 0 T))
    (hbound : ∀ t : ℝ, 0 ≤ t →
      ∀ᶠ lambda in atTop, ‖exp (t • yosidaApproximation A lambda)‖ ≤ M) :
    (yosidaLimitSemigroupOfTendsto htend hunif hbound).HasGrowthBound 0 M := by
  refine StronglyContinuousSemigroup.hasGrowthBound_of_bound hM fun t _ht => ?_
  rw [zero_mul, Real.exp_zero, mul_one, StronglyContinuousSemigroup.realOperator_def,
    yosidaLimitSemigroupOfTendsto_coe]
  exact norm_yosidaLimitCLMOfTendsto_le hM htend hbound t.toNNReal

/-- The orbits of the limit semigroup are the limits of the Yosida exponentials. -/
theorem tendsto_yosidaLimitSemigroupOfTendsto {A : X →ₗ.[ℝ] X} {M : ℝ}
    (htend : ∀ t : ℝ, 0 ≤ t → ∀ x : X,
      Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
        (𝓝 (yosidaLimit A t x)))
    (hunif : ∀ (x : X) (T : ℝ), 0 ≤ T →
      TendstoUniformlyOn (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) x)
        (fun t : ℝ => yosidaLimit A t x) atTop (Set.Icc 0 T))
    (hbound : ∀ t : ℝ, 0 ≤ t →
      ∀ᶠ lambda in atTop, ‖exp (t • yosidaApproximation A lambda)‖ ≤ M)
    (t : ℝ≥0) (x : X) :
    Tendsto (fun lambda : ℝ => exp ((t : ℝ) • yosidaApproximation A lambda) x) atTop
      (𝓝 (yosidaLimitSemigroupOfTendsto htend hunif hbound t x)) := by
  rw [yosidaLimitSemigroupOfTendsto_apply]
  exact htend t.1 t.coe_nonneg x

end SharedConstruction

namespace IsMDissipative

variable {A : X →ₗ.[ℝ] X}

/-! ## Existence of the limit -/

/-- The defining convergence of the Yosida limit: `exp (t A_lambda) x -> yosidaLimit A t x` as
`lambda -> +∞`, for every nonnegative time `t`.

Completeness turns the compact-time Cauchy estimate into convergence to the chosen value
`limUnder atTop`, which is `yosidaLimit A t x` by definition. -/
theorem tendsto_yosidaLimit (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    {t : ℝ} (ht : 0 ≤ t) (x : X) :
    Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x) atTop
      (𝓝 (yosidaLimit A t x)) :=
  tendsto_yosidaLimit_of_cauchySeq A t x <|
    (hA.exp_yosidaApproximation_uniformCauchySeqOn_compact hdense x ht).cauchySeq
      (Set.right_mem_Icc.mpr ht)

/-- The convergence to the Yosida limit is uniform on every compact time interval. -/
theorem tendstoUniformlyOn_exp_yosidaApproximation (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) (x : X) {T : ℝ} (hT : 0 ≤ T) :
    TendstoUniformlyOn (fun lambda t : ℝ => exp (t • yosidaApproximation A lambda) x)
      (fun t : ℝ => yosidaLimit A t x) atTop (Set.Icc 0 T) :=
  (hA.exp_yosidaApproximation_uniformCauchySeqOn_compact hdense x hT).tendstoUniformlyOn_of_tendsto
    fun _t ht => hA.tendsto_yosidaLimit hdense ht.1 x

/-! ## Linearity and contractivity in the vector variable -/

/-- The Yosida limit is additive in the vector variable. -/
theorem yosidaLimit_add (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    {t : ℝ} (ht : 0 ≤ t) (x y : X) :
    yosidaLimit A t (x + y) = yosidaLimit A t x + yosidaLimit A t y :=
  yosidaLimit_add_of_tendsto (fun u => hA.tendsto_yosidaLimit hdense ht u) x y

/-- The Yosida limit is homogeneous in the vector variable. -/
theorem yosidaLimit_smul (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    {t : ℝ} (ht : 0 ≤ t) (c : ℝ) (x : X) :
    yosidaLimit A t (c • x) = c • yosidaLimit A t x :=
  yosidaLimit_smul_of_tendsto (fun u => hA.tendsto_yosidaLimit hdense ht u) c x

private theorem eventually_norm_exp_smul_yosidaApproximation_le (hA : IsMDissipative A)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᶠ lambda in atTop, ‖exp (t • yosidaApproximation A lambda)‖ ≤ 1 := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with lambda hlambda
  exact norm_exp_smul_yosidaApproximation_le_one
    (hA.mul_norm_resolvent_le_one hlambda) hlambda ht

/-- The Yosida limit is contractive: `‖yosidaLimit A t x‖ ≤ ‖x‖` at every nonnegative time.

Each Yosida exponential is a contraction, and the bound passes to the limit. -/
theorem norm_yosidaLimit_le (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    {t : ℝ} (ht : 0 ≤ t) (x : X) : ‖yosidaLimit A t x‖ ≤ ‖x‖ := by
  simpa using norm_yosidaLimit_le_of_tendsto_of_norm_le
    (hA.tendsto_yosidaLimit hdense ht x)
    (hA.eventually_norm_exp_smul_yosidaApproximation_le ht)

/-! ## The semigroup law and continuity in time -/

/-- **The semigroup law for the Yosida limit.** At nonnegative times,
`yosidaLimit A (s + t) x = yosidaLimit A s (yosidaLimit A t x)`.

The corresponding identity for the approximations is exact; the two error terms it produces are
controlled by the contractivity of `exp (s A_lambda)` and by the two defining convergences. -/
theorem yosidaLimit_time_add (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : X) :
    yosidaLimit A (s + t) x = yosidaLimit A s (yosidaLimit A t x) :=
  yosidaLimit_time_add_of_tendsto_of_norm_le x
    (hA.tendsto_yosidaLimit hdense ht x)
    (hA.tendsto_yosidaLimit hdense hs (yosidaLimit A t x))
    (hA.tendsto_yosidaLimit hdense (add_nonneg hs ht) x)
    (hA.eventually_norm_exp_smul_yosidaApproximation_le hs)

/-- The Yosida limit is continuous in time on every compact interval `[0, T]`: it is a uniform
limit there of the continuous orbits of the bounded approximations. -/
theorem continuousOn_yosidaLimit_Icc (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    (x : X) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t : ℝ => yosidaLimit A t x) (Set.Icc 0 T) :=
  continuousOn_yosidaLimit_Icc_of_tendstoUniformlyOn A x
    (hA.tendstoUniformlyOn_exp_yosidaApproximation hdense x hT)

/-- The Yosida limit is continuous in time on the whole nonnegative half-line. -/
theorem continuousOn_yosidaLimit (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    (x : X) : ContinuousOn (fun t : ℝ => yosidaLimit A t x) (Set.Ici 0) :=
  continuousOn_Ici_of_forall_continuousOn_Icc fun _T hT =>
    hA.continuousOn_yosidaLimit_Icc hdense x hT

/-- Strong continuity at time `0` of the Yosida limit, in the nonnegative-time parametrisation
used by `StronglyContinuousSemigroup`. -/
private theorem continuousAt_yosidaLimit_zero (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) (x : X) :
    ContinuousAt (fun t : ℝ≥0 => yosidaLimit A t x) 0 :=
  continuousAt_nnreal_zero_of_continuousOn_Ici (hA.continuousOn_yosidaLimit hdense x)

/-! ## The contraction semigroup -/

/-- **The contraction semigroup produced by the Yosida construction.** For a densely defined
m-dissipative operator `A` on a real Banach space, the limits of the Yosida exponentials form a
strongly continuous contraction semigroup. -/
def yosidaLimitSemigroup (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X)) :
    ContractionSemigroup X where
  toStronglyContinuousSemigroup := yosidaLimitSemigroupOfTendsto
    (fun _t ht x => hA.tendsto_yosidaLimit hdense ht x)
    (fun x _T hT => hA.tendstoUniformlyOn_exp_yosidaApproximation hdense x hT)
    (fun _t ht => hA.eventually_norm_exp_smul_yosidaApproximation_le ht)
  contracting t := norm_yosidaLimitCLMOfTendsto_le le_rfl
    (fun _t ht x => hA.tendsto_yosidaLimit hdense ht x)
    (fun _t ht => hA.eventually_norm_exp_smul_yosidaApproximation_le ht) t

@[simp]
theorem yosidaLimitSemigroup_apply (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    (t : ℝ≥0) (x : X) : hA.yosidaLimitSemigroup hdense t x = yosidaLimit A t x :=
  (rfl)

/-- The real-time orbit of `yosidaLimitSemigroup` is the Yosida limit at nonnegative times. -/
@[simp]
theorem yosidaLimitSemigroup_realOperator_apply (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) {t : ℝ} (ht : 0 ≤ t) (x : X) :
    (hA.yosidaLimitSemigroup hdense).realOperator t x = yosidaLimit A t x := by
  rw [StronglyContinuousSemigroup.realOperator_def,
    ContractionSemigroup.toStronglyContinuousSemigroup_apply, yosidaLimitSemigroup_apply,
    Real.coe_toNNReal t ht]

/-- The orbits of `yosidaLimitSemigroup` are exactly the limits of the Yosida exponentials. -/
theorem tendsto_yosidaLimitSemigroup (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    (t : ℝ≥0) (x : X) :
    Tendsto (fun lambda : ℝ => exp ((t : ℝ) • yosidaApproximation A lambda) x) atTop
      (𝓝 (hA.yosidaLimitSemigroup hdense t x)) := by
  rw [yosidaLimitSemigroup_apply]
  exact hA.tendsto_yosidaLimit hdense t.coe_nonneg x

/-- **A densely defined m-dissipative operator gives rise to a contraction semigroup**, obtained
as the strong limit of the semigroups generated by its Yosida approximations.

This is the existence half of the Lumer--Phillips generation theorem; the generator of the
resulting semigroup is identified with `A` in
`TauCeti/Analysis/Semigroups/Generation/LumerPhillips.lean`. -/
theorem exists_contractionSemigroup (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) :
    ∃ S : ContractionSemigroup X, ∀ (t : ℝ≥0) (x : X),
      Tendsto (fun lambda : ℝ => exp ((t : ℝ) • yosidaApproximation A lambda) x) atTop
        (𝓝 (S t x)) :=
  ⟨hA.yosidaLimitSemigroup hdense, hA.tendsto_yosidaLimitSemigroup hdense⟩

end IsMDissipative

end TauCeti.Semigroups

end
