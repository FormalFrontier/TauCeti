/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Generation.Yosida.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# The contraction semigroup obtained as a limit of Yosida semigroups

For a densely defined m-dissipative operator `A` on a real Banach space, the Yosida
approximations `A_lambda = lambda ^ 2 R(lambda, A) - lambda I` are bounded, and the exponentials
`exp (t A_lambda) x` are Cauchy as `lambda -> +∞`, uniformly on every compact time interval
by `TauCeti.Semigroups.IsMDissipative.exp_yosidaApproximation_uniformCauchySeqOn_compact`. This
file takes the limit of that Cauchy family.

Completeness of the Banach space turns the Cauchy estimate into a limit vector
`yosidaLimit A t x`. The definition is the chosen value `limUnder atTop` of
`exp (t A_lambda) x`, so it makes sense for every real `t`, but it is only *proved* to be the
limit when `A` is m-dissipative with dense domain and `t ≥ 0`; every statement below that appeals
to convergence carries those hypotheses. On that range it is linear and contractive in `x`,
satisfies `S(0) = I` and `S(s + t) = S(s) S(t)`, and — because the convergence is uniform on
compact time intervals — depends continuously on `t`. Packaging these facts gives a genuine
contraction semigroup `yosidaLimitSemigroup`.

Note that the semigroup laws are proved for the *limit* rather than transported from the
approximations: `A` need not generate anything a priori, so every statement below is about the
family `exp (t A_lambda)` and its limit.

## Main definitions

* `TauCeti.Semigroups.yosidaLimit`: the value chosen from the family `exp (t A_lambda) x` as
  `lambda -> ∞`, which is its limit at nonnegative times.
* `TauCeti.Semigroups.IsMDissipative.yosidaLimitSemigroup`: the resulting contraction semigroup.

## Main results

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

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section II.3.5;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Chapter 1, Theorem 4.3.
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
proved to be the limit exactly when `A` is m-dissipative with dense domain and `t ≥ 0` — there
the general compact-time Cauchy estimate gives convergence, and
`IsMDissipative.tendsto_yosidaLimit` records it. Every lemma below that appeals to the limit
property carries those hypotheses explicitly. -/
def yosidaLimit (A : X →ₗ.[ℝ] X) (t : ℝ) (x : X) : X :=
  limUnder atTop fun lambda : ℝ => exp (t • yosidaApproximation A lambda) x

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
  ((hA.exp_yosidaApproximation_uniformCauchySeqOn_compact hdense x ht).cauchySeq
    (Set.right_mem_Icc.mpr ht)).tendsto_limUnder

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
    yosidaLimit A t (x + y) = yosidaLimit A t x + yosidaLimit A t y := by
  refine tendsto_nhds_unique (hA.tendsto_yosidaLimit hdense ht (x + y)) ?_
  simpa only [map_add] using
    (hA.tendsto_yosidaLimit hdense ht x).add (hA.tendsto_yosidaLimit hdense ht y)

/-- The Yosida limit is homogeneous in the vector variable. -/
theorem yosidaLimit_smul (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    {t : ℝ} (ht : 0 ≤ t) (c : ℝ) (x : X) :
    yosidaLimit A t (c • x) = c • yosidaLimit A t x := by
  refine tendsto_nhds_unique (hA.tendsto_yosidaLimit hdense ht (c • x)) ?_
  simpa only [map_smul] using (hA.tendsto_yosidaLimit hdense ht x).const_smul c

/-- The Yosida limit is contractive: `‖yosidaLimit A t x‖ ≤ ‖x‖` at every nonnegative time.

Each Yosida exponential is a contraction, and the bound passes to the limit. -/
theorem norm_yosidaLimit_le (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    {t : ℝ} (ht : 0 ≤ t) (x : X) : ‖yosidaLimit A t x‖ ≤ ‖x‖ := by
  refine le_of_tendsto (hA.tendsto_yosidaLimit hdense ht x).norm ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with lambda hlambda
  calc ‖exp (t • yosidaApproximation A lambda) x‖
      ≤ ‖exp (t • yosidaApproximation A lambda)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖x‖ := by
        gcongr
        exact norm_exp_smul_yosidaApproximation_le_one
          (hA.mul_norm_resolvent_le_one hlambda) hlambda ht
    _ = ‖x‖ := one_mul _

/-! ## The semigroup law and continuity in time -/

/-- **The semigroup law for the Yosida limit.** At nonnegative times,
`yosidaLimit A (s + t) x = yosidaLimit A s (yosidaLimit A t x)`.

The corresponding identity for the approximations is exact; the two error terms it produces are
controlled by the contractivity of `exp (s A_lambda)` and by the two defining convergences. -/
theorem yosidaLimit_time_add (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : X) :
    yosidaLimit A (s + t) x = yosidaLimit A s (yosidaLimit A t x) := by
  set y := yosidaLimit A t x with hy
  set z := yosidaLimit A s y with hz
  have hstep : Tendsto (fun lambda : ℝ => exp ((s + t) • yosidaApproximation A lambda) x - z)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun lambda : ℝ =>
      ‖exp (t • yosidaApproximation A lambda) x - y‖ +
        ‖exp (s • yosidaApproximation A lambda) y - z‖) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with lambda hlambda
      have hcontr : ‖exp (s • yosidaApproximation A lambda)‖ ≤ 1 :=
        norm_exp_smul_yosidaApproximation_le_one
          (hA.mul_norm_resolvent_le_one hlambda) hlambda hs
      have hsplit : exp ((s + t) • yosidaApproximation A lambda) x - z =
          exp (s • yosidaApproximation A lambda)
              (exp (t • yosidaApproximation A lambda) x - y) +
            (exp (s • yosidaApproximation A lambda) y - z) := by
        rw [map_sub, exp_add_smul_apply]
        abel
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      gcongr
      calc ‖exp (s • yosidaApproximation A lambda)
            (exp (t • yosidaApproximation A lambda) x - y)‖
          ≤ ‖exp (s • yosidaApproximation A lambda)‖ *
              ‖exp (t • yosidaApproximation A lambda) x - y‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖exp (t • yosidaApproximation A lambda) x - y‖ := by
            simpa using mul_le_mul_of_nonneg_right hcontr (norm_nonneg _)
    · have h1 : Tendsto
          (fun lambda : ℝ => ‖exp (t • yosidaApproximation A lambda) x - y‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.mp (hA.tendsto_yosidaLimit hdense ht x)
      have h2 : Tendsto
          (fun lambda : ℝ => ‖exp (s • yosidaApproximation A lambda) y - z‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.mp (hA.tendsto_yosidaLimit hdense hs y)
      simpa using h1.add h2
  refine tendsto_nhds_unique (hA.tendsto_yosidaLimit hdense (add_nonneg hs ht) x) ?_
  simpa using hstep.add_const z

/-- The Yosida limit is continuous in time on every compact interval `[0, T]`: it is a uniform
limit there of the continuous orbits of the bounded approximations. -/
theorem continuousOn_yosidaLimit_Icc (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    (x : X) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t : ℝ => yosidaLimit A t x) (Set.Icc 0 T) :=
  (hA.tendstoUniformlyOn_exp_yosidaApproximation hdense x hT).continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun lambda =>
      (((differentiable_exp_smul_const ℝ (yosidaApproximation A lambda)).continuous).clm_apply
        continuous_const).continuousOn))

/-- The Yosida limit is continuous in time on the whole nonnegative half-line. -/
theorem continuousOn_yosidaLimit (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    (x : X) : ContinuousOn (fun t : ℝ => yosidaLimit A t x) (Set.Ici 0) := by
  intro t ht
  have ht' : (0 : ℝ) ≤ t := ht
  have hmem : Set.Icc 0 (t + 1) ∈ 𝓝[Set.Ici (0 : ℝ)] t := by
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Set.Iio (t + 1), Iio_mem_nhds (by linarith), ?_⟩
    rintro u ⟨hu₁, hu₂⟩
    exact ⟨hu₂, le_of_lt hu₁⟩
  exact (hA.continuousOn_yosidaLimit_Icc hdense x (by linarith : (0 : ℝ) ≤ t + 1) t
    ⟨ht', by linarith⟩).mono_of_mem_nhdsWithin hmem

/-- Strong continuity at time `0` of the Yosida limit, in the nonnegative-time parametrisation
used by `StronglyContinuousSemigroup`. -/
private theorem continuousAt_yosidaLimit_zero (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) (x : X) :
    ContinuousAt (fun t : ℝ≥0 => yosidaLimit A t x) 0 := by
  have hIci : ContinuousWithinAt (fun t : ℝ => yosidaLimit A t x) (Set.Ici 0)
      (((0 : ℝ≥0) : ℝ)) := by
    simpa using hA.continuousOn_yosidaLimit hdense x 0 (Set.mem_Ici.mpr le_rfl)
  have hcoe : ContinuousWithinAt (fun t : ℝ≥0 => (t : ℝ)) Set.univ 0 :=
    NNReal.continuous_coe.continuousWithinAt
  exact continuousWithinAt_univ _ _ |>.mp
    (hIci.comp hcoe fun t _ => t.coe_nonneg)

/-! ## The contraction semigroup -/

/-- The Yosida limit at a nonnegative time, packaged as a bounded operator on `X`. This is the
scaffolding of `yosidaLimitSemigroup` below, which is the public form of the construction. -/
private def yosidaLimitCLM (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X)) (t : ℝ≥0) :
    X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := fun x => yosidaLimit A t x
      map_add' := hA.yosidaLimit_add hdense t.coe_nonneg
      map_smul' := hA.yosidaLimit_smul hdense t.coe_nonneg }
    1 fun x => by simpa using hA.norm_yosidaLimit_le hdense t.coe_nonneg x

-- `yosidaLimitCLM` and `yosidaLimitSemigroup` below are deliberately not `@[expose]`d, so their
-- characteristic lemmas are written `(rfl)` rather than `rfl`: the parentheses opt out of
-- exporting the definitional equality that these lemmas exist to replace.
@[simp]
private theorem yosidaLimitCLM_apply (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    (t : ℝ≥0) (x : X) : hA.yosidaLimitCLM hdense t x = yosidaLimit A t x :=
  (rfl)

/-- Each Yosida limit operator is a contraction. -/
private theorem norm_yosidaLimitCLM_le (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    (t : ℝ≥0) : ‖hA.yosidaLimitCLM hdense t‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **The contraction semigroup produced by the Yosida construction.** For a densely defined
m-dissipative operator `A` on a real Banach space, the limits of the Yosida exponentials form a
strongly continuous contraction semigroup. -/
def yosidaLimitSemigroup (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X)) :
    ContractionSemigroup X where
  toFun := hA.yosidaLimitCLM hdense
  map_zero' := by
    ext x
    simp
  map_add' s t := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, yosidaLimitCLM_apply, NNReal.coe_add]
    exact hA.yosidaLimit_time_add hdense s.coe_nonneg t.coe_nonneg x
  continuousAt_zero' x := by
    simpa only [yosidaLimitCLM_apply] using hA.continuousAt_yosidaLimit_zero hdense x
  contracting t := hA.norm_yosidaLimitCLM_le hdense t

@[simp]
theorem yosidaLimitSemigroup_apply (hA : IsMDissipative A) (hdense : Dense (A.domain : Set X))
    (t : ℝ≥0) (x : X) : hA.yosidaLimitSemigroup hdense t x = yosidaLimit A t x :=
  (rfl)

/-- The real-time orbit of `yosidaLimitSemigroup` is the Yosida limit at nonnegative times. -/
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
