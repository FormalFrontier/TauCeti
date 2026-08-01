/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Growth bounds for strongly continuous semigroups

This file contains exponential growth bounds for C₀-semigroups, including the
contraction case and the existence of a finite exponential type.

## References
Ported and adapted (Apache 2.0) from `mrdouglasny/hille-yosida`; references include
Engel--Nagel, Linares, Pazy, Hille, and Yosida.
-/

public section

noncomputable section

open scoped Topology NNReal

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-! ## Exponential growth bounds -/

/-- A C₀-semigroup has exponential growth bound `(ω, M)`, with `M ≥ 1`. -/
def StronglyContinuousSemigroup.HasGrowthBound
    (S : StronglyContinuousSemigroup X) (ω : ℝ) (M : ℝ) : Prop :=
  1 ≤ M ∧ ∀ (t : ℝ), 0 ≤ t → ‖S.realOperator t‖ ≤ M * Real.exp (ω * t)

omit [CompleteSpace X] in
/-- The multiplicative constant in a growth bound is at least one. -/
theorem StronglyContinuousSemigroup.HasGrowthBound.one_le
    {S : StronglyContinuousSemigroup X} {ω M : ℝ} (hb : S.HasGrowthBound ω M) :
    1 ≤ M := by
  unfold StronglyContinuousSemigroup.HasGrowthBound at hb
  exact hb.1

omit [CompleteSpace X] in
/-- The operator-norm estimate supplied by a growth bound. -/
theorem StronglyContinuousSemigroup.HasGrowthBound.bound
    {S : StronglyContinuousSemigroup X} {ω M : ℝ} (hb : S.HasGrowthBound ω M)
    (t : ℝ) (ht : 0 ≤ t) : ‖S.realOperator t‖ ≤ M * Real.exp (ω * t) := by
  unfold StronglyContinuousSemigroup.HasGrowthBound at hb
  exact hb.2 t ht

omit [CompleteSpace X] in
/-- Constructor for a growth bound from the multiplicative lower bound and operator-norm
estimate. -/
public theorem StronglyContinuousSemigroup.hasGrowthBound_of_bound
    {S : StronglyContinuousSemigroup X} {ω M : ℝ} (hM : 1 ≤ M)
    (hbound : ∀ (t : ℝ), 0 ≤ t → ‖S.realOperator t‖ ≤ M * Real.exp (ω * t)) :
    S.HasGrowthBound ω M := by
  unfold StronglyContinuousSemigroup.HasGrowthBound
  exact ⟨hM, hbound⟩

omit [CompleteSpace X] in
/-- A growth bound can be weakened by increasing both the exponential rate and the multiplicative
constant. -/
theorem StronglyContinuousSemigroup.HasGrowthBound.mono
    {S : StronglyContinuousSemigroup X} {ω M ω' M' : ℝ}
    (hb : S.HasGrowthBound ω M) (hω : ω ≤ ω') (hM : M ≤ M') :
    S.HasGrowthBound ω' M' := by
  refine ⟨hb.one_le.trans hM, fun t ht => ?_⟩
  have hM_nonneg : 0 ≤ M := zero_le_one.trans hb.one_le
  have hexp : Real.exp (ω * t) ≤ Real.exp (ω' * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hω ht)
  exact (hb.bound t ht).trans
    (mul_le_mul hM hexp (Real.exp_nonneg _) (hM_nonneg.trans hM))

omit [CompleteSpace X] in
/-- A growth bound can be weakened by increasing the exponential rate. -/
theorem StronglyContinuousSemigroup.HasGrowthBound.mono_omega
    {S : StronglyContinuousSemigroup X} {ω M ω' : ℝ} (hb : S.HasGrowthBound ω M) (hω : ω ≤ ω') :
    S.HasGrowthBound ω' M :=
  hb.mono hω le_rfl

omit [CompleteSpace X] in
/-- A growth bound can be weakened by increasing the multiplicative constant. -/
theorem StronglyContinuousSemigroup.HasGrowthBound.mono_const
    {S : StronglyContinuousSemigroup X} {ω M M' : ℝ} (hb : S.HasGrowthBound ω M) (hM : M ≤ M') :
    S.HasGrowthBound ω M' :=
  hb.mono le_rfl hM

omit [CompleteSpace X] in
/-- A contraction semigroup has growth bound `(0, 1)`. -/
theorem ContractionSemigroup.hasGrowthBound (S : ContractionSemigroup X) :
    S.toStronglyContinuousSemigroup.HasGrowthBound 0 1 :=
  ⟨le_rfl, fun t ht => by simpa using S.contracting_real t ht⟩

omit [CompleteSpace X] in
/-- A contraction semigroup has every nonnegative exponential growth rate with constant `1`. -/
theorem ContractionSemigroup.hasGrowthBound_of_nonneg_omega
    (S : ContractionSemigroup X) {ω : ℝ} (hω : 0 ≤ ω) :
    S.toStronglyContinuousSemigroup.HasGrowthBound ω 1 :=
  S.hasGrowthBound.mono_omega hω

omit [CompleteSpace X] in
/-- A contraction semigroup has growth bound `(0, M)` for every `M ≥ 1`. -/
theorem ContractionSemigroup.hasGrowthBound_of_one_le_const
    (S : ContractionSemigroup X) {M : ℝ} (hM : 1 ≤ M) :
    S.toStronglyContinuousSemigroup.HasGrowthBound 0 M :=
  S.hasGrowthBound.mono_const hM

omit [CompleteSpace X] in
/-- A contraction semigroup has growth bound `(ω, M)` whenever `0 ≤ ω` and `1 ≤ M`. -/
theorem ContractionSemigroup.hasGrowthBound_of_nonneg_omega_of_one_le_const
    (S : ContractionSemigroup X) {ω M : ℝ} (hω : 0 ≤ ω) (hM : 1 ≤ M) :
    S.toStronglyContinuousSemigroup.HasGrowthBound ω M :=
  S.hasGrowthBound.mono hω hM


/-! ## Growth Bounds and Exponential Type -/

/-- Every C₀-semigroup has a finite exponential growth bound
([EN] Prop. I.5.5, [Linares] Thm. 1). -/
theorem StronglyContinuousSemigroup.existsGrowthBound (S : StronglyContinuousSemigroup X) :
    ∃ (ω : ℝ) (M : ℝ), S.HasGrowthBound ω M := by
  obtain ⟨M, hM1, hMbound⟩ := S.normBoundedOnUnitInterval
  have hM_pos : 0 < M := by linarith
  refine ⟨Real.log M, M, hM1, fun t ht => ?_⟩
  -- Integer-time operator norm bound by induction: ‖S(k)‖ ≤ M^k
  have h_int_bound : ∀ (k : ℕ), ‖S.realOperator (↑k : ℝ)‖ ≤ M ^ k := by
    intro k; induction k with
    | zero =>
      simp only [Nat.cast_zero, S.realOperator_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ k ih =>
      calc ‖S.realOperator (↑(k + 1) : ℝ)‖
          = ‖S.realOperator (1 + ↑k)‖ := by
            rw [Nat.cast_add, Nat.cast_one, add_comm]
        _ ≤ ‖S.realOperator 1‖ * ‖S.realOperator ↑k‖ :=
            S.norm_realOperator_add_le 1 ↑k (by linarith) (Nat.cast_nonneg k)
        _ ≤ M * M ^ k :=
            mul_le_mul (hMbound 1 (by linarith) le_rfl) ih (norm_nonneg _) (by linarith)
        _ = M ^ (k + 1) := by ring
  set n := ⌊t⌋₊ with hn_def
  have hn_le : (↑n : ℝ) ≤ t := Nat.floor_le ht
  have hfrac_nn : 0 ≤ t - ↑n := sub_nonneg.mpr hn_le
  have hfrac_le1 : t - ↑n ≤ 1 := by
    have := Nat.lt_floor_add_one t; linarith
  calc ‖S.realOperator t‖
      = ‖S.realOperator ((t - ↑n) + ↑n)‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖S.realOperator (t - ↑n)‖ * ‖S.realOperator ↑n‖ :=
        S.norm_realOperator_add_le _ _ hfrac_nn (Nat.cast_nonneg n)
    _ ≤ M * M ^ n :=
        mul_le_mul (hMbound _ hfrac_nn hfrac_le1) (h_int_bound n) (norm_nonneg _) (by linarith)
    _ ≤ M * Real.exp (Real.log M * t) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        calc (M : ℝ) ^ n
            = Real.exp (↑n * Real.log M) := by
              rw [Real.exp_nat_mul, Real.exp_log hM_pos]
          _ ≤ Real.exp (Real.log M * t) := by
              apply Real.exp_le_exp.mpr
              calc ↑n * Real.log M ≤ t * Real.log M :=
                    mul_le_mul_of_nonneg_right hn_le (Real.log_nonneg hM1)
                _ = Real.log M * t := by ring

/-- A C₀-semigroup admits a growth bound with exponent at least any prescribed real number. -/
theorem StronglyContinuousSemigroup.existsGrowthBound_ge_omega
    (S : StronglyContinuousSemigroup X) (ω₀ : ℝ) :
    ∃ (ω : ℝ) (M : ℝ), ω₀ ≤ ω ∧ S.HasGrowthBound ω M := by
  obtain ⟨ω, M, hb⟩ := S.existsGrowthBound
  refine ⟨max ω ω₀, M, le_max_right _ _, hb.mono_omega ?_⟩
  exact le_max_left _ _

/-- A C₀-semigroup admits a growth bound with multiplicative constant at least any prescribed
real number. -/
theorem StronglyContinuousSemigroup.existsGrowthBound_ge_const
    (S : StronglyContinuousSemigroup X) (M₀ : ℝ) :
    ∃ (ω : ℝ) (M : ℝ), M₀ ≤ M ∧ S.HasGrowthBound ω M := by
  obtain ⟨ω, M, hb⟩ := S.existsGrowthBound
  refine ⟨ω, max M M₀, le_max_right _ _, hb.mono_const ?_⟩
  exact le_max_left _ _

/-- A C₀-semigroup admits a growth bound whose exponent and multiplicative constant are both at
least prescribed lower bounds. -/
theorem StronglyContinuousSemigroup.existsGrowthBound_ge
    (S : StronglyContinuousSemigroup X) (ω₀ M₀ : ℝ) :
    ∃ (ω : ℝ) (M : ℝ), ω₀ ≤ ω ∧ M₀ ≤ M ∧ S.HasGrowthBound ω M := by
  obtain ⟨ω, M, hb⟩ := S.existsGrowthBound
  refine ⟨max ω ω₀, max M M₀, le_max_right _ _, le_max_right _ _, ?_⟩
  exact hb.mono (le_max_left _ _) (le_max_left _ _)

end TauCeti.Semigroups

end
