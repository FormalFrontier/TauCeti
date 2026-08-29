/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.ValuativeRel

/-!
# `ℚ_[p]` is a nonarchimedean local field

Mathlib equips `ℚ_[p]` with a valuative relation, induced by the multiplicative `p`-adic
valuation `Padic.mulValuation`, but until now its topology was only the `p`-adic norm topology:
neither `IsValuativeTopology ℚ_[p]` nor `IsNonarchimedeanLocalField ℚ_[p]` existed. This file
supplies both instances, for every prime `p`, together with the bridges that make the
local-field API of `Mathlib/NumberTheory/LocalField/Basic.lean` usable on `ℚ_[p]`.

## Main results

* `TauCeti.Padic.mem_nhds_zero_iff`: a set is a neighbourhood of `0` exactly when it contains a
  valuation ball `{z | ValuativeRel.valuation ℚ_[p] z < γ}`. This identifies the `p`-adic norm
  topology with the valuative topology and drives the instances.
* `TauCeti.Padic.instIsValuativeTopology` and `TauCeti.Padic.instIsNonarchimedeanLocalField`:
  the two instances.
* `TauCeti.Padic.uniformSpace_eq_rightUniformSpace`: the metric uniformity agrees with the right
  uniformity `IsTopologicalAddGroup.rightUniformSpace` of the valuative topology. The agreement
  is a lemma, so the completeness API of `IsNonarchimedeanLocalField` (`CompleteSpace 𝒪[K]`,
  `IsAdicComplete 𝓂[K] 𝒪[K]`) is available for the metric uniformity without relying on an
  accident of unification.
* `TauCeti.Padic.valuation_lt_iff`, `TauCeti.Padic.valuation_le_iff` and
  `TauCeti.Padic.mem_integer_iff_norm_le_one`: the canonical valuation and the integer ring
  `𝒪[ℚ_[p]]` in terms of `Padic.mulValuation`.
* `TauCeti.Padic.integer_eq_padicIntSubring`: `𝒪[ℚ_[p]] = PadicInt.subring p`, so the
  compactness and adic completeness of `𝒪[ℚ_[p]]` transfer to `ℤ_[p]`.

## References

[Serre, *Local Fields*, Chapter II]

## Tags

local field, p-adic
-/

public section

open scoped Topology

open Padic ValuativeRel WithZero

namespace TauCeti.Padic

variable {p : ℕ} [hp : Fact p.Prime]

private theorem p_pos (p : ℕ) [h : Fact p.Prime] : (0 : ℝ) < p := by exact_mod_cast h.out.pos

private theorem p_one_lt (p : ℕ) [h : Fact p.Prime] : 1 < (p : ℝ) := by
  exact_mod_cast h.out.one_lt

private theorem p_pow_ne_zero (p : ℕ) [h : Fact p.Prime] (n : ℕ) :
    ((p : ℚ_[p]) ^ n : ℚ_[p]) ≠ 0 :=
  pow_ne_zero n (norm_pos_iff.mp (by rw [norm_p]; exact inv_pos.mpr (p_pos p)))

/-! ### Elementary values of the `p`-adic valuations -/

/-- The `p`-adic valuation of `p ^ n` is `n`. -/
theorem valuation_p_pow (n : ℕ) : ((p : ℚ_[p]) ^ n).valuation = n := by
  rw [valuation_pow, valuation_p, mul_one]

/-- The multiplicative `p`-adic valuation of `p ^ n` is `exp (-(n : ℤ))`. -/
theorem mulValuation_p_pow (n : ℕ) :
    mulValuation ((p : ℚ_[p]) ^ n) = exp (-(n : ℤ)) := by
  have hp0 := p_pow_ne_zero p n
  simp [hp0]

/-- Away from zero, the multiplicative `p`-adic valuation is the exponential of the negative
`p`-adic valuation. -/
private theorem mulValuation_eq_exp {x : ℚ_[p]} (hx : x ≠ 0) :
    mulValuation x = exp (-(x.valuation : ℤ)) := by simp [hx]

/-! ### The canonical valuation in terms of `mulValuation` -/

/-- The canonical valuation of the valuative relation on `ℚ_[p]` compares exactly as the
multiplicative `p`-adic valuation does: the two valuations are compatible with the relation,
hence equivalent. -/
theorem valuation_lt_iff {x y : ℚ_[p]} :
    ValuativeRel.valuation ℚ_[p] x < ValuativeRel.valuation ℚ_[p] y ↔
      mulValuation x < mulValuation y :=
  (isEquiv (ValuativeRel.valuation ℚ_[p]) mulValuation).lt_iff_lt

/-- The canonical valuation of the valuative relation on `ℚ_[p]` compares exactly as the
multiplicative `p`-adic valuation does. -/
theorem valuation_le_iff {x y : ℚ_[p]} :
    ValuativeRel.valuation ℚ_[p] x ≤ ValuativeRel.valuation ℚ_[p] y ↔
      mulValuation x ≤ mulValuation y :=
  isEquiv (ValuativeRel.valuation ℚ_[p]) mulValuation x y

/-- An element of `ℚ_[p]` lies in the integer ring `𝒪[ℚ_[p]]` of the valuative relation exactly
when its norm is at most one, i.e. when it is a `p`-adic integer. -/
theorem mem_integer_iff_norm_le_one (x : ℚ_[p]) : x ∈ 𝒪[ℚ_[p]] ↔ ‖x‖ ≤ 1 := by
  have key : ∀ y : ℚ_[p], mulValuation y ≤ 1 ↔ ‖y‖ ≤ 1 := by
    intro y
    by_cases hy0 : y = 0
    · simp [hy0]
    · rw [mulValuation_eq_exp hy0, ← exp_zero, exp_le_exp, norm_le_one_iff_val_nonneg]
      constructor <;> omega
  rw [Valuation.mem_integer_iff]
  exact ((isEquiv (ValuativeRel.valuation ℚ_[p]) mulValuation).le_one_iff_le_one).trans (key x)

/-- The integer ring `𝒪[ℚ_[p]]` of the valuative relation is the ring of `p`-adic integers. -/
theorem integer_eq_padicIntSubring : 𝒪[ℚ_[p]] = PadicInt.subring p := by
  ext x
  exact (mem_integer_iff_norm_le_one x).trans Iff.rfl

/-! ### The valuative topology -/

/-- A set in `ℚ_[p]` is a neighbourhood of zero iff it contains a valuation ball
`{z | ValuativeRel.valuation ℚ_[p] z < γ}` with `γ` a unit of the value group. This says that
the `p`-adic norm topology is the valuative topology of the relation `ValuativeRel ℚ_[p]`. -/
theorem mem_nhds_zero_iff (s : Set ℚ_[p]) :
    s ∈ 𝓝 (0 : ℚ_[p]) ↔
      ∃ γ : (ValueGroupWithZero ℚ_[p])ˣ, {z | ValuativeRel.valuation ℚ_[p] z < γ} ⊆ s := by
  constructor
  · intro hs
    obtain ⟨ε, hε, hsub⟩ := (Metric.nhds_basis_ball (x := (0 : ℚ_[p]))).mem_iff.mp hs
    have hp0r : (0 : ℝ) < p := p_pos p
    obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
    refine ⟨Units.mk0 (ValuativeRel.valuation ℚ_[p] ((p : ℚ_[p]) ^ n))
      ((ValuativeRel.valuation ℚ_[p]).ne_zero_iff.mpr (p_pow_ne_zero p n)), ?_⟩
    calc {z | ValuativeRel.valuation ℚ_[p] z < ValuativeRel.valuation ℚ_[p] ((p : ℚ_[p]) ^ n)}
        ⊆ Metric.ball (0 : ℚ_[p]) ((p : ℝ) ^ (-(n : ℤ))) := by
          intro z hz
          by_cases hz0 : z = 0
          · simp only [hz0, Metric.mem_ball, dist_zero_right, norm_zero]
            exact zpow_pos hp0r _
          · have hmv : mulValuation z < mulValuation ((p : ℚ_[p]) ^ n) :=
              valuation_lt_iff.mp hz
            rw [mulValuation_eq_exp hz0, mulValuation_p_pow, exp_lt_exp] at hmv
            rw [Metric.mem_ball, dist_zero_right, norm_eq_zpow_neg_valuation hz0,
              zpow_lt_zpow_iff_right₀ (p_one_lt p)]
            omega
      _ ⊆ Metric.ball (0 : ℚ_[p]) ε := Metric.ball_subset_ball hn.le
      _ ⊆ s := hsub
  · rintro ⟨γ, hγ⟩
    have hγ0 : (γ : ValueGroupWithZero ℚ_[p]) ≠ 0 := Units.ne_zero γ
    obtain ⟨w, hwv⟩ := valuation_surjective (γ : ValueGroupWithZero ℚ_[p])
    rw [← hwv] at hγ hγ0
    have hw : w ≠ 0 := fun h0 => hγ0 (by rw [h0, map_zero])
    have hsub : Metric.ball (0 : ℚ_[p]) ‖w‖ ⊆
        {z | ValuativeRel.valuation ℚ_[p] z < ValuativeRel.valuation ℚ_[p] w} := by
      intro z hz
      by_cases hz0 : z = 0
      · simp only [hz0, map_zero, Set.mem_ofPred_eq]
        exact zero_lt_iff.mpr hγ0
      · have hz' : ‖z‖ < ‖w‖ := by simpa only [Metric.mem_ball, dist_zero_right] using hz
        rw [norm_eq_zpow_neg_valuation hz0, norm_eq_zpow_neg_valuation hw,
          zpow_lt_zpow_iff_right₀ (p_one_lt p)] at hz'
        simp only [Set.mem_ofPred_eq]
        rw [valuation_lt_iff, mulValuation_eq_exp hz0, mulValuation_eq_exp hw, exp_lt_exp]
        omega
    exact Filter.mem_of_superset (Metric.ball_mem_nhds _ (norm_pos_iff.mpr hw)) (hsub.trans hγ)

/-- **The `p`-adic norm topology is the valuative topology.** -/
instance instIsValuativeTopology : IsValuativeTopology ℚ_[p] := by
  have : ContinuousConstVAdd ℚ_[p] ℚ_[p] := ⟨continuous_const_add⟩
  exact IsValuativeTopology.of_zero (mem_nhds_zero_iff)

/-- **`ℚ_[p]` is a nonarchimedean local field.** Local compactness comes from the compactness of
`ℤ_[p]` (`PadicInt.compactSpace`), which is a neighbourhood of zero in the ultrametric `ℚ_[p]`;
nontriviality of the valuation is Mathlib's `Padic` instance. -/
instance instIsNonarchimedeanLocalField : IsNonarchimedeanLocalField ℚ_[p] where
  toIsValuativeTopology := instIsValuativeTopology

/-! ### The uniformity -/

/-- The metric uniformity on `ℚ_[p]` agrees with the right uniformity of the valuative topology.
Through the uniform-space API of `IsNonarchimedeanLocalField` this makes every completeness
statement about `𝒪[ℚ_[p]]` and `𝓂[ℚ_[p]]` a statement about the metric uniformity, as a lemma
rather than an accident of unification. -/
theorem uniformSpace_eq_rightUniformSpace :
    IsTopologicalAddGroup.rightUniformSpace ℚ_[p] = (inferInstance : UniformSpace ℚ_[p]) :=
  IsUniformAddGroup.rightUniformSpace_eq

/-! ### Consequences for the integer ring -/

/-- The integer ring `𝒪[ℚ_[p]]` is adically complete for its maximal ideal. With
`integer_eq_padicIntSubring` this is Mathlib's `PadicInt` adic completeness, now carried by the
metric uniformity that the valuative topology agrees with. -/
theorem isAdicComplete : IsAdicComplete 𝓂[ℚ_[p]] 𝒪[ℚ_[p]] := inferInstance

end TauCeti.Padic
