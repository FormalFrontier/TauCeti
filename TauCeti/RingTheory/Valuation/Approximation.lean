/-
Copyright (c) 2026 Tau Ceti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.AbsoluteValue.Equivalence
public import Mathlib.Data.Int.WithZero
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Weak approximation for discrete valuations

This file proves weak approximation for a finite family of pairwise inequivalent `ℤᵐ⁰`-valued
valuations. It first sends such a valuation through the strictly monotone embedding
`ℤᵐ⁰ → ℝ≥0 → ℝ`, obtaining a real absolute value with exactly the same comparisons. Mathlib's
abstract weak approximation theorem for real absolute values then supplies simultaneous open-ball
approximation. For normalized valuations, shifting each target by an element of prescribed value
gives the equality form with arbitrary integer orders.

The final statement is Stichtenoth, *Algebraic Function Fields and Codes*, second edition,
Theorem 1.3.1. The proof consumes Mathlib's `AbsoluteValue.denseRange_algebraMap_pi` rather than
rebuilding the Artin--Whaples approximation argument.

## Main results

* `Valuation.toRealAbsoluteValue` realizes a `ℤᵐ⁰`-valued valuation as a real absolute value.
* `Valuation.exists_forall_sub_lt` gives simultaneous open-ball approximation.
* `Valuation.exists_forall_sub_eq_exp` gives prescribed integer orders for normalized valuations.
-/

public section

open scoped NNReal WithZero

namespace Valuation

variable {K : Type*} [Field K]

private theorem withZeroMulIntToReal_strictMono :
    StrictMono (fun n : ℤᵐ⁰ ↦
      (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) n : ℝ)) := by
  intro m n hmn
  exact_mod_cast
    WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2) hmn

/-- A `ℤᵐ⁰`-valued valuation, viewed as a real absolute value through the base-two embedding of
its value group. This changes neither comparisons nor equivalence of valuations. -/
noncomputable def toRealAbsoluteValue (v : Valuation K ℤᵐ⁰) : AbsoluteValue K ℝ :=
  AbsoluteValue.mk
    (NNReal.toRealHom.toMonoidWithZeroHom.comp
      ((WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)).comp
        v.toMonoidWithZeroHom))
    (fun _ ↦ NNReal.coe_nonneg _)
    (fun x ↦ by simp)
    fun x y ↦ calc
      (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v (x + y)) : ℝ)
          ≤ (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0)
            (max (v x) (v y)) : ℝ) :=
        withZeroMulIntToReal_strictMono.monotone (v.map_add x y)
      _ = max
          (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v x) : ℝ)
          (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v y) : ℝ) :=
        withZeroMulIntToReal_strictMono.monotone.map_max
      _ ≤ (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v x) : ℝ) +
          (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v y) : ℝ) :=
        max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)

@[simp]
theorem toRealAbsoluteValue_apply (v : Valuation K ℤᵐ⁰) (x : K) :
    v.toRealAbsoluteValue x =
      (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v x) : ℝ) :=
  (rfl)

/-- Passing a discrete valuation to its real absolute value preserves and reflects inequalities. -/
theorem toRealAbsoluteValue_le_iff (v : Valuation K ℤᵐ⁰) {x y : K} :
    v.toRealAbsoluteValue x ≤ v.toRealAbsoluteValue y ↔ v x ≤ v y := by
  change (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v x) : ℝ) ≤
    (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v y) : ℝ) ↔ _
  exact withZeroMulIntToReal_strictMono.le_iff_le

/-- Passing discrete valuations to real absolute values preserves and reflects equivalence. -/
theorem toRealAbsoluteValue_isEquiv_iff (v w : Valuation K ℤᵐ⁰) :
    v.toRealAbsoluteValue.IsEquiv w.toRealAbsoluteValue ↔ v.IsEquiv w := by
  simp only [AbsoluteValue.IsEquiv, IsEquiv, toRealAbsoluteValue_le_iff]

/-- A discrete valuation is nontrivial exactly when its associated real absolute value is. -/
theorem toRealAbsoluteValue_isNontrivial_iff (v : Valuation K ℤᵐ⁰) :
    v.toRealAbsoluteValue.IsNontrivial ↔ v.IsNontrivial := by
  constructor
  · rintro ⟨x, hx0, hx1⟩
    refine ⟨x, v.ne_zero_iff.mpr hx0, fun hx ↦ hx1 ?_⟩
    rw [toRealAbsoluteValue_apply, hx, map_one, NNReal.coe_one]
  · rintro ⟨x, hx0, hx1⟩
    refine ⟨x, v.ne_zero_iff.mp hx0, fun hx ↦ hx1 ?_⟩
    apply withZeroMulIntToReal_strictMono.injective
    change (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (v x) : ℝ) =
      (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) 1 : ℝ)
    simpa [toRealAbsoluteValue_apply] using hx

/-- Weak approximation for finitely many nontrivial, pairwise inequivalent discrete valuations,
in open-ball form. -/
theorem exists_forall_sub_lt {ι : Type*} [Finite ι] (v : ι → Valuation K ℤᵐ⁰)
    (h_nontrivial : ∀ i, (v i).IsNontrivial)
    (h_inequiv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j))
    (a : ι → K) (ε : ι → ℤᵐ⁰) (hε : ∀ i, ε i ≠ 0) :
    ∃ x : K, ∀ i, v i (x - a i) < ε i := by
  classical
  let av : ι → AbsoluteValue K ℝ := fun i ↦ (v i).toRealAbsoluteValue
  have hav_nontrivial : ∀ i, (av i).IsNontrivial := fun i ↦
    (toRealAbsoluteValue_isNontrivial_iff (v i)).mpr (h_nontrivial i)
  have hav_inequiv : Pairwise fun i j ↦ ¬(av i).IsEquiv (av j) := by
    intro i j hij h
    exact h_inequiv hij ((toRealAbsoluteValue_isEquiv_iff (v i) (v j)).mp h)
  let target : (i : ι) → WithAbs (av i) := fun i ↦ WithAbs.toAbs (av i) (a i)
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      exact ⟨0, fun i ↦ isEmptyElim i⟩
  | inr hι =>
      let _ := Fintype.ofFinite ι
      let radius : ℝ := Finset.univ.inf' Finset.univ_nonempty fun i ↦
        (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (ε i) : ℝ)
      have hradius : 0 < radius := by
        apply (Finset.lt_inf'_iff _).mpr
        intro i _
        change (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) 0 : ℝ) <
          (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (ε i) : ℝ)
        exact withZeroMulIntToReal_strictMono (zero_lt_iff.mpr (hε i))
      obtain ⟨x, hx⟩ :=
        (AbsoluteValue.denseRange_algebraMap_pi hav_nontrivial hav_inequiv).exists_dist_lt
          target hradius
      refine ⟨x, fun i ↦ ?_⟩
      have hxi : dist (target i) ((algebraMap K ((i : ι) → WithAbs (av i)) x) i) < radius :=
        (dist_pi_lt_iff hradius).mp hx i
      have hiradius : radius ≤
          (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (ε i) : ℝ) :=
        Finset.inf'_le _ (Finset.mem_univ i)
      apply withZeroMulIntToReal_strictMono.lt_iff_lt.mp
      refine lt_of_lt_of_le ?_ hiradius
      rw [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub,
        Pi.algebraMap_apply, WithAbs.ofAbs_toAbs, WithAbs.algebraMap_right_apply,
        WithAbs.ofAbs_toAbs, Algebra.algebraMap_self_apply] at hxi
      rw [(av i).map_sub] at hxi
      change (v i).toRealAbsoluteValue (x - a i) < radius at hxi
      simpa [toRealAbsoluteValue_apply] using hxi

/-- Equality-form weak approximation for finitely many normalized discrete valuations. The error
at index `i` has the prescribed valuation `exp (-r i)`, hence the prescribed additive order
`r i`. -/
theorem exists_forall_sub_eq_exp {ι : Type*} [Finite ι] (v : ι → Valuation K ℤᵐ⁰)
    (h_surjective : ∀ i, Function.Surjective (v i))
    (h_inequiv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j))
    (a : ι → K) (r : ι → ℤ) :
    ∃ x : K, ∀ i, v i (x - a i) = WithZero.exp (-(r i)) := by
  choose p hp using fun i ↦ h_surjective i (WithZero.exp (-(r i)))
  obtain ⟨x, hx⟩ := exists_forall_sub_lt v
    (fun i ↦ by
      obtain ⟨u, hu⟩ := h_surjective i (WithZero.exp (-1))
      exact ⟨u, by simp [hu], by simp [hu]⟩)
    h_inequiv (fun i ↦ a i + p i)
    (fun i ↦ WithZero.exp (-(r i))) (fun _ ↦ WithZero.exp_ne_zero)
  refine ⟨x, fun i ↦ ?_⟩
  rw [show x - a i = (x - (a i + p i)) + p i by ring,
    (v i).map_add_eq_of_lt_right (hp i ▸ hx i), hp i]

end Valuation
