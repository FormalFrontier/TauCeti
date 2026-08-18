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

The results below are the finite-family approximation engine for abstract `ℤᵐ⁰`-valued
valuations: they mention neither function fields nor places. Weak approximation for places of an
algebraic function field — Stichtenoth, *Algebraic Function Fields and Codes*, second edition,
Theorem 1.3.1 — follows from `Valuation.exists_forall_sub_eq_exp` once the place API supplies the
normalized valuation of a place and the inequivalence of distinct normalized places. The proof
consumes Mathlib's `AbsoluteValue.denseRange_algebraMap_pi` rather than rebuilding the
Artin--Whaples approximation argument.

## Main results

* `Valuation.toRealAbsoluteValue` realizes a `ℤᵐ⁰`-valued valuation as a real absolute value.
* `Valuation.exists_forall_sub_lt` gives simultaneous open-ball approximation.
* `Valuation.exists_forall_sub_eq_exp` gives prescribed integer orders for normalized valuations.
-/

public section

open scoped NNReal WithZero

namespace Valuation

private theorem withZeroMulIntToReal_strictMono :
    StrictMono (fun n : ℤᵐ⁰ ↦
      (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) n : ℝ)) := by
  intro m n hmn
  exact_mod_cast
    WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : ℝ≥0) < 2) hmn

section DivisionRing

variable {K : Type*} [DivisionRing K]

/-- A `ℤᵐ⁰`-valued valuation, viewed as a real absolute value through the base-two embedding of
its value group. This changes neither comparisons nor equivalence of valuations.

A division ring is needed already here: an `AbsoluteValue` vanishes only at `0`, whereas a
valuation on a general ring may have nontrivial support. -/
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
  -- The parentheses keep the module system's `rfl`-theorem check from demanding that
  -- `toRealAbsoluteValue` be `@[expose]`d; the two sides are definitionally equal.
  (rfl)

/-- Passing a discrete valuation to its real absolute value preserves and reflects inequalities. -/
theorem toRealAbsoluteValue_le_iff (v : Valuation K ℤᵐ⁰) {x y : K} :
    v.toRealAbsoluteValue x ≤ v.toRealAbsoluteValue y ↔ v x ≤ v y := by
  simp only [toRealAbsoluteValue_apply]
  exact withZeroMulIntToReal_strictMono.le_iff_le

/-- Passing discrete valuations to real absolute values preserves and reflects equivalence. -/
@[simp]
theorem toRealAbsoluteValue_isEquiv_iff (v w : Valuation K ℤᵐ⁰) :
    v.toRealAbsoluteValue.IsEquiv w.toRealAbsoluteValue ↔ v.IsEquiv w := by
  simp only [AbsoluteValue.IsEquiv, IsEquiv, toRealAbsoluteValue_le_iff]

/-- A discrete valuation is nontrivial exactly when its associated real absolute value is. -/
@[simp]
theorem toRealAbsoluteValue_isNontrivial_iff (v : Valuation K ℤᵐ⁰) :
    v.toRealAbsoluteValue.IsNontrivial ↔ v.IsNontrivial := by
  constructor
  · rintro ⟨x, hx0, hx1⟩
    refine ⟨x, v.ne_zero_iff.mpr hx0, fun hx ↦ hx1 ?_⟩
    rw [toRealAbsoluteValue_apply, hx, map_one, NNReal.coe_one]
  · rintro ⟨x, hx0, hx1⟩
    refine ⟨x, v.ne_zero_iff.mp hx0, fun hx ↦ hx1 ?_⟩
    rw [toRealAbsoluteValue_apply] at hx
    refine withZeroMulIntToReal_strictMono.injective ?_
    simpa using hx

end DivisionRing

section Field

variable {K : Type*} [Field K]

/-- In the product `(j : ι) → WithAbs (av j)`, the distance from the point `y` of the `i`-th
factor to the `i`-th component of the diagonal image of `x` is `av i (x - y)`. -/
private theorem dist_toAbs_algebraMap_pi {ι : Type*} (av : ι → AbsoluteValue K ℝ) (i : ι)
    (x y : K) :
    dist (WithAbs.toAbs (av i) y) (algebraMap K ((j : ι) → WithAbs (av j)) x i) =
      av i (x - y) := by
  rw [dist_eq_norm, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub, Pi.algebraMap_apply,
    WithAbs.ofAbs_toAbs, WithAbs.algebraMap_right_apply, WithAbs.ofAbs_toAbs,
    Algebra.algebraMap_self_apply, (av i).map_sub]

/-- Weak approximation for finitely many nontrivial, pairwise inequivalent discrete valuations,
in open-ball form. -/
theorem exists_forall_sub_lt {ι : Type*} [Finite ι] (v : ι → Valuation K ℤᵐ⁰)
    (h_nontrivial : ∀ i, (v i).IsNontrivial)
    (h_inequiv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j))
    (a : ι → K) (ε : ι → ℤᵐ⁰) (hε : ∀ i, ε i ≠ 0) :
    ∃ x : K, ∀ i, v i (x - a i) < ε i := by
  classical
  let av : ι → AbsoluteValue K ℝ := fun i ↦ (v i).toRealAbsoluteValue
  have hav : ∀ i, av i = (v i).toRealAbsoluteValue := fun _ ↦ rfl
  have hav_nontrivial : ∀ i, (av i).IsNontrivial := fun i ↦
    (toRealAbsoluteValue_isNontrivial_iff (v i)).mpr (h_nontrivial i)
  have hav_inequiv : Pairwise fun i j ↦ ¬(av i).IsEquiv (av j) := by
    intro i j hij h
    exact h_inequiv hij ((toRealAbsoluteValue_isEquiv_iff (v i) (v j)).mp h)
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      exact ⟨0, fun i ↦ isEmptyElim i⟩
  | inr hι =>
      let _ := Fintype.ofFinite ι
      let radius : ℝ := Finset.univ.inf' Finset.univ_nonempty fun i ↦
        (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (ε i) : ℝ)
      have hradius : 0 < radius := by
        refine (Finset.lt_inf'_iff _).mpr fun i _ ↦ ?_
        exact_mod_cast WithZeroMulInt.toNNReal_pos (by norm_num : (2 : ℝ≥0) ≠ 0) (hε i)
      obtain ⟨x, hx⟩ :=
        (AbsoluteValue.denseRange_algebraMap_pi hav_nontrivial hav_inequiv).exists_dist_lt
          (fun i ↦ WithAbs.toAbs (av i) (a i)) hradius
      refine ⟨x, fun i ↦ ?_⟩
      have hxi : dist (WithAbs.toAbs (av i) (a i))
          ((algebraMap K ((j : ι) → WithAbs (av j)) x) i) < radius :=
        (dist_pi_lt_iff hradius).mp hx i
      rw [dist_toAbs_algebraMap_pi, hav i, toRealAbsoluteValue_apply] at hxi
      have hiradius : radius ≤
          (WithZeroMulInt.toNNReal (by norm_num : (2 : ℝ≥0) ≠ 0) (ε i) : ℝ) :=
        Finset.inf'_le _ (Finset.mem_univ i)
      exact withZeroMulIntToReal_strictMono.lt_iff_lt.mp (hxi.trans_le hiradius)

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
  have hshift : x - a i = (x - (a i + p i)) + p i := by ring
  have hlt : v i (x - (a i + p i)) < v i (p i) := hp i ▸ hx i
  rw [hshift, (v i).map_add_eq_of_lt_right hlt, hp i]

end Field

end Valuation
