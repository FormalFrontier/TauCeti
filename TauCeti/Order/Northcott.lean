/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Northcott

/-!
# Finite real-cutoff carriers for Northcott functions

This file packages the finite carrier selected by a real cutoff for a natural-valued Northcott
function, together with generic summatory functions over that carrier. For a nonnegative cutoff,
the carrier agrees with the one selected by its natural floor.
-/

public section

namespace TauCeti

variable {ι : Type*} (N : ι → ℕ) [Northcott N]

/-- Only finitely many indices have `N`-value at most a fixed real number, because the `N`-value
is a natural number and `N` is Northcott. -/
theorem finite_setOf_natCast_le (x : ℝ) : {i : ι | (N i : ℝ) ≤ x}.Finite :=
  (Northcott.finite_le (h := N) ⌊x⌋₊).subset fun _ hi ↦ Nat.le_floor hi

/-- The finite set of indices whose `N`-value is at most the real cutoff `x`. The cutoff is
inclusive: an index with `N i = x` belongs to `normLE N x`. -/
public noncomputable def normLE (x : ℝ) : Finset ι :=
  (finite_setOf_natCast_le N x).toFinset

/-- An index belongs to `normLE N x` exactly when its `N`-value is at most the inclusive
real cutoff `x`. -/
@[simp, grind =]
theorem mem_normLE {i : ι} {x : ℝ} : i ∈ normLE N x ↔ (N i : ℝ) ≤ x := by
  simp [normLE]

@[simp]
theorem coe_normLE (x : ℝ) : (normLE N x : Set ι) = {i : ι | (N i : ℝ) ≤ x} := by
  ext i
  simp

/-- The cardinality of the cutoff subtype agrees with that of its finite carrier. -/
theorem Nat.card_coe_normLE (x : ℝ) :
    Nat.card {i : ι // (N i : ℝ) ≤ x} = (normLE N x).card := by
  rw [← Set.coe_ofPred]
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (finite_setOf_natCast_le N x)]
  rfl

/-- Increasing the real cutoff can only enlarge the finite carrier. -/
theorem normLE_mono : Monotone (normLE N) := fun _ _ hxy _ hi ↦
  mem_normLE N |>.mpr <| (mem_normLE N |>.mp hi).trans hxy

/-- Membership in a carrier with natural cutoff is the plain inequality of natural numbers. -/
theorem mem_normLE_natCast {i : ι} {n : ℕ} : i ∈ normLE N (n : ℝ) ↔ N i ≤ n := by
  simp

/-- A nonnegative real cutoff and its floor select the same indices; this is the promised
conversion between the real and the natural cutoff conventions. Nonnegativity is needed: for
`x < 0` the floor is `0`, which still admits an index of `N`-value `0`. -/
theorem normLE_eq_normLE_natFloor {x : ℝ} (hx : 0 ≤ x) :
    normLE N x = normLE N (⌊x⌋₊ : ℝ) := by
  ext i
  rw [mem_normLE, mem_normLE_natCast]
  exact ⟨Nat.le_floor, fun hi ↦ (Nat.le_floor_iff hx).mp hi⟩

/-- Below a uniform lower bound for the `N`-values the carrier is empty. -/
theorem normLE_eq_empty_of_lt {b x : ℝ} (hb : ∀ i, b ≤ (N i : ℝ)) (hx : x < b) :
    normLE N x = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun i hi ↦ ?_
  exact absurd ((hb i).trans (mem_normLE N |>.mp hi)) (not_le.mpr hx)

/-! ### Generic summatory functions -/

/-- The inclusive summatory function of a weight `w`: the sum of `w` over all indices of
`N`-value at most `x`. -/
public noncomputable def summatory {M : Type*} [AddCommMonoid M]
    (w : ι → M) (x : ℝ) : M :=
  ∑ i ∈ normLE N x, w i

/-- Evaluating `summatory N w` at `x` gives the finite sum of `w` over `normLE N x`. -/
theorem summatory_apply {M : Type*} [AddCommMonoid M] (w : ι → M) (x : ℝ) :
    summatory N w x = ∑ i ∈ normLE N x, w i := by
  rw [summatory]

@[simp]
theorem summatory_zero {M : Type*} [AddCommMonoid M] (x : ℝ) :
    summatory N (0 : ι → M) x = 0 := by
  simp [summatory]

/-- Summation distributes over pointwise addition of weights. -/
theorem summatory_add {M : Type*} [AddCommMonoid M] (w₁ w₂ : ι → M) (x : ℝ) :
    summatory N (w₁ + w₂) x = summatory N w₁ x + summatory N w₂ x := by
  simp [summatory, Finset.sum_add_distrib]

/-- Summation distributes over pointwise subtraction of weights. -/
theorem summatory_sub {M : Type*} [AddCommGroup M] (w₁ w₂ : ι → M) (x : ℝ) :
    summatory N (w₁ - w₂) x = summatory N w₁ x - summatory N w₂ x := by
  simp [summatory, Finset.sum_sub_distrib]

/-- A real scalar can be pulled out of a summatory function. -/
theorem summatory_const_mul (c : ℝ) (w : ι → ℝ) (x : ℝ) :
    summatory N (fun i ↦ c * w i) x = c * summatory N w x := by
  simp [summatory, Finset.mul_sum]

/-- Below a uniform lower bound for the `N`-values every summatory function vanishes. -/
theorem summatory_eq_zero_of_lt {M : Type*} [AddCommMonoid M] {b x : ℝ}
    (hb : ∀ i, b ≤ (N i : ℝ)) (hx : x < b) (w : ι → M) : summatory N w x = 0 := by
  simp [summatory, normLE_eq_empty_of_lt N hb hx]

/-- For a nonnegative cutoff, a summatory function has the same value at the cutoff and at its
natural floor. -/
theorem summatory_eq_summatory_natFloor {M : Type*} [AddCommMonoid M] (w : ι → M) {x : ℝ}
    (hx : 0 ≤ x) : summatory N w x = summatory N w (⌊x⌋₊ : ℝ) := by
  rw [summatory, summatory, normLE_eq_normLE_natFloor N hx]

/-- The summatory function of a pointwise nonnegative real weight is nonnegative. -/
theorem summatory_nonneg {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (x : ℝ) : 0 ≤ summatory N w x :=
  Finset.sum_nonneg fun i _ ↦ hw i

/-- Pointwise comparison of real weights gives the same comparison of their summatory functions. -/
theorem summatory_le_summatory {w₁ w₂ : ι → ℝ} (h : ∀ i, w₁ i ≤ w₂ i) (x : ℝ) :
    summatory N w₁ x ≤ summatory N w₂ x :=
  Finset.sum_le_sum fun i _ ↦ h i

/-- A summatory function with nonnegative real weight is monotone in the cutoff. -/
theorem summatory_mono {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) : Monotone (summatory N w) :=
  fun _ _ hxy ↦ Finset.sum_le_sum_of_subset_of_nonneg (normLE_mono N hxy) fun i _ _ ↦ hw i

/-- Changing a weight on a finite set of indices changes the summatory function, for all large
cutoffs, by the constant total discrepancy over that set. -/
theorem eventually_summatory_sub_eq {M : Type*} [AddCommGroup M] (w₁ w₂ : ι → M) (u : Finset ι)
    (h : ∀ i ∉ u, w₁ i = w₂ i) :
    ∀ᶠ x in Filter.atTop,
      summatory N w₁ x - summatory N w₂ x = ∑ i ∈ u, (w₁ i - w₂ i) := by
  filter_upwards [Filter.eventually_ge_atTop ((u.sup N : ℕ) : ℝ)] with x hx
  have hsub : u ⊆ normLE N x := fun i hi ↦
    mem_normLE N |>.mpr <| le_trans (by exact_mod_cast Finset.le_sup (f := N) hi) hx
  rw [summatory, summatory, ← Finset.sum_sub_distrib]
  exact (Finset.sum_subset hsub fun i _ hi ↦ by rw [h i hi, sub_self]).symm

/-- A weight vanishing outside a finite set has eventually constant summatory function, equal to
its total sum. -/
theorem eventually_summatory_eq_sum {M : Type*} [AddCommMonoid M] (w : ι → M) (u : Finset ι)
    (h : ∀ i ∉ u, w i = 0) : ∀ᶠ x in Filter.atTop, summatory N w x = ∑ i ∈ u, w i := by
  filter_upwards [Filter.eventually_ge_atTop ((u.sup N : ℕ) : ℝ)] with x hx
  have hsub : u ⊆ normLE N x := fun i hi ↦
    mem_normLE N |>.mpr <| le_trans (by exact_mod_cast Finset.le_sup (f := N) hi) hx
  exact (Finset.sum_subset hsub fun i _ hi ↦ h i hi).symm

/-- If two sets have finite symmetric difference, their indicator-weighted summatory functions
have eventually constant difference. -/
theorem eventually_summatory_indicator_sub_eq (w : ι → ℝ) {S T : Set ι}
    (hST : (symmDiff S T).Finite) :
    ∀ᶠ x in Filter.atTop, summatory N (S.indicator w) x - summatory N (T.indicator w) x
      = ∑ i ∈ hST.toFinset, (S.indicator w i - T.indicator w i) := by
  refine eventually_summatory_sub_eq N _ _ hST.toFinset fun i hi ↦ ?_
  rw [Set.Finite.mem_toFinset, Set.mem_symmDiff] at hi
  by_cases hS : i ∈ S
  · rw [Set.indicator_of_mem hS, Set.indicator_of_mem (by tauto)]
  · rw [Set.indicator_of_notMem hS, Set.indicator_of_notMem (by tauto)]

end TauCeti
