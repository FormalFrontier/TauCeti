/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Probability.Martingale.Upcrossing

/-!
# Time-reversal crossing bound

Reverse-martingale infrastructure bounding the completion time of upcrossings in a time-reversed,
negated process. This is a combinatorial ingredient of the reverse-martingale upcrossing argument.

## Main definitions

- `revProcess`: time reversal of a stochastic process up to a horizon `N`.

## Main results

- `MeasureTheory.upperCrossingTime_neg_revProcess_le`: for a process `X` with `k`
  upcrossings `[a→b]` completing before time `N`, the time-reversed negated process
  `-(revProcess X N)` has its `k`-th upcrossing `[-b→-a]` completing at time `≤ N`.

Adapted from `cameronfreer/exchangeability` (`Probability/TimeReversalCrossing.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace MeasureTheory

/-- Time reversal of a stochastic process up to time `N`, using Mathlib's horizon reversal
`Polynomial.revAt`. For `n ≤ N` this is `X (N - n)`; see `revProcess_apply_of_le`. -/
def revProcess {Ω α : Type*} (X : ℕ → Ω → α) (N : ℕ) : ℕ → Ω → α :=
  fun n ω => X (Polynomial.revAt N n) ω

/-- Defining equation for `revProcess` (whose body is deliberately not `@[expose]`d). -/
@[simp]
lemma revProcess_apply {Ω α : Type*} (X : ℕ → Ω → α) (N n : ℕ) (ω : Ω) :
    revProcess X N n ω = X (Polynomial.revAt N n) ω := by rfl

/-- Below the horizon, `Polynomial.revAt N` is genuine subtraction, so `revProcess` reverses. -/
lemma revProcess_apply_of_le {Ω α : Type*} (X : ℕ → Ω → α) {N n : ℕ} (h : n ≤ N) (ω : Ω) :
    revProcess X N n ω = X (N - n) ω := by simp [revProcess, Polynomial.revAt_le h]

/-- Inductive step of `upperCrossingTime_neg_revProcess_le_strong`.

Fix a crossing index `i` and a count `m'`, and assume:
* `hab : a < b`;
* `hσ_lt_N`: `X`'s `(i + 1)`-th upper crossing completes strictly before `N`;
* `ih'`: the reversed process satisfies the bound at count `m'` (endpoint index `i + 1`).

Then the bound holds for `m' + 1`, with reflected endpoint `N - lowerCrossingTime a b X N i ω`. -/
private lemma upperCrossingTime_neg_revProcess_succ_le
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) (N m' i : ℕ) (ω : Ω)
    (hσ_lt_N : upperCrossingTime a b X N (i + 1) ω < N)
    (ih' : upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) m' ω
      ≤ N - lowerCrossingTime a b X N (i + 1) ω) :
    upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) (m' + 1) ω
      ≤ N - lowerCrossingTime a b X N i ω := by
  set Y := -(revProcess X N) with hY_def
  -- `X` reaches `≥ b` at its `(i+1)`-th upper crossing, `≤ a` at its `i`-th lower crossing, and the
  -- latter precedes the former. (Stated on explicit terms, then folded to `σ`, `τ` by `set`.)
  have hτ_lt_σ : lowerCrossingTime a b X N i ω < upperCrossingTime a b X N (i + 1) ω :=
    lowerCrossingTime_lt_upperCrossingTime hab (Nat.ne_of_lt hσ_lt_N)
  -- The `i`-th lower crossing precedes the `(i+1)`-th upper, so it too completes before `N`.
  have hτ_lt_N : lowerCrossingTime a b X N i ω < N := lt_trans hτ_lt_σ hσ_lt_N
  have hX_σ_ge_b : b ≤ X (upperCrossingTime a b X N (i + 1) ω) ω :=
    stoppedValue_upperCrossingTime (Nat.ne_of_lt hσ_lt_N)
  have hX_τ_le_a : X (lowerCrossingTime a b X N i ω) ω ≤ a :=
    stoppedValue_lowerCrossingTime (Nat.ne_of_lt hτ_lt_N)
  have h_lct_ge : upperCrossingTime a b X N (i + 1) ω ≤ lowerCrossingTime a b X N (i + 1) ω :=
    upperCrossingTime_le_lowerCrossingTime
  set σ := upperCrossingTime a b X N (i + 1) ω with hσ_def
  set τ := lowerCrossingTime a b X N i ω with hτ_def
  -- The reflected process `Y` mirrors these levels at the reflected times `N - σ` and `N - τ`.
  have hY_Nσ_le_negb : Y (N - σ) ω ≤ -b := by
    have hrev : revProcess X N (N - σ) ω = X σ ω := by
      rw [revProcess_apply_of_le X (Nat.sub_le N σ) ω, Nat.sub_sub_self (Nat.le_of_lt hσ_lt_N)]
    simp only [hY_def, Pi.neg_apply, hrev]; linarith
  have hY_Nτ_ge_nega : -a ≤ Y (N - τ) ω := by
    have hrev : revProcess X N (N - τ) ω = X τ ω := by
      rw [revProcess_apply_of_le X (Nat.sub_le N τ) ω, Nat.sub_sub_self (Nat.le_of_lt hτ_lt_N)]
    simp only [hY_def, Pi.neg_apply, hrev]; linarith
  -- Advance `Y`'s crossing count: the induction hypothesis bounds `Y`'s `m'`-th upper crossing by
  -- `N - σ`, hence its `m'`-th lower crossing too; the `(m'+1)`-th upper crossing then lands by
  -- `N - τ`, the reflection of `X`'s crossing start.
  have h_uct_le_Nσ : upperCrossingTime (-b) (-a) Y (N + 1) m' ω ≤ N - σ :=
    le_trans ih' (Nat.sub_le_sub_left h_lct_ge N)
  have h_lctY_le_Nσ : lowerCrossingTime (-b) (-a) Y (N + 1) m' ω ≤ N - σ := by
    simpa only [lowerCrossingTime] using
      hittingBtwn_le_of_mem h_uct_le_Nσ (Nat.le_succ_of_le (Nat.sub_le N σ)) hY_Nσ_le_negb
  have h_lctY_le_Nτ : lowerCrossingTime (-b) (-a) Y (N + 1) m' ω ≤ N - τ :=
    Nat.le_of_lt (lt_of_le_of_lt h_lctY_le_Nσ (Nat.sub_lt_sub_left hτ_lt_N hτ_lt_σ))
  calc upperCrossingTime (-b) (-a) Y (N + 1) (m' + 1) ω
      = hittingBtwn Y (Set.Ici (-a)) (lowerCrossingTime (-b) (-a) Y (N + 1) m' ω) (N + 1) ω :=
        upperCrossingTime_succ_eq ω
    _ ≤ N - τ :=
        hittingBtwn_le_of_mem h_lctY_le_Nτ (Nat.le_succ_of_le (Nat.sub_le N τ)) hY_Nτ_ge_nega

/-- Strong version tracking the bijection explicitly.

For `m ≤ k` with `X`'s `k`-th crossing completing before `N`:
  `upperCrossingTime Y (N + 1) m ≤ N - lowerCrossingTime X (k - m)`.

This captures that `Y`'s `m`-th crossing corresponds to `X`'s `(k - m + 1)`-th crossing (reversed
order), with `Y`'s crossing ending at time `N - τ` where `τ` is the start of `X`'s crossing. -/
private lemma upperCrossingTime_neg_revProcess_le_strong
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) (N k m : ℕ) (ω : Ω)
    (hm : m ≤ k)
    (h_k : upperCrossingTime a b X N k ω < N) :
    upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) m ω
      ≤ N - lowerCrossingTime a b X N (k - m) ω := by
  -- All of `X`'s upper crossings up to the `k`-th complete before `N`, and so do the lower ones.
  have h_j : ∀ j ≤ k, upperCrossingTime a b X N j ω < N := fun j hj =>
    lt_of_le_of_lt (upperCrossingTime_mono hj) h_k
  induction m with
  | zero => simp only [upperCrossingTime_zero, Nat.sub_zero]; exact Nat.zero_le _
  | succ m' ih =>
    -- `Y`'s `(m'+1)`-th crossing reflects `X`'s `(k-m')`-th; set `i = k-(m'+1)`, so `k-m' = i+1`.
    have hik : k - m' = k - (m' + 1) + 1 := by omega
    refine upperCrossingTime_neg_revProcess_succ_le X a b hab N m' (k - (m' + 1)) ω ?_ ?_
    · rw [← hik]; exact h_j (k - m') (Nat.sub_le k m')
    · rw [← hik]; exact ih (Nat.le_of_lt (Nat.lt_of_succ_le hm))

/-- **Time-reversal crossing bound.**

For a process `X` with `k` upcrossings `[a→b]` completing before time `N`, the time-reversed
negated process `-(revProcess X N)` has its `k`-th upcrossing `[-b→-a]` completing at
time `≤ N`. -/
lemma upperCrossingTime_neg_revProcess_le
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) (N k : ℕ) (ω : Ω)
    (h_k : upperCrossingTime a b X N k ω < N) :
    upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) k ω ≤ N := by
  -- The `strong` version bounds this by `N - lowerCrossingTime …` via the bijection
  -- `(τ, σ) ↦ (N - σ, N - τ)`; discard the subtraction with `Nat.sub_le`.
  have h := upperCrossingTime_neg_revProcess_le_strong X a b hab N k k ω le_rfl h_k
  exact le_trans (by simpa using h) (Nat.sub_le N _)

end MeasureTheory
