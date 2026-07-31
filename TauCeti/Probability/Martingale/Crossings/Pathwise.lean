/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Probability.Martingale.Crossings.TimeReversal

/-!
# Crossings: pathwise reversal lemmas

Pathwise reversal lemmas relating upcrossings of a process to upcrossings of its negated time
reversal. Downcrossings are not reintroduced here: Mathlib's `upcrossings (-b) (-a) (-X)` already
*is* the downcrossing count, so we phrase everything through Mathlib's `upcrossings` /
`upcrossingsBefore` of the negated process. No filtration / integrability content here — this is the
purely combinatorial / pathwise layer.

## Main results

- `upcrossingsBefore_congr` / `upcrossingsBefore_succ_congr`: `upcrossingsBefore` (at horizon `N`,
  resp. the free-boundary horizon `N + 1`) depends only on the path values on `[0, N]`.
- `upcrossingsBefore_le_upcrossingsBefore_neg_revProcess_succ`: the reversal bound — upcrossings of
  `X` on `[a, b]` before time `N` are bounded by upcrossings of the negated time reversal
  `-(revProcess X N)` on `[-b, -a]` before time `N + 1`.

Adapted from `cameronfreer/exchangeability` (`Probability/Martingale/Crossings/Pathwise.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory Set

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {𝔽 : ℕ → MeasurableSpace Ω}

/-- Helper: hitting respects pointwise equality on `[n, m]`. -/
private lemma hitting_congr {Ω β ι : Type*} [Preorder ι] [InfSet ι] {u v : ι → Ω → β}
    {s : Set β} {n m : ι} {ω : Ω}
    (h : ∀ k, n ≤ k → k ≤ m → u k ω = v k ω) :
    hittingBtwn u s n m ω = hittingBtwn v s n m ω := by
  simp only [hittingBtwn]
  by_cases hex : ∃ j ∈ Set.Icc n m, u j ω ∈ s
  · have hex' : ∃ j ∈ Set.Icc n m, v j ω ∈ s := by
      obtain ⟨j, hj, hj_mem⟩ := hex
      refine ⟨j, hj, ?_⟩
      rw [← h j hj.1 hj.2]
      exact hj_mem
    simp only [if_pos hex, if_pos hex']
    congr 1
    ext k
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro ⟨hk_Icc, hk_mem⟩
      refine ⟨hk_Icc, ?_⟩
      rw [← h k hk_Icc.1 hk_Icc.2]
      exact hk_mem
    · intro ⟨hk_Icc, hk_mem⟩
      refine ⟨hk_Icc, ?_⟩
      rw [h k hk_Icc.1 hk_Icc.2]
      exact hk_mem
  · have hex' : ¬∃ j ∈ Set.Icc n m, v j ω ∈ s := by
      intro ⟨j, hj, hj_mem⟩
      apply hex
      refine ⟨j, hj, ?_⟩
      rw [h j hj.1 hj.2]
      exact hj_mem
    simp only [if_neg hex, if_neg hex']

/-- Helper: `upperCrossingTime` respects pointwise equality on `[0, N]`. -/
private lemma upperCrossingTime_congr {Ω ι : Type*} [Preorder ι] [OrderBot ι] [InfSet ι]
    {a b : ℝ} {f g : ι → Ω → ℝ} {N : ι} {ω : Ω} (h : ∀ n ≤ N, f n ω = g n ω) :
    ∀ k, upperCrossingTime a b f N k ω = upperCrossingTime a b g N k ω := by
  intro k
  induction k with
  | zero =>
    simp [upperCrossingTime_zero]
  | succ n ih =>
    simp only [upperCrossingTime_succ_eq]
    have lct_eq : lowerCrossingTime a b f N n ω = lowerCrossingTime a b g N n ω := by
      simp only [lowerCrossingTime]
      rw [ih]
      apply hitting_congr
      intros k _ hk_ub
      exact h k hk_ub
    rw [lct_eq]
    apply hitting_congr
    intros k _ hk_ub
    exact h k hk_ub

/-- Helper: `upcrossingsBefore` is invariant under pointwise equality on `[0, N]`. -/
lemma upcrossingsBefore_congr {Ω ι : Type*} [Preorder ι] [OrderBot ι] [InfSet ι]
    {a b : ℝ} {f g : ι → Ω → ℝ} {N : ι} {ω : Ω} (h : ∀ n ≤ N, f n ω = g n ω) :
    upcrossingsBefore a b f N ω = upcrossingsBefore a b g N ω := by
  simp [upcrossingsBefore, upperCrossingTime_congr h]

/-- Free-boundary hitting congruence: at horizon `N + 1`, agreement of `u` and `v` on `[n, N]`
already forces equal hitting times. A hit at the free top index `N + 1` yields the horizon value
`N + 1`, exactly as the no-hit default does, so the value at `N + 1` never matters. -/
private lemma hittingBtwn_succ_congr {Ω β : Type*} {u v : ℕ → Ω → β} {s : Set β} {n N : ℕ}
    {ω : Ω} (h : ∀ k, n ≤ k → k ≤ N → u k ω = v k ω) :
    hittingBtwn u s n (N + 1) ω = hittingBtwn v s n (N + 1) ω := by
  by_cases hex : ∃ j ∈ Set.Icc n N, u j ω ∈ s
  · have hexv : ∃ j ∈ Set.Icc n N, v j ω ∈ s := by
      obtain ⟨j, hj, hjs⟩ := hex
      exact ⟨j, hj, h j hj.1 hj.2 ▸ hjs⟩
    rw [← hittingBtwn_eq_hittingBtwn_of_exists (Nat.le_succ N) hex,
        ← hittingBtwn_eq_hittingBtwn_of_exists (Nat.le_succ N) hexv]
    exact hitting_congr h
  · have hexv : ¬ ∃ j ∈ Set.Icc n N, v j ω ∈ s := by
      rintro ⟨j, hj, hjs⟩
      exact hex ⟨j, hj, (h j hj.1 hj.2).symm ▸ hjs⟩
    have key : ∀ {w : ℕ → Ω → β}, (¬ ∃ j ∈ Set.Icc n N, w j ω ∈ s) →
        hittingBtwn w s n (N + 1) ω = N + 1 := by
      intro w hw
      refine le_antisymm (hittingBtwn_le ω) ?_
      by_contra hlt
      rw [not_le, hittingBtwn_lt_iff (N + 1) le_rfl] at hlt
      obtain ⟨j, hj, hjs⟩ := hlt
      rw [Set.mem_Ico] at hj
      exact hw ⟨j, Set.mem_Icc.mpr ⟨hj.1, Nat.lt_succ_iff.mp hj.2⟩, hjs⟩
    rw [key hex, key hexv]

/-- Helper: `upperCrossingTime` at horizon `N + 1` respects pointwise equality on `[0, N]`. -/
private lemma upperCrossingTime_succ_congr {Ω : Type*} {a b : ℝ} {f g : ℕ → Ω → ℝ} {N : ℕ}
    {ω : Ω} (h : ∀ n ≤ N, f n ω = g n ω) :
    ∀ k, upperCrossingTime a b f (N + 1) k ω = upperCrossingTime a b g (N + 1) k ω := by
  intro k
  induction k with
  | zero => simp [upperCrossingTime_zero]
  | succ n ih =>
    simp only [upperCrossingTime_succ_eq]
    have lct_eq : lowerCrossingTime a b f (N + 1) n ω = lowerCrossingTime a b g (N + 1) n ω := by
      simp only [lowerCrossingTime]
      rw [ih]
      exact hittingBtwn_succ_congr fun k _ hk_ub => h k hk_ub
    rw [lct_eq]
    exact hittingBtwn_succ_congr fun k _ hk_ub => h k hk_ub

/-- Helper: `upcrossingsBefore` at horizon `N + 1` is invariant under pointwise equality on
`[0, N]`. The extra index `N + 1` is a "free boundary" that never affects the crossing count. -/
lemma upcrossingsBefore_succ_congr {Ω : Type*} {a b : ℝ} {f g : ℕ → Ω → ℝ} {N : ℕ} {ω : Ω}
    (h : ∀ n ≤ N, f n ω = g n ω) :
    upcrossingsBefore a b f (N + 1) ω = upcrossingsBefore a b g (N + 1) ω := by
  simp [upcrossingsBefore, upperCrossingTime_succ_congr h]

/-- Reversed-crossing bound: the upcrossings of `X` on `[a, b]` before time `N` are bounded by the
upcrossings of the negated time-reversed process `-(revProcess X N)` on `[-b, -a]` before time
`N + 1`. The extra `N + 1` horizon on the reversed side is what makes crossings completing exactly
at time `N` count. -/
-- Via the bijection `(τ, σ) ↦ (N - σ, N - τ)` mapping `X` upcrossings to reversed-process
-- upcrossings (packaged in `upperCrossingTime_neg_revProcess_le`): when `τ = 0` the reversed
-- crossing completes at time `N`, which the `N + 1` horizon includes since `N < N + 1`.
lemma upcrossingsBefore_le_upcrossingsBefore_neg_revProcess_succ
    {Ω : Type*} (X : ℕ → Ω → ℝ) (a b : ℝ) (hab : a < b) (N : ℕ) (ω : Ω) :
    upcrossingsBefore a b X N ω
      ≤ upcrossingsBefore (-b) (-a) (-(revProcess X N)) (N + 1) ω := by
  classical
  simp only [upcrossingsBefore]
  by_cases hN : N = 0
  · simp [hN]
  by_cases hemp : {n | upperCrossingTime a b X N n ω < N}.Nonempty
  · -- Mathlib's boundedness of the completed-crossing index set on the reversed side.
    have hneg : -b < -a := by linarith
    have hbdd : BddAbove
        {n | upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) n ω < N + 1} :=
      upperCrossingTime_lt_bddAbove hneg
    have hsub : {n | upperCrossingTime a b X N n ω < N} ⊆
        {n | upperCrossingTime (-b) (-a) (-(revProcess X N)) (N + 1) n ω < N + 1} := by
      intro n hn
      simp only [Set.mem_ofPred_eq] at hn ⊢
      -- With horizon `N + 1` the bijection works: crossings completing at time `N` are now counted
      -- since `N < N + 1`.
      cases n with
      | zero =>
        simp only [upperCrossingTime_zero]
        exact Nat.zero_lt_succ N
      | succ k =>
        -- `hn` says `X` has `k + 1` complete crossings before time `N`; the bijection
        -- `(τ, σ) ↦ (N - σ, N - τ)` maps these to reversed crossings completing by time `N`.
        have h_bound : upperCrossingTime (-b) (-a)
            (-(revProcess X N)) (N + 1) (k + 1) ω ≤ N :=
          upperCrossingTime_neg_revProcess_le X a b hab N (k + 1) ω hn
        exact Nat.lt_succ_of_le h_bound
    exact csSup_le_csSup hbdd hemp hsub
  · rw [Set.not_nonempty_iff_eq_empty] at hemp
    simp [hemp]

end MeasureTheory
