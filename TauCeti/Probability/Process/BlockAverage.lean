/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Algebra.BigOperators.Fin

/-!
# Block averages of a real-valued process

The empirical mean of a process over a finite selection of coordinates, with its elementary
algebra. Nothing here involves a measure: `blockAverage X k` is a function of `ω`, and the three
lemmas below are the pointwise formula, the scaled-sum normal form, and the value on a constant
block. `average_sub_sq_eq_sum_sum` records the one further piece of average algebra used
downstream: the square of a deviation from an average, expanded as a double sum.
`birkhoffAverage_eq_prefixAverage` identifies a Birkhoff average of an arbitrary self-map with a
prefix average of the iterated observable, which is how Mathlib's mean-ergodic theory reaches this
API; it is stated for an arbitrary self-map because no dynamical content enters — both sides are
the same normalised sum.

It also carries the standard selections, all measure-free. `prefixAverage X n` averages the first
`n` coordinates and `followingAverage X n` the `n` after them, with their pointwise formulas.

`fixedStart r` is the same fixed-start window in *moving-selection* form — a family
`∀ n, Fin (n + 1) → ℕ` rather than a single block — which is the shape the `L²` convergence
theorems quantify over. It belongs here because it is a generic block selection with no disjointness
content; the disjoint windows those theorems also accept are `disjointWindow` in
`Process/DisjointWindow.lean`. `fixedStart_injective` gives injectivity at each length and
`fixedStart_eventually_injective` the eventual form the limit theorems take.

Measure-theoretic facts about all three — square-integrability, conditional expectations, variances
and covariances under contractability — live with the `L²` averaging library in
`Exchangeability/L2/BlockAverages.lean` and `Exchangeability/L2/LongTailAverages.lean`, which import
this module. Keeping the definitions here means a route that only needs the algebra does not import
the `L²` machinery to get them: the Koopman route needs `prefixAverage` to state its Birkhoff
bridge, and has no `L²` content of its own.
-/

public section

noncomputable section

open Filter Finset
open scoped BigOperators

namespace TauCeti

namespace Probability

variable {Ω : Type*} {X : ℕ → Ω → ℝ}

/-- The **block average** of a real-valued process `X` over a finite selection `k : Fin n → ℕ`:
the empirical mean `n⁻¹ • ∑ i, X (k i)` of the block `(X (k i))ᵢ`. -/
def blockAverage (X : ℕ → Ω → ℝ) {n : ℕ} (k : Fin n → ℕ) : Ω → ℝ :=
  𝔼 i, X (k i)

/-- **The pointwise formula for a block average**: at each `ω` it is the normalised finite sum
`n⁻¹ * ∑ i, X (k i) ω`. -/
@[simp]
theorem blockAverage_apply {n : ℕ} (k : Fin n → ℕ) (ω : Ω) :
    blockAverage X k ω = (n : ℝ)⁻¹ * ∑ i, X (k i) ω := by
  rw [blockAverage, Finset.expect_apply, Fintype.expect_eq_sum_div_card]
  simp [div_eq_inv_mul]

/-- A block average as a real-scaled finite sum. -/
theorem blockAverage_eq_sum {n : ℕ} (k : Fin n → ℕ) :
    blockAverage X k = (n : ℝ)⁻¹ • ∑ i, X (k i) := by
  ext ω
  simp

/-- **A block average of a constant block.** If every coordinate of a nonempty block takes the
value `c` at `ω`, then so does the block average: the normalisation `n⁻¹` cancels the `n` terms. -/
theorem blockAverage_apply_of_forall_eq {n : ℕ} (hn : 0 < n) {k : Fin n → ℕ} {ω : Ω} {c : ℝ}
    (h : ∀ i, X (k i) ω = c) : blockAverage X k ω = c := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rw [blockAverage, Finset.expect_apply, Finset.expect_congr rfl fun i _ => h i,
    Fintype.expect_const]

/-- The average of the first `n` coordinates of a real-valued process. -/
def prefixAverage (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  blockAverage X fun i : Fin n => i

/-- The average of the `n` coordinates immediately following the first `n` coordinates. -/
def followingAverage (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  blockAverage X fun i : Fin n => n + i

/-- A prefix average is the block average over the selection `i ↦ i`. -/
theorem prefixAverage_def (X : ℕ → Ω → ℝ) (n : ℕ) :
    prefixAverage X n = blockAverage X fun i : Fin n => (i : ℕ) := (rfl)

/-- A following-block average is the block average over the selection `i ↦ n + i`. -/
theorem followingAverage_def (X : ℕ → Ω → ℝ) (n : ℕ) :
    followingAverage X n = blockAverage X fun i : Fin n => n + (i : ℕ) := (rfl)

/-- **The pointwise formula for a prefix average.** -/
@[simp]
theorem prefixAverage_apply (n : ℕ) (ω : Ω) :
    prefixAverage X n ω = (n : ℝ)⁻¹ * ∑ i : Fin n, X i ω := by
  simp [prefixAverage, blockAverage_apply]

/-- **The pointwise formula for a following-block average.** -/
@[simp]
theorem followingAverage_apply (n : ℕ) (ω : Ω) :
    followingAverage X n ω = (n : ℝ)⁻¹ * ∑ i : Fin n, X (n + i) ω := by
  simp [followingAverage, blockAverage_apply]

/-- **A product of block averages is an average of products.** Purely algebraic: the product of
sums distributes by `Fintype.prod_sum`, and the normalisations multiply. Disjointness of the
selections plays no role here — it matters only for what the individual terms mean. -/
theorem prod_blockAverage_eq_expect {m N : ℕ} (Y : Fin m → ℕ → Ω → ℝ) (k : Fin m → Fin N → ℕ)
    (ω : Ω) :
    (∏ i : Fin m, blockAverage (Y i) (k i) ω)
      = 𝔼 js : Fin m → Fin N, ∏ i : Fin m, Y i (k i (js i)) ω := by
  classical
  have hL : (∏ i : Fin m, blockAverage (Y i) (k i) ω)
      = ((N : ℝ)⁻¹) ^ m * ∏ i : Fin m, ∑ j : Fin N, Y i (k i j) ω := by
    simp [blockAverage_apply, Finset.prod_mul_distrib]
  rw [hL, Fintype.prod_sum fun i (j : Fin N) => Y i (k i j) ω, Fintype.expect_eq_sum_div_card]
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, card_univ, div_eq_inv_mul]
  push_cast
  simp [inv_pow]

/-- The **fixed-start selection**: the window of length `n + 1` beginning at `r`. -/
def fixedStart (r : ℕ) : ∀ n : ℕ, Fin (n + 1) → ℕ := fun _ j => r + (j : ℕ)

@[simp]
theorem fixedStart_apply (r n : ℕ) (j : Fin (n + 1)) : fixedStart r n j = r + (j : ℕ) := (rfl)

/-- The fixed-start selection is injective at each length. -/
theorem fixedStart_injective (r n : ℕ) : Function.Injective (fixedStart r n) :=
  (add_right_injective r).comp Fin.val_injective

/-- The eventual form, as the moving-selection theorems take it. -/
theorem fixedStart_eventually_injective (r : ℕ) :
    ∀ᶠ n in atTop, Function.Injective (fixedStart r n) :=
  Eventually.of_forall (fixedStart_injective r)

/-- **The squared deviation of an average, as a double sum.** For a nonempty finite index set `s`,
the square of `(#s)⁻¹ * ∑ i ∈ s, a i - b` is `(#s)⁻¹ ^ 2` times the double sum of
`(a i - b) * (a j - b)` over `s × s`. -/
theorem average_sub_sq_eq_sum_sum {ι R : Type*} [Field R] [CharZero R] {s : Finset ι}
    (hs : s.Nonempty) (a : ι → R) (b : R) :
    ((s.card : R)⁻¹ * (∑ i ∈ s, a i) - b) ^ 2
      = (s.card : R)⁻¹ ^ 2 * ∑ i ∈ s, ∑ j ∈ s, (a i - b) * (a j - b) := by
  -- both normalised sums are expectations, where subtracting a constant is `expect_const`
  have hexp : ∀ f : ι → R, (s.card : R)⁻¹ * (∑ i ∈ s, f i) = 𝔼 i ∈ s, f i := fun f => by
    rw [Finset.expect_eq_sum_div_card, div_eq_inv_mul]
  have h1 : (s.card : R)⁻¹ * (∑ i ∈ s, a i) - b = (s.card : R)⁻¹ * ∑ i ∈ s, (a i - b) := by
    rw [hexp, hexp, Finset.expect_sub_distrib, Finset.expect_const hs]
  rw [h1, mul_pow, sq (∑ i ∈ s, (a i - b)), Finset.sum_mul_sum]

/-- **A Birkhoff average is a prefix average of the iterated observable.** For any self-map `T` and
any real observable `F`, `birkhoffAverage ℝ T F n` is the prefix average of `i ↦ F ∘ T^[i]`.

Nothing about any particular dynamical system enters: both sides are the same normalised sum. This
is the bridge from Mathlib's mean-ergodic theory, which speaks of Birkhoff averages, to the
block-average API, which speaks of averages of a process over a selection of coordinates. -/
theorem birkhoffAverage_eq_prefixAverage {β : Type*} (T : β → β) (F : β → ℝ) (n : ℕ) :
    birkhoffAverage ℝ T F n = prefixAverage (fun i (x : β) => F (T^[i] x)) n := by
  funext x
  rw [birkhoffAverage, birkhoffSum, prefixAverage_apply, smul_eq_mul]
  congr 1
  exact Finset.sum_range fun i => F (T^[i] x)

/-! ### The unit interval

A block average of `[0,1]`-valued coordinates stays in `[0,1]`. This is the bound the product
convergence lemmas need, and it is pure order algebra — no measure and no norm is involved, so the
`‖·‖ ≤ 1` form is left to the consumer that has a normed structure in scope. -/

/-- A block average of nonnegative coordinates is nonnegative. Only the sampled coordinates at the
one point `ω` are constrained. -/
theorem blockAverage_nonneg {Y : ℕ → Ω → ℝ} {n : ℕ} {k : Fin n → ℕ} {ω : Ω}
    (hY : ∀ i, 0 ≤ Y (k i) ω) : 0 ≤ blockAverage Y k ω := by
  rw [blockAverage, Finset.expect_apply]
  exact Finset.expect_nonneg fun i _ => hY i

/-- A block average of coordinates bounded by `1` is bounded by `1`. Only the sampled coordinates
at the one point `ω` are constrained. -/
theorem blockAverage_le_one {Y : ℕ → Ω → ℝ} {n : ℕ} {k : Fin n → ℕ} {ω : Ω}
    (hY : ∀ i, Y (k i) ω ≤ 1) : blockAverage Y k ω ≤ 1 := by
  rw [blockAverage, Finset.expect_apply]
  rcases Finset.univ.eq_empty_or_nonempty (α := Fin n) with h | h
  · simp [h]
  · exact Finset.expect_le h fun i _ => hY i

end Probability

end TauCeti
