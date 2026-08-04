/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Comparing two products of numbers in the unit interval

For families taking values in `[0, 1]`, the difference of the products is controlled by the sum of
the pointwise differences:

```text
|∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i|
```

This is the elementary step that turns coordinatewise convergence of finitely many bounded
observables into convergence of their product, without any Hölder or dominated-convergence
machinery: an `L¹` bound on each factor sums to an `L¹` bound on the product.

The unit-interval hypothesis is what makes the constant `1`; the same telescoping argument with a
uniform bound `C` gives `C ^ (s.card - 1)` and is not needed here.
-/

public section

namespace TauCeti

open Finset

/-- **Telescoping bound for a product of numbers in the unit interval.** If `a i` and `b i` both lie
in `[0, 1]` for every `i ∈ s`, then the difference of the products is at most the sum of the
pointwise differences. -/
theorem abs_prod_sub_prod_le_sum_abs_sub {ι : Type*} (s : Finset ι) {a b : ι → ℝ}
    (ha₀ : ∀ i ∈ s, 0 ≤ a i) (ha₁ : ∀ i ∈ s, a i ≤ 1)
    (hb₀ : ∀ i ∈ s, 0 ≤ b i) (hb₁ : ∀ i ∈ s, b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
      have hmem : ∀ i ∈ s, i ∈ insert j s := fun i hi => Finset.mem_insert_of_mem hi
      have hjs : j ∈ insert j s := Finset.mem_insert_self j s
      have ihs := ih (fun i hi => ha₀ i (hmem i hi)) (fun i hi => ha₁ i (hmem i hi))
        (fun i hi => hb₀ i (hmem i hi)) (fun i hi => hb₁ i (hmem i hi))
      have hprodb : |∏ i ∈ s, b i| ≤ 1 := by
        rw [abs_of_nonneg (Finset.prod_nonneg fun i hi => hb₀ i (hmem i hi))]
        exact Finset.prod_le_one (fun i hi => hb₀ i (hmem i hi)) fun i hi => hb₁ i (hmem i hi)
      rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
      have hsplit : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i
          = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have h1 : |a j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
        have haj : |a j| ≤ 1 := by
          rw [abs_of_nonneg (ha₀ j hjs)]; exact ha₁ j hjs
        calc |a j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i|
            ≤ 1 * |∏ i ∈ s, a i - ∏ i ∈ s, b i| := by gcongr
          _ = |∏ i ∈ s, a i - ∏ i ∈ s, b i| := one_mul _
          _ ≤ ∑ i ∈ s, |a i - b i| := ihs
      have h2 : |a j - b j| * |∏ i ∈ s, b i| ≤ |a j - b j| := by
        calc |a j - b j| * |∏ i ∈ s, b i| ≤ |a j - b j| * 1 := by gcongr
          _ = |a j - b j| := mul_one _
      linarith

end TauCeti
