/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Comparing two products of elements of the unit ball

For families taking values in the unit ball of a linearly ordered commutative ring, the difference
of the products is controlled by the sum of the pointwise differences:

```text
|∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i|
```

This is the elementary step that turns coordinatewise convergence of finitely many bounded
observables into convergence of their product, without any Hölder or dominated-convergence
machinery: an `L¹` bound on each factor sums to an `L¹` bound on the product.

Only `|a i| ≤ 1` and `|b i| ≤ 1` are needed — neither nonnegativity nor a real codomain. That bound
is what makes the constant `1`; the same telescoping argument with a uniform bound `C` gives
`C ^ (s.card - 1)` and is not needed here.
-/

public section

namespace TauCeti

open Finset

/-- **Telescoping bound for a product of elements of the unit ball.** If `|a i| ≤ 1` and
`|b i| ≤ 1` for every `i ∈ s`, then the difference of the products is at most the sum of the
pointwise differences. -/
theorem abs_prod_sub_prod_le_sum_abs_sub {ι R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (s : Finset ι) {a b : ι → R}
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
      have hmem : ∀ i ∈ s, i ∈ insert j s := fun i hi => Finset.mem_insert_of_mem hi
      have hjs : j ∈ insert j s := Finset.mem_insert_self j s
      have ihs := ih (fun i hi => ha i (hmem i hi)) (fun i hi => hb i (hmem i hi))
      have hprodb : |∏ i ∈ s, b i| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun i _ => abs_nonneg _) fun i hi => hb i (hmem i hi)
      rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
      have hsplit : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i
          = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have h1 : |a j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| :=
        calc |a j| * |∏ i ∈ s, a i - ∏ i ∈ s, b i|
            ≤ 1 * |∏ i ∈ s, a i - ∏ i ∈ s, b i| := by gcongr; exact ha j hjs
          _ = |∏ i ∈ s, a i - ∏ i ∈ s, b i| := one_mul _
          _ ≤ ∑ i ∈ s, |a i - b i| := ihs
      have h2 : |a j - b j| * |∏ i ∈ s, b i| ≤ |a j - b j| :=
        calc |a j - b j| * |∏ i ∈ s, b i| ≤ |a j - b j| * 1 := by gcongr
          _ = |a j - b j| := mul_one _
      linarith

end TauCeti
