/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Comparing two products of elements of the unit ball

For families taking values in the closed unit ball of a seminormed commutative ring, the difference
of the products is controlled by the sum of the pointwise differences:

```text
‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖
```

Only `‖a i‖ ≤ 1` and `‖b i‖ ≤ 1` are needed; the argument uses subadditivity and submultiplicativity
of the norm and nothing else, so it holds over `ℂ` as well as `ℝ`, and norm definiteness is never
used — hence `SeminormedCommRing` rather than `NormedCommRing`. The unit-ball bound is what makes
the constant `1`; the same telescoping argument with a uniform bound `C` gives `C ^ (s.card - 1)`
and is not needed here.

`abs_prod_sub_prod_le_sum_abs_sub` is the real-valued corollary, phrased with `|·|`, which is the
form the probability consumers use.

This is the elementary step that turns coordinatewise convergence of finitely many bounded
observables into convergence of their product, without Hölder or dominated-convergence machinery.
It is motivated by `TauCetiRoadmap/Exchangeability/README.md`, **Layer 3** (the L² averaging library
and the standard-Borel de Finetti route): both that route and the Layer 5 Koopman route reduce a
block factorization to convergence of a product of finitely many block averages.
-/

public section

namespace TauCeti

open Finset

/-- **A finite product of unit-ball elements lies in the unit ball.** Mathlib's
`Finset.norm_prod_le` gives this over a `NormedCommRing`, but only submultiplicativity of the norm
and `‖1‖ = 1` are used, so it holds over a seminormed ring. -/
theorem norm_prod_le_one {ι R : Type*} [SeminormedCommRing R] [NormOneClass R] {s : Finset ι}
    {b : ι → R} (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) : ‖∏ i ∈ s, b i‖ ≤ 1 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
      rw [Finset.prod_insert hj]
      exact (norm_mul_le _ _).trans (mul_le_one₀ (hb j (Finset.mem_insert_self j s))
        (norm_nonneg _) (ih fun i hi => hb i (Finset.mem_insert_of_mem hi)))

/-- **Telescoping bound for a product of unit-ball elements.** If `‖a i‖ ≤ 1` and `‖b i‖ ≤ 1` for
every `i ∈ s`, then the difference of the products is at most the sum of the pointwise
differences. -/
theorem norm_prod_sub_prod_le_sum_norm_sub {ι R : Type*} [SeminormedCommRing R]
    [NormOneClass R]
    (s : Finset ι) {a b : ι → R}
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
      have hmem : ∀ i ∈ s, i ∈ insert j s := fun i hi => Finset.mem_insert_of_mem hi
      have hjs : j ∈ insert j s := Finset.mem_insert_self j s
      have ihs := ih (fun i hi => ha i (hmem i hi)) (fun i hi => hb i (hmem i hi))
      have hprodb : ‖∏ i ∈ s, b i‖ ≤ 1 := norm_prod_le_one fun i hi => hb i (hmem i hi)
      rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
      have hsplit : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i
          = a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)‖ ≤ ∑ i ∈ s, ‖a i - b i‖ :=
        calc ‖a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)‖
            ≤ ‖a j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ := norm_mul_le _ _
          _ ≤ 1 * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ := by gcongr; exact ha j hjs
          _ = ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ := one_mul _
          _ ≤ ∑ i ∈ s, ‖a i - b i‖ := ihs
      have h2 : ‖(a j - b j) * ∏ i ∈ s, b i‖ ≤ ‖a j - b j‖ :=
        calc ‖(a j - b j) * ∏ i ∈ s, b i‖ ≤ ‖a j - b j‖ * ‖∏ i ∈ s, b i‖ := norm_mul_le _ _
          _ ≤ ‖a j - b j‖ * 1 := by gcongr
          _ = ‖a j - b j‖ := mul_one _
      linarith

/-- **Real-valued form**, phrased with `|·|`: the shape the probability consumers use, where the
factors are block averages and conditional expectations of indicators, all in `[0, 1]`. -/
theorem abs_prod_sub_prod_le_sum_abs_sub {ι : Type*} (s : Finset ι) {a b : ι → ℝ}
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  simpa only [Real.norm_eq_abs] using
    norm_prod_sub_prod_le_sum_norm_sub s (a := a) (b := b)
      (fun i hi => by simpa only [Real.norm_eq_abs] using ha i hi)
      (fun i hi => by simpa only [Real.norm_eq_abs] using hb i hi)

end TauCeti
