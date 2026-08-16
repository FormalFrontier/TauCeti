/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RingTheory.DividedPowers.NormalOrdering

/-!
# Normal ordering divided powers along a root string of length three

Let `x`, `y`, `z`, and `w` belong to an associative algebra over `ℚ`, with

```text
x * y = y * x + z,   x * z = z * x + 2 • w,
```

`w` commuting with `x`, and `y`, `z`, `w` pairwise commuting. This is the situation of two roots
`α`, `β` for which `α + β` and `2α + β` are roots while `3α + β` and `α + 2β` are not: with `x` and
`y` the root vectors of `α` and `β` in a Chevalley basis, `z` is `N_{α β}` times the root vector of
`α + β`, and the second divided power `(ad x)² y / 2` of the inner derivation is again an *integral*
multiple `w` of the root vector of `2α + β`.

The resulting straightening rule is again coefficient-one,

```text
x⁽ᵐ⁾ y⁽ⁿ⁾ = ∑ b + c ≤ n, b + 2c ≤ m,  y⁽ⁿ⁻ᵇ⁻ᶜ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ x⁽ᵐ⁻ᵇ⁻²ᶜ⁾,
```

so it holds in a Kostant integral form and, after base change, over a ring of any characteristic.
The class-two rule `TauCeti.Associative.dividedPower_mul_dividedPower_of_commutator_eq` is the
degenerate case `w = 0`, and covers every pair of non-proportional roots in a simply-laced root
system; the rule proved here is what the multiply-laced types `B`, `C`, `F₄`, and `G₂` need.

The proof feeds `TauCeti.Associative.dividedPower_mul_of_commutator_series` the sequence

```text
d k = ∑ b + 2c = k,  y⁽ⁿ⁻ᵇ⁻ᶜ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾,
```

which is the `k`-th divided power of the inner derivation `ad x` applied to `y⁽ⁿ⁾`. Verifying the
defining recurrence of that sequence is the whole content: moving `x` across one summand either
lengthens the `z`-power, with coefficient `b + 1`, or lengthens the `w`-power, with coefficient
`2 (c + 1)`, and the two contributions to a summand of `d (k + 1)` add up to `b + 2c = k + 1`.

## Main results

* `TauCeti.Associative.dividedPower_mul_dividedPower_of_root_string`: the coefficient-one
  straightening rule for a root string of length three.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Associative

open Finset

variable {A : Type*} [Semiring A] [Algebra ℚ A] {x y z w : A}

/-! ## Moving one element across a single normal-ordered monomial -/

-- The one-sided normal-ordering rule of `NormalOrdering`, stated without a successor pattern so
-- that it can be applied to an exponent that is only known at run time.
private theorem mul_dividedPower_of_commutator_eq' (hxy : x * y = y * x + z) (hyz : Commute y z)
    (n : ℕ) :
    x * dividedPower n y =
      dividedPower n y * x + if 0 < n then dividedPower (n - 1) y * z else 0 := by
  cases n with
  | zero => simp
  | succ n => simpa using mul_dividedPower_of_commutator_eq hxy hyz n

-- Moving `x` across a normal-ordered monomial `y⁽ᵃ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾` releases at most two terms: one
-- that trades a `y` for a `z`, and one that trades a `z` for a `w`. The coefficient `2` of the
-- second commutator is what makes the `w`-coefficient `2 (c + 1)` rather than `c + 1`.
private theorem mul_dividedPower_triple (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : Commute x w) (hyz : Commute y z) (hzw : Commute z w) (a b c : ℕ) :
    x * (dividedPower a y * dividedPower b z * dividedPower c w) =
      dividedPower a y * dividedPower b z * dividedPower c w * x +
        (if 0 < a then
          (b + 1) • (dividedPower (a - 1) y * dividedPower (b + 1) z * dividedPower c w)
          else 0) +
        (if 0 < b then
          (2 * (c + 1)) •
            (dividedPower a y * dividedPower (b - 1) z * dividedPower (c + 1) w)
          else 0) := by
  have hxwc : Commute x (dividedPower c w) := by
    simpa using commute_dividedPower_dividedPower hxw 1 c
  have hzw2 : Commute z (2 • w) := by
    rw [two_smul]
    exact hzw.add_right hzw
  -- Split off the two commutator terms, keeping them in unevaluated form.
  have key : x * (dividedPower a y * dividedPower b z * dividedPower c w) =
      dividedPower a y * dividedPower b z * dividedPower c w * x +
        (if 0 < a then dividedPower (a - 1) y * z else 0) *
          dividedPower b z * dividedPower c w +
        dividedPower a y *
          ((if 0 < b then dividedPower (b - 1) z * (2 • w) else 0) * dividedPower c w) := by
    calc x * (dividedPower a y * dividedPower b z * dividedPower c w)
        = x * dividedPower a y * dividedPower b z * dividedPower c w := by
          simp only [mul_assoc]
      _ = (dividedPower a y * (x * dividedPower b z)) * dividedPower c w +
            (if 0 < a then dividedPower (a - 1) y * z else 0) *
              dividedPower b z * dividedPower c w := by
          rw [mul_dividedPower_of_commutator_eq' hxy hyz a, add_mul, add_mul,
            mul_assoc (dividedPower a y) x]
      _ = _ := by
          rw [mul_dividedPower_of_commutator_eq' hxz hzw2 b, mul_add, add_mul,
            ← mul_assoc (dividedPower a y) (dividedPower b z) x,
            mul_assoc (dividedPower a y * dividedPower b z) x (dividedPower c w), hxwc.eq,
            ← mul_assoc (dividedPower a y * dividedPower b z) (dividedPower c w) x,
            mul_assoc (dividedPower a y)
              (if 0 < b then dividedPower (b - 1) z * (2 • w) else 0) (dividedPower c w)]
          abel
  rw [key]
  congr 1
  · congr 1
    split_ifs with ha
    · rw [mul_assoc (dividedPower (a - 1) y) z, self_mul_dividedPower, mul_smul_comm,
        smul_mul_assoc]
    · simp
  · split_ifs with hb
    · rw [mul_assoc (dividedPower (b - 1) z), smul_mul_assoc, self_mul_dividedPower, smul_smul,
        mul_smul_comm, mul_smul_comm, mul_assoc]
    · simp

/-! ## The divided-power series of the inner derivation -/

/-- The exponents occurring in the `k`-th divided power of `ad x` applied to `y⁽ⁿ⁾`: pairs `(b, c)`
with `b + c ≤ n` and `b + 2c = k`, the remaining `y`-exponent being `n - b - c`. -/
private def rootStringIndex (n k : ℕ) : Finset (ℕ × ℕ) :=
  {p ∈ range (n + 1) ×ˢ range (n + 1) | p.1 + p.2 ≤ n ∧ p.1 + 2 * p.2 = k}

private theorem mem_rootStringIndex {n k : ℕ} {p : ℕ × ℕ} :
    p ∈ rootStringIndex n k ↔ p.1 + p.2 ≤ n ∧ p.1 + 2 * p.2 = k := by
  simp only [rootStringIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- The `k`-th divided power of the inner derivation `ad x`, applied to `y⁽ⁿ⁾`. -/
private noncomputable def rootStringSeries (y z w : A) (n k : ℕ) : A :=
  ∑ p ∈ rootStringIndex n k,
    dividedPower (n - p.1 - p.2) y * dividedPower p.1 z * dividedPower p.2 w

private theorem rootStringSeries_zero (n : ℕ) : rootStringSeries y z w n 0 = dividedPower n y := by
  have hindex : rootStringIndex n 0 = {(0, 0)} := by
    ext ⟨b, c⟩
    simp only [mem_rootStringIndex, Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [rootStringSeries, hindex]
  simp

-- The defining recurrence of the sequence: it is what `dividedPower_mul_of_commutator_series`
-- consumes. Each summand of `rootStringSeries n (k + 1)` is reached in two ways, from a longer
-- `y`-power with coefficient `b` and from a longer `z`-power with coefficient `2c`, and
-- `b + 2c = k + 1`.
private theorem mul_rootStringSeries (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : Commute x w) (hyz : Commute y z) (hzw : Commute z w) (n k : ℕ) :
    x * rootStringSeries y z w n k =
      rootStringSeries y z w n k * x + (k + 1) • rootStringSeries y z w n (k + 1) := by
  classical
  have hterm : ∀ p ∈ rootStringIndex n k,
      x * (dividedPower (n - p.1 - p.2) y * dividedPower p.1 z * dividedPower p.2 w) =
        dividedPower (n - p.1 - p.2) y * dividedPower p.1 z * dividedPower p.2 w * x +
          (if 0 < n - p.1 - p.2 then
            (p.1 + 1) • (dividedPower (n - (p.1 + 1) - p.2) y *
              dividedPower (p.1 + 1) z * dividedPower p.2 w) else 0) +
          (if 0 < p.1 then
            (2 * (p.2 + 1)) • (dividedPower (n - (p.1 - 1) - (p.2 + 1)) y *
              dividedPower (p.1 - 1) z * dividedPower (p.2 + 1) w) else 0) := by
    intro p hp
    have h1 : n - (p.1 + 1) - p.2 = n - p.1 - p.2 - 1 := by omega
    have h2 : 0 < p.1 → n - (p.1 - 1) - (p.2 + 1) = n - p.1 - p.2 := by omega
    rw [mul_dividedPower_triple hxy hxz hxw hyz hzw (n - p.1 - p.2) p.1 p.2, h1]
    rcases Nat.eq_zero_or_pos p.1 with hb | hb
    · simp [hb]
    · rw [h2 hb]
  -- The reindexings that identify the two released families with the summands of the next term.
  have hshiftz : ∑ p ∈ {p ∈ rootStringIndex n k | 0 < n - p.1 - p.2},
        (p.1 + 1) • (dividedPower (n - (p.1 + 1) - p.2) y *
          dividedPower (p.1 + 1) z * dividedPower p.2 w) =
      ∑ q ∈ {q ∈ rootStringIndex n (k + 1) | 0 < q.1},
        q.1 • (dividedPower (n - q.1 - q.2) y * dividedPower q.1 z * dividedPower q.2 w) := by
    refine Finset.sum_nbij' (fun p => (p.1 + 1, p.2)) (fun q => (q.1 - 1, q.2)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨b, c⟩ hp
      simp only [Finset.mem_filter, mem_rootStringIndex] at hp ⊢
      omega
    · rintro ⟨b, c⟩ hq
      simp only [Finset.mem_filter, mem_rootStringIndex] at hq ⊢
      omega
    · rintro ⟨b, c⟩ _
      simp
    · rintro ⟨b, c⟩ hq
      have hb : 0 < b := by
        simp only [Finset.mem_filter, mem_rootStringIndex] at hq
        omega
      simp [Nat.sub_add_cancel hb]
    · rintro ⟨b, c⟩ _
      simp
  have hshiftw : ∑ p ∈ {p ∈ rootStringIndex n k | 0 < p.1},
        (2 * (p.2 + 1)) • (dividedPower (n - (p.1 - 1) - (p.2 + 1)) y *
          dividedPower (p.1 - 1) z * dividedPower (p.2 + 1) w) =
      ∑ q ∈ {q ∈ rootStringIndex n (k + 1) | 0 < q.2},
        (2 * q.2) • (dividedPower (n - q.1 - q.2) y * dividedPower q.1 z * dividedPower q.2 w) := by
    refine Finset.sum_nbij' (fun p => (p.1 - 1, p.2 + 1)) (fun q => (q.1 + 1, q.2 - 1))
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨b, c⟩ hp
      simp only [Finset.mem_filter, mem_rootStringIndex] at hp ⊢
      omega
    · rintro ⟨b, c⟩ hq
      simp only [Finset.mem_filter, mem_rootStringIndex] at hq ⊢
      omega
    · rintro ⟨b, c⟩ hp
      have hb : 0 < b := by
        simp only [Finset.mem_filter, mem_rootStringIndex] at hp
        omega
      simp [Nat.sub_add_cancel hb]
    · rintro ⟨b, c⟩ hq
      have hc : 0 < c := by
        simp only [Finset.mem_filter, mem_rootStringIndex] at hq
        omega
      simp [Nat.sub_add_cancel hc]
    · rintro ⟨b, c⟩ _
      simp
  -- Every summand of the next term is reached with total coefficient `b + 2c = k + 1`.
  have hcombine : ∑ q ∈ {q ∈ rootStringIndex n (k + 1) | 0 < q.1},
        q.1 • (dividedPower (n - q.1 - q.2) y * dividedPower q.1 z * dividedPower q.2 w) +
      ∑ q ∈ {q ∈ rootStringIndex n (k + 1) | 0 < q.2},
        (2 * q.2) • (dividedPower (n - q.1 - q.2) y * dividedPower q.1 z * dividedPower q.2 w) =
      (k + 1) • rootStringSeries y z w n (k + 1) := by
    rw [Finset.sum_filter_of_ne
        (fun q _ hq => Nat.pos_of_ne_zero fun h => hq (by simp [h])),
      Finset.sum_filter_of_ne
        (fun q _ hq => Nat.pos_of_ne_zero fun h => hq (by simp [h])),
      rootStringSeries, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← add_smul]
    congr 1
    have := (mem_rootStringIndex.mp hq).2
    omega
  rw [rootStringSeries, Finset.mul_sum, Finset.sum_mul, Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    hshiftz, hshiftw, add_assoc, hcombine]

/-! ## The straightening rule -/

/-- **Coefficient-one normal ordering along a root string of length three.** Suppose

```text
x * y = y * x + z,   x * z = z * x + 2 • w,
```

that `w` commutes with `x`, and that `y`, `z`, `w` commute with one another. Then

```text
x⁽ᵐ⁾ y⁽ⁿ⁾ = ∑ b + c ≤ n, b + 2c ≤ m,  y⁽ⁿ⁻ᵇ⁻ᶜ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ x⁽ᵐ⁻ᵇ⁻²ᶜ⁾.
```

Every coefficient in the divided-power basis is `1`, so the identity survives restriction to a
Kostant integral lattice and base change to a ring of arbitrary characteristic. Taking `w = 0`
and discarding the terms with `c ≠ 0` recovers the class-two rule
`dividedPower_mul_dividedPower_of_commutator_eq`. -/
theorem dividedPower_mul_dividedPower_of_root_string (hxy : x * y = y * x + z)
    (hxz : x * z = z * x + 2 • w) (hxw : Commute x w) (hyz : Commute y z) (hzw : Commute z w)
    (m n : ℕ) :
    dividedPower m x * dividedPower n y =
      ∑ p ∈ {p ∈ range (n + 1) ×ˢ range (n + 1) | p.1 + p.2 ≤ n ∧ p.1 + 2 * p.2 ≤ m},
        dividedPower (n - p.1 - p.2) y * dividedPower p.1 z * dividedPower p.2 w *
          dividedPower (m - p.1 - 2 * p.2) x := by
  classical
  set S : Finset (ℕ × ℕ) :=
    {p ∈ range (n + 1) ×ˢ range (n + 1) | p.1 + p.2 ≤ n ∧ p.1 + 2 * p.2 ≤ m} with hS
  have hmemS : ∀ p : ℕ × ℕ, p ∈ S ↔ p.1 + p.2 ≤ n ∧ p.1 + 2 * p.2 ≤ m := by
    intro p
    simp only [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  have hseries := dividedPower_mul_of_commutator_series
    (x := x) (d := rootStringSeries y z w n)
    (fun k => mul_rootStringSeries hxy hxz hxw hyz hzw n k) m
  rw [rootStringSeries_zero] at hseries
  rw [hseries]
  -- Group the flat sum by the value of `b + 2c`, which is the index of the series.
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 + 2 * p.2)
    (t := range (m + 1)) (fun p hp => Finset.mem_range.mpr (by have := (hmemS p).mp hp; omega))
    (fun p => dividedPower (n - p.1 - p.2) y * dividedPower p.1 z * dividedPower p.2 w *
      dividedPower (m - p.1 - 2 * p.2) x)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hfib : {p ∈ S | p.1 + 2 * p.2 = k} = rootStringIndex n k := by
    ext p
    simp only [Finset.mem_filter, hmemS, mem_rootStringIndex]
    omega
  rw [hfib, rootStringSeries, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := (mem_rootStringIndex.mp hp).2
  have : m - p.1 - 2 * p.2 = m - k := by omega
  rw [this]

end TauCeti.Associative
