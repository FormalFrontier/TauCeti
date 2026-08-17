/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RingTheory.DividedPowers.RootString.Basic

/-!
# Normal ordering divided powers along the type-`G₂` root string

Let `x`, `y`, `z`, `w`, `v`, and `s` belong to an associative algebra over `ℚ`, with

```text
x * y = y * x + z,   x * z = z * x + 2 • w,   x * w = w * x + 3 • v,   w * z = z * w + 3 • s,
```

`v` and `s` commuting with `x`, `y` commuting with `z`, `w` commuting with `v`, and `s` commuting
with `z`, `w`, and `v`. This is the situation of the two simple roots of a root system of type `G₂`,
`α` short and `β` long: with `x` and `y` the Chevalley root vectors of `α` and `β`, the divided
powers `(ad x)ᵏ y / k!` of the inner derivation are the root vectors of `α + β`, `2α + β`, and
`3α + β` up to sign, and `s` is the root vector of `3α + 2β`. Every one of the four brackets above
is integral.

The resulting straightening rule is again coefficient-one,

```text
x⁽ᵐ⁾ y⁽ⁿ⁾ = ∑ b + c + d + 2e ≤ n, b + 2c + 3d + 3e ≤ m,
              y⁽ⁿ⁻ᵇ⁻ᶜ⁻ᵈ⁻²ᵉ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ v⁽ᵈ⁾ s⁽ᵉ⁾ x⁽ᵐ⁻ᵇ⁻²ᶜ⁻³ᵈ⁻³ᵉ⁾,
```

so it holds in a Kostant integral form and, after base change, over a ring of any characteristic.
The two exponents attached to a summand are the pair `(i, j)` of the root `i α + j β` it comes from:
`z` contributes `(1, 1)`, `w` contributes `(2, 1)`, `v` contributes `(3, 1)`, and `s` contributes
`(3, 2)`. That last root is what makes the type-`G₂` case genuinely longer than the chain treated in
`TauCeti.RingTheory.DividedPowers.RootString.Basic`: `3α + 2β` is not on the `α`-string through `β`,
and it enters through the bracket `w * z = z * w + 3 • s` rather than through `ad x`.

Type `G₂` has one further configuration, not treated here: for the pair `α`, `α + β` the roots
`i α + j (α + β)` with `i, j > 0` are `2α + β`, `3α + β`, and `3α + 2β`, the last of them carrying
the exponents `(i, j) = (1, 2)` and arising from `⁅y, ⁅x, y⁆⁆` rather than from `⁅w, z⁆`.

The proof feeds `TauCeti.Associative.dividedPower_mul_of_ad_dividedPower_series` the sequence

```text
d k = ∑ b + 2c + 3d + 3e = k,  y⁽ⁿ⁻ᵇ⁻ᶜ⁻ᵈ⁻²ᵉ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ v⁽ᵈ⁾ s⁽ᵉ⁾,
```

which is the `k`-th divided power of the inner derivation `ad x` applied to `y⁽ⁿ⁾`. Verifying its
defining recurrence is the whole content: moving `x` across one normal-ordered monomial lengthens
the `z`-power with coefficient `b + 1`, the `w`-power with coefficient `2 (c + 1)`, the `v`-power
with coefficient `3 (d + 1)`, or the `s`-power with coefficient `3 (e + 1)`, and the four
contributions to a summand of `d (k + 1)` add up to `b + 2c + 3d + 3e = k + 1`.

## Main results

* `TauCeti.Associative.mul_dividedPower_of_commutator_eq_two_nsmul`: moving one element across a
  divided power when the commutator itself has a central second commutator.
* `TauCeti.Associative.commutator_eq_three_nsmul_of_commute`: the bracket `w * z = z * w + 3 • s`
  is forced by the other type-`G₂` brackets, so a consumer holding a Chevalley basis need not
  supply it separately.
* `TauCeti.Associative.dividedPower_mul_dividedPower_of_commutator_eq_three_nsmul`: the
  coefficient-one straightening rule for the type-`G₂` root string.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Associative

open Finset

variable {A : Type*} [Semiring A] [Algebra ℚ A] {x y z w v s : A}

/-! ## Moving one element across a power whose commutator is not central -/

-- The ordinary-power form, stated with an exponent of the shape `b + 2` so that no truncated
-- subtraction appears. Both released terms are present from that exponent on.
omit [Algebra ℚ A] in
private theorem mul_pow_of_commutator_eq_two_nsmul {a d : A} (hxz : x * z = z * x + a)
    (haz : a * z = z * a + 2 • d) (hzd : Commute z d) (b : ℕ) :
    x * z ^ (b + 2) =
      z ^ (b + 2) * x + (b + 2) • (z ^ (b + 1) * a) + ((b + 2) * (b + 1)) • (z ^ b * d) := by
  induction b with
  | zero =>
      change x * z ^ 2 = z ^ 2 * x + 2 • (z ^ 1 * a) + 2 • (z ^ 0 * d)
      rw [pow_two, pow_one, pow_zero, one_mul]
      calc x * (z * z) = (x * z) * z := (mul_assoc _ _ _).symm
        _ = (z * x + a) * z := by rw [hxz]
        _ = z * (x * z) + a * z := by rw [add_mul, mul_assoc]
        _ = z * (z * x + a) + (z * a + 2 • d) := by rw [hxz, haz]
        _ = _ := by rw [mul_add, ← mul_assoc]; abel
  | succ b ih =>
      have hp3 : z ^ (b + 3) = z ^ (b + 2) * z := by
        rw [show b + 3 = b + 2 + 1 from by omega, pow_succ]
      have hp2 : z ^ (b + 2) = z ^ (b + 1) * z := by
        rw [show b + 2 = b + 1 + 1 from by omega, pow_succ]
      have hp1 : z ^ (b + 1) = z ^ b * z := by rw [pow_succ]
      have hfin : ∀ T P Q : A,
          T + P + ((b + 2) • P + (2 * (b + 2)) • Q) + ((b + 2) * (b + 1)) • Q =
            T + (b + 3) • P + ((b + 3) * (b + 2)) • Q := by
        intro T P Q
        have h1 : (b + 3) • P = P + (b + 2) • P := by
          rw [show b + 3 = 1 + (b + 2) from by omega, add_smul, one_smul]
        have h2 : ((b + 3) * (b + 2)) • Q = (2 * (b + 2)) • Q + ((b + 2) * (b + 1)) • Q := by
          rw [← add_smul, show 2 * (b + 2) + (b + 2) * (b + 1) = (b + 3) * (b + 2) from by ring]
        rw [h1, h2]
        abel
      rw [show b + 1 + 2 = b + 3 from by omega, show b + 1 + 1 = b + 2 from by omega]
      calc x * z ^ (b + 3)
          = (x * z ^ (b + 2)) * z := by rw [hp3, ← mul_assoc]
        _ = z ^ (b + 2) * (x * z) + (b + 2) • (z ^ (b + 1) * (a * z)) +
              ((b + 2) * (b + 1)) • (z ^ b * (d * z)) := by
            rw [ih, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, mul_assoc, mul_assoc,
              mul_assoc]
        _ = z ^ (b + 2) * (z * x + a) + (b + 2) • (z ^ (b + 1) * (z * a + 2 • d)) +
              ((b + 2) * (b + 1)) • (z ^ b * (z * d)) := by rw [hxz, haz, hzd.eq]
        _ = (z ^ (b + 3) * x + z ^ (b + 2) * a) +
              ((b + 2) • (z ^ (b + 2) * a) + (2 * (b + 2)) • (z ^ (b + 1) * d)) +
              ((b + 2) * (b + 1)) • (z ^ (b + 1) * d) := by
            rw [mul_add, ← mul_assoc, ← hp3, mul_add, ← mul_assoc, ← hp2, mul_smul_comm, smul_add,
              smul_smul, mul_comm (b + 2) 2, ← mul_assoc, ← hp1]
        _ = _ := hfin _ _ _

/-- **Moving one element across a divided power with a non-central commutator.** Suppose
`x * z = z * x + a` and `a * z = z * a + 2 • d`, with `d` commuting with `z`. Then

```text
x z⁽ᵇ⁾ = z⁽ᵇ⁾ x + z⁽ᵇ⁻¹⁾ a + z⁽ᵇ⁻²⁾ d,
```

both released terms being present exactly when their exponent is defined. Every coefficient is `1`:
the factor `2` in the second hypothesis is exactly what the divided powers absorb, which is why
`d` rather than `a * z - z * a` is the integral datum. Taking `d = 0` recovers
`mul_dividedPower_of_commutator_eq'`. -/
theorem mul_dividedPower_of_commutator_eq_two_nsmul {a d : A} (hxz : x * z = z * x + a)
    (haz : a * z = z * a + 2 • d) (hzd : Commute z d) (b : ℕ) :
    x * dividedPower b z =
      dividedPower b z * x + (if 0 < b then dividedPower (b - 1) z * a else 0) +
        (if 1 < b then dividedPower (b - 2) z * d else 0) := by
  match b with
  | 0 => simp
  | 1 => simpa using hxz
  | (b + 2) =>
      have key : ∀ c F G : ℚ, c ≠ 0 → F = c * G → F⁻¹ * c = G⁻¹ := by
        intro c F G hc hF
        subst hF
        rw [mul_inv, mul_comm c⁻¹ G⁻¹, mul_assoc, inv_mul_cancel₀ hc, mul_one]
      have hsucc : ((b + 2).factorial : ℚ) = ((b + 2 : ℕ) : ℚ) * ((b + 1).factorial : ℚ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) (Nat.factorial_succ (b + 1))
      have hsucc2 : ((b + 2).factorial : ℚ) =
          (((b + 2) * (b + 1) : ℕ) : ℚ) * (b.factorial : ℚ) := by
        have hnat : (b + 2).factorial = (b + 2) * (b + 1) * b.factorial := by
          rw [Nat.factorial_succ (b + 1), Nat.factorial_succ b, mul_assoc]
        exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hnat
      have hfac1 : ((b + 2).factorial : ℚ)⁻¹ * ((b + 2 : ℕ) : ℚ) = ((b + 1).factorial : ℚ)⁻¹ :=
        key _ _ _ (Nat.cast_ne_zero.mpr (by omega)) hsucc
      have hfac2 : ((b + 2).factorial : ℚ)⁻¹ * (((b + 2) * (b + 1) : ℕ) : ℚ) =
          (b.factorial : ℚ)⁻¹ :=
        key _ _ _ (Nat.cast_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) hsucc2
      rw [ite_eq_left (by omega : 0 < b + 2), ite_eq_left (by omega : 1 < b + 2),
        show b + 2 - 1 = b + 1 from by omega, show b + 2 - 2 = b from by omega]
      simp only [dividedPower_def, smul_mul_assoc]
      rw [mul_smul_comm, mul_pow_of_commutator_eq_two_nsmul hxz haz hzd b, smul_add, smul_add]
      congr 1
      · congr 1
        rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, hfac1]
      · rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, hfac2]

/-! ## The bracket at the root `3α + 2β` -/

/-- **The fifth bracket is forced.** In the type-`G₂` configuration the bracket of the root vectors
of `α + β` and `2α + β` is not an independent datum: it is three times the root vector of `3α + 2β`
that already appears as `⁅y, v⁆`. The proof is the Jacobi identity applied to `⁅x, ⁅y, w⁆⁆ = 0`.

A consumer holding a Chevalley basis therefore supplies the four brackets along the `α`-string
together with `⁅e_β, e_{3α+β}⁆`, and reads off the hypothesis
`w * z = z * w + 3 • s` of the straightening rule below. -/
theorem commutator_eq_three_nsmul_of_commute {B : Type*} [Ring B] {x y z w v s : B}
    (hxy : x * y = y * x + z) (hxw : x * w = w * x + 3 • v) (hyw : Commute y w)
    (hyv : y * v = v * y + s) :
    w * z = z * w + 3 • s := by
  have h1 : x * y * w = w * y * x + 3 • (v * y) + 3 • s + z * w := by
    calc x * y * w = (y * x + z) * w := by rw [hxy]
      _ = y * (x * w) + z * w := by rw [add_mul, mul_assoc]
      _ = y * (w * x + 3 • v) + z * w := by rw [hxw]
      _ = y * w * x + 3 • (y * v) + z * w := by rw [mul_add, mul_smul_comm, ← mul_assoc]
      _ = w * y * x + 3 • (v * y + s) + z * w := by rw [hyw.eq, hyv]
      _ = _ := by rw [smul_add]; abel
  have h2 : x * y * w = w * y * x + 3 • (v * y) + w * z := by
    calc x * y * w = x * (w * y) := by rw [mul_assoc, hyw.eq]
      _ = (w * x + 3 • v) * y := by rw [← mul_assoc, hxw]
      _ = w * (y * x + z) + 3 • (v * y) := by rw [add_mul, mul_assoc, hxy, smul_mul_assoc]
      _ = w * y * x + w * z + 3 • (v * y) := by rw [mul_add, ← mul_assoc]
      _ = _ := by abel
  have h3 : w * y * x + 3 • (v * y) + (3 • s + z * w) =
      w * y * x + 3 • (v * y) + w * z := by
    rw [← add_assoc]
    exact h1.symm.trans h2
  rw [← add_left_cancel h3]
  abel

/-! ## Moving one element across a single normal-ordered monomial -/

-- Moving `x` across a normal-ordered monomial `y⁽ᵃ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ v⁽ᵈ⁾ s⁽ᵉ⁾ releases four terms: one
-- trading a `y` for a `z`, one trading a `z` for a `w`, one trading two `z`s for an `s`, and one
-- trading a `w` for a `v`. The monomials are written right-associated, which is the order in which
-- `x` meets their factors.
private theorem mul_dividedPower_quintuple (hxy : x * y = y * x + z)
    (hxz : x * z = z * x + 2 • w) (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s)
    (hxv : Commute x v) (hxs : Commute x s) (hyz : Commute y z) (hwv : Commute w v)
    (hzs : Commute z s) (hws : Commute w s) (hvs : Commute v s) (a b c d e : ℕ) :
    x * (dividedPower a y * (dividedPower b z * (dividedPower c w *
        (dividedPower d v * dividedPower e s)))) =
      dividedPower a y * (dividedPower b z * (dividedPower c w *
          (dividedPower d v * dividedPower e s))) * x +
        (if 0 < a then (b + 1) • (dividedPower (a - 1) y * (dividedPower (b + 1) z *
          (dividedPower c w * (dividedPower d v * dividedPower e s)))) else 0) +
        (if 0 < b then (2 * (c + 1)) • (dividedPower a y * (dividedPower (b - 1) z *
          (dividedPower (c + 1) w * (dividedPower d v * dividedPower e s)))) else 0) +
        (if 1 < b then (3 * (e + 1)) • (dividedPower a y * (dividedPower (b - 2) z *
          (dividedPower c w * (dividedPower d v * dividedPower (e + 1) s)))) else 0) +
        (if 0 < c then (3 * (d + 1)) • (dividedPower a y * (dividedPower b z *
          (dividedPower (c - 1) w * (dividedPower (d + 1) v * dividedPower e s)))) else 0) := by
  have hxV : Commute x (dividedPower d v) := by
    simpa using commute_dividedPower_dividedPower hxv 1 d
  have hxS : Commute x (dividedPower e s) := by
    simpa using commute_dividedPower_dividedPower hxs 1 e
  have hsW : Commute s (dividedPower c w) := by
    simpa using commute_dividedPower_dividedPower hws.symm 1 c
  have hsV : Commute s (dividedPower d v) := by
    simpa using commute_dividedPower_dividedPower hvs.symm 1 d
  -- The second commutator of `x` with `z` is `2 • (3 • s)`, which is what the divided powers of
  -- `z` absorb into a single copy of `s`.
  have haz : (2 • w) * z = z * (2 • w) + 2 • (3 • s) := by
    rw [smul_mul_assoc, hwz, mul_smul_comm, smul_add]
  -- Push `x` rightwards through the monomial, one factor at a time.
  have e0 : x * (dividedPower d v * dividedPower e s) =
      dividedPower d v * dividedPower e s * x := by
    rw [← mul_assoc, hxV.eq, mul_assoc, hxS.eq, ← mul_assoc]
  have e1 : x * (dividedPower c w * (dividedPower d v * dividedPower e s)) =
      dividedPower c w * (dividedPower d v * dividedPower e s) * x +
        (if 0 < c then dividedPower (c - 1) w * (3 • v) else 0) *
          (dividedPower d v * dividedPower e s) := by
    rw [← mul_assoc, mul_dividedPower_of_commutator_eq' hxw (hwv.smul_right 3) c, add_mul,
      mul_assoc, e0, ← mul_assoc]
  have e2 : x * (dividedPower b z * (dividedPower c w *
        (dividedPower d v * dividedPower e s))) =
      dividedPower b z * (dividedPower c w * (dividedPower d v * dividedPower e s)) * x +
        dividedPower b z * ((if 0 < c then dividedPower (c - 1) w * (3 • v) else 0) *
          (dividedPower d v * dividedPower e s)) +
        (if 0 < b then dividedPower (b - 1) z * (2 • w) else 0) *
          (dividedPower c w * (dividedPower d v * dividedPower e s)) +
        (if 1 < b then dividedPower (b - 2) z * (3 • s) else 0) *
          (dividedPower c w * (dividedPower d v * dividedPower e s)) := by
    rw [← mul_assoc, mul_dividedPower_of_commutator_eq_two_nsmul hxz haz (hzs.smul_right 3) b,
      add_mul, add_mul, mul_assoc, e1, mul_add, ← mul_assoc]
  rw [← mul_assoc, mul_dividedPower_of_commutator_eq' hxy hyz a, add_mul, mul_assoc, e2,
    mul_add, mul_add, mul_add, ← mul_assoc]
  -- Now evaluate the four released terms, absorbing each new factor into its own divided power.
  have tA : (if 0 < a then dividedPower (a - 1) y * z else 0) *
      (dividedPower b z * (dividedPower c w * (dividedPower d v * dividedPower e s))) =
      if 0 < a then (b + 1) • (dividedPower (a - 1) y * (dividedPower (b + 1) z *
        (dividedPower c w * (dividedPower d v * dividedPower e s)))) else 0 := by
    split_ifs with ha
    · rw [mul_assoc, ← mul_assoc z, self_mul_dividedPower, smul_mul_assoc, mul_smul_comm]
    · rw [zero_mul]
  have tB : dividedPower a y * ((if 0 < b then dividedPower (b - 1) z * (2 • w) else 0) *
      (dividedPower c w * (dividedPower d v * dividedPower e s))) =
      if 0 < b then (2 * (c + 1)) • (dividedPower a y * (dividedPower (b - 1) z *
        (dividedPower (c + 1) w * (dividedPower d v * dividedPower e s)))) else 0 := by
    split_ifs with hb
    · rw [mul_assoc, smul_mul_assoc, ← mul_assoc w, self_mul_dividedPower, smul_mul_assoc,
        smul_smul, mul_smul_comm, mul_smul_comm]
    · rw [zero_mul, mul_zero]
  have hmove : s * (dividedPower c w * (dividedPower d v * dividedPower e s)) =
      (e + 1) • (dividedPower c w * (dividedPower d v * dividedPower (e + 1) s)) := by
    rw [← mul_assoc, hsW.eq, mul_assoc, ← mul_assoc s, hsV.eq, mul_assoc,
      self_mul_dividedPower, mul_smul_comm, mul_smul_comm]
  have tC : dividedPower a y * ((if 1 < b then dividedPower (b - 2) z * (3 • s) else 0) *
      (dividedPower c w * (dividedPower d v * dividedPower e s))) =
      if 1 < b then (3 * (e + 1)) • (dividedPower a y * (dividedPower (b - 2) z *
        (dividedPower c w * (dividedPower d v * dividedPower (e + 1) s)))) else 0 := by
    split_ifs with hb
    · rw [mul_assoc, smul_mul_assoc, hmove, smul_smul, mul_smul_comm, mul_smul_comm]
    · rw [zero_mul, mul_zero]
  have tD : dividedPower a y * (dividedPower b z *
      ((if 0 < c then dividedPower (c - 1) w * (3 • v) else 0) *
        (dividedPower d v * dividedPower e s))) =
      if 0 < c then (3 * (d + 1)) • (dividedPower a y * (dividedPower b z *
        (dividedPower (c - 1) w * (dividedPower (d + 1) v * dividedPower e s)))) else 0 := by
    split_ifs with hc
    · rw [mul_assoc, smul_mul_assoc, ← mul_assoc v, self_mul_dividedPower, smul_mul_assoc,
        smul_smul, mul_smul_comm, mul_smul_comm, mul_smul_comm]
    · rw [zero_mul, mul_zero, mul_zero]
  rw [tA, tB, tC, tD]
  abel

/-! ## The divided-power series of the inner derivation -/

/-- The exponents occurring in the `k`-th divided power of `ad x` applied to `y⁽ⁿ⁾`: quadruples
`(b, c, d, e)` with `b + c + d + 2e ≤ n` and `b + 2c + 3d + 3e = k`. -/
private def g2SeriesIndex (n k : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  {p ∈ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1) |
    p.1 + p.2.1 + p.2.2.1 + 2 * p.2.2.2 ≤ n ∧
      p.1 + 2 * p.2.1 + 3 * p.2.2.1 + 3 * p.2.2.2 = k}

private theorem mem_g2SeriesIndex {n k : ℕ} {p : ℕ × ℕ × ℕ × ℕ} :
    p ∈ g2SeriesIndex n k ↔
      p.1 + p.2.1 + p.2.2.1 + 2 * p.2.2.2 ≤ n ∧
        p.1 + 2 * p.2.1 + 3 * p.2.2.1 + 3 * p.2.2.2 = k := by
  simp only [g2SeriesIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- The normal-ordered monomial attached to a quadruple of exponents, the `y`-exponent being
whatever is left of `n`. -/
private noncomputable def g2Monomial (y z w v s : A) (n : ℕ) (p : ℕ × ℕ × ℕ × ℕ) : A :=
  dividedPower (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) y *
    (dividedPower p.1 z * (dividedPower p.2.1 w *
      (dividedPower p.2.2.1 v * dividedPower p.2.2.2 s)))

/-- The `k`-th divided power of the inner derivation `ad x`, applied to `y⁽ⁿ⁾`. -/
private noncomputable def g2Series (y z w v s : A) (n k : ℕ) : A :=
  ∑ p ∈ g2SeriesIndex n k, g2Monomial y z w v s n p

private theorem g2Series_zero (n : ℕ) : g2Series y z w v s n 0 = dividedPower n y := by
  have hindex : g2SeriesIndex n 0 = {(0, 0, 0, 0)} := by
    ext ⟨b, c, d, e⟩
    simp only [mem_g2SeriesIndex, Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [g2Series, hindex]
  simp [g2Monomial]

/-! ### Reindexing the four exponent shifts

Each of the four ways to advance the series moves the index `p` of weighted degree `k` to an
index of weighted degree `k + 1` by a fixed shift of the exponents.  All four are instances of
one reindexing lemma, which leaves each of them only the arithmetic of its own shift. -/

private theorem mem_filter_g2SeriesIndex {n k : ℕ} {P : (ℕ × ℕ × ℕ × ℕ) → Prop} [DecidablePred P]
    {p : ℕ × ℕ × ℕ × ℕ} :
    p ∈ {p ∈ g2SeriesIndex n k | P p} ↔
      (p.1 + p.2.1 + p.2.2.1 + 2 * p.2.2.2 ≤ n ∧
        p.1 + 2 * p.2.1 + 3 * p.2.2.1 + 3 * p.2.2.2 = k) ∧ P p := by
  rw [Finset.mem_filter, mem_g2SeriesIndex]

private theorem sum_g2Monomial_shift {n k : ℕ} {P Q : (ℕ × ℕ × ℕ × ℕ) → Prop}
    [DecidablePred P] [DecidablePred Q]
    (f finv : (ℕ × ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ × ℕ)) (coeff : (ℕ × ℕ × ℕ × ℕ) → ℕ)
    (hf : ∀ p, (p.1 + p.2.1 + p.2.2.1 + 2 * p.2.2.2 ≤ n ∧
        p.1 + 2 * p.2.1 + 3 * p.2.2.1 + 3 * p.2.2.2 = k) ∧ P p →
      ((f p).1 + (f p).2.1 + (f p).2.2.1 + 2 * (f p).2.2.2 ≤ n ∧
        (f p).1 + 2 * (f p).2.1 + 3 * (f p).2.2.1 + 3 * (f p).2.2.2 = k + 1) ∧ Q (f p))
    (hfinv : ∀ q, (q.1 + q.2.1 + q.2.2.1 + 2 * q.2.2.2 ≤ n ∧
        q.1 + 2 * q.2.1 + 3 * q.2.2.1 + 3 * q.2.2.2 = k + 1) ∧ Q q →
      ((finv q).1 + (finv q).2.1 + (finv q).2.2.1 + 2 * (finv q).2.2.2 ≤ n ∧
        (finv q).1 + 2 * (finv q).2.1 + 3 * (finv q).2.2.1 + 3 * (finv q).2.2.2 = k) ∧ P (finv q))
    (hleft : ∀ p, (p.1 + p.2.1 + p.2.2.1 + 2 * p.2.2.2 ≤ n ∧
        p.1 + 2 * p.2.1 + 3 * p.2.2.1 + 3 * p.2.2.2 = k) ∧ P p → finv (f p) = p)
    (hright : ∀ q, (q.1 + q.2.1 + q.2.2.1 + 2 * q.2.2.2 ≤ n ∧
        q.1 + 2 * q.2.1 + 3 * q.2.2.1 + 3 * q.2.2.2 = k + 1) ∧ Q q → f (finv q) = q) :
    ∑ p ∈ {p ∈ g2SeriesIndex n k | P p},
        (coeff (f p)) • g2Monomial y z w v s n (f p) =
      ∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | Q q}, coeff q • g2Monomial y z w v s n q :=
  Finset.sum_nbij' f finv
    (fun _ hp => mem_filter_g2SeriesIndex.mpr (hf _ (mem_filter_g2SeriesIndex.mp hp)))
    (fun _ hq => mem_filter_g2SeriesIndex.mpr (hfinv _ (mem_filter_g2SeriesIndex.mp hq)))
    (fun _ hp => hleft _ (mem_filter_g2SeriesIndex.mp hp))
    (fun _ hq => hright _ (mem_filter_g2SeriesIndex.mp hq))
    (fun _ _ => rfl)

-- The defining recurrence of the sequence: it is what `dividedPower_mul_of_ad_dividedPower_series`
-- consumes. Each summand of `g2Series n (k + 1)` is reached in four ways, with coefficients
-- `b`, `2c`, `3d`, and `3e`, which add up to `k + 1`.
private theorem mul_g2Series (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s) (hxv : Commute x v)
    (hxs : Commute x s) (hyz : Commute y z) (hwv : Commute w v) (hzs : Commute z s)
    (hws : Commute w s) (hvs : Commute v s) (n k : ℕ) :
    x * g2Series y z w v s n k =
      g2Series y z w v s n k * x + (k + 1) • g2Series y z w v s n (k + 1) := by
  classical
  have hterm : ∀ p ∈ g2SeriesIndex n k,
      x * g2Monomial y z w v s n p =
        g2Monomial y z w v s n p * x +
          (if 0 < n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2 then
            (p.1 + 1) • g2Monomial y z w v s n (p.1 + 1, p.2.1, p.2.2.1, p.2.2.2) else 0) +
          (if 0 < p.1 then
            (2 * (p.2.1 + 1)) •
              g2Monomial y z w v s n (p.1 - 1, p.2.1 + 1, p.2.2.1, p.2.2.2) else 0) +
          (if 1 < p.1 then
            (3 * (p.2.2.2 + 1)) •
              g2Monomial y z w v s n (p.1 - 2, p.2.1, p.2.2.1, p.2.2.2 + 1) else 0) +
          (if 0 < p.2.1 then
            (3 * (p.2.2.1 + 1)) •
              g2Monomial y z w v s n (p.1, p.2.1 - 1, p.2.2.1 + 1, p.2.2.2) else 0) := by
    rintro ⟨b, c, d, e⟩ _
    have hA : n - (b + 1) - c - d - 2 * e = n - b - c - d - 2 * e - 1 := by omega
    have hB : 0 < b → n - (b - 1) - (c + 1) - d - 2 * e = n - b - c - d - 2 * e := by omega
    have hC : 1 < b → n - (b - 2) - c - d - 2 * (e + 1) = n - b - c - d - 2 * e := by omega
    have hD : 0 < c → n - b - (c - 1) - (d + 1) - 2 * e = n - b - c - d - 2 * e := by omega
    have eqB : (if 0 < b then (2 * (c + 1)) •
          (dividedPower (n - (b - 1) - (c + 1) - d - 2 * e) y * (dividedPower (b - 1) z *
            (dividedPower (c + 1) w * (dividedPower d v * dividedPower e s)))) else 0) =
        (if 0 < b then (2 * (c + 1)) •
          (dividedPower (n - b - c - d - 2 * e) y * (dividedPower (b - 1) z *
            (dividedPower (c + 1) w * (dividedPower d v * dividedPower e s)))) else 0) := by
      split_ifs with h
      · rw [hB h]
      · rfl
    have eqC : (if 1 < b then (3 * (e + 1)) •
          (dividedPower (n - (b - 2) - c - d - 2 * (e + 1)) y * (dividedPower (b - 2) z *
            (dividedPower c w * (dividedPower d v * dividedPower (e + 1) s)))) else 0) =
        (if 1 < b then (3 * (e + 1)) •
          (dividedPower (n - b - c - d - 2 * e) y * (dividedPower (b - 2) z *
            (dividedPower c w * (dividedPower d v * dividedPower (e + 1) s)))) else 0) := by
      split_ifs with h
      · rw [hC h]
      · rfl
    have eqD : (if 0 < c then (3 * (d + 1)) •
          (dividedPower (n - b - (c - 1) - (d + 1) - 2 * e) y * (dividedPower b z *
            (dividedPower (c - 1) w * (dividedPower (d + 1) v * dividedPower e s)))) else 0) =
        (if 0 < c then (3 * (d + 1)) •
          (dividedPower (n - b - c - d - 2 * e) y * (dividedPower b z *
            (dividedPower (c - 1) w * (dividedPower (d + 1) v * dividedPower e s)))) else 0) := by
      split_ifs with h
      · rw [hD h]
      · rfl
    simp only [g2Monomial]
    rw [mul_dividedPower_quintuple hxy hxz hxw hwz hxv hxs hyz hwv hzs hws hvs
      (n - b - c - d - 2 * e) b c d e, hA, eqB, eqC, eqD]
  -- The four reindexings that identify the released families with the summands of the next term.
  have hshiftA : ∑ p ∈ {p ∈ g2SeriesIndex n k | 0 < n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2},
        (p.1 + 1) • g2Monomial y z w v s n (p.1 + 1, p.2.1, p.2.2.1, p.2.2.2) =
      ∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.1}, q.1 • g2Monomial y z w v s n q := by
    refine sum_g2Monomial_shift (fun p => (p.1 + 1, p.2.1, p.2.2.1, p.2.2.2))
      (fun q => (q.1 - 1, q.2.1, q.2.2.1, q.2.2.2)) (fun q => q.1) ?_ ?_ ?_ ?_
    · rintro ⟨b, c, d, e⟩ hp
      dsimp at *; omega
    · rintro ⟨b, c, d, e⟩ hq
      dsimp at *; omega
    · rintro ⟨b, c, d, e⟩ _
      simp
    · rintro ⟨b, c, d, e⟩ hq
      simp [Nat.sub_add_cancel hq.2]
  have hshiftB : ∑ p ∈ {p ∈ g2SeriesIndex n k | 0 < p.1},
        (2 * (p.2.1 + 1)) • g2Monomial y z w v s n (p.1 - 1, p.2.1 + 1, p.2.2.1, p.2.2.2) =
      ∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.2.1},
        (2 * q.2.1) • g2Monomial y z w v s n q := by
    refine sum_g2Monomial_shift (fun p => (p.1 - 1, p.2.1 + 1, p.2.2.1, p.2.2.2))
      (fun q => (q.1 + 1, q.2.1 - 1, q.2.2.1, q.2.2.2)) (fun q => 2 * q.2.1) ?_ ?_ ?_ ?_
    · rintro ⟨b, c, d, e⟩ hp
      dsimp at *; omega
    · rintro ⟨b, c, d, e⟩ hq
      dsimp at *; omega
    · rintro ⟨b, c, d, e⟩ hp
      simp [Nat.sub_add_cancel hp.2]
    · rintro ⟨b, c, d, e⟩ hq
      simp [Nat.sub_add_cancel hq.2]
  have hshiftC : ∑ p ∈ {p ∈ g2SeriesIndex n k | 1 < p.1},
        (3 * (p.2.2.2 + 1)) • g2Monomial y z w v s n (p.1 - 2, p.2.1, p.2.2.1, p.2.2.2 + 1) =
      ∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.2.2.2},
        (3 * q.2.2.2) • g2Monomial y z w v s n q := by
    refine sum_g2Monomial_shift (fun p => (p.1 - 2, p.2.1, p.2.2.1, p.2.2.2 + 1))
      (fun q => (q.1 + 2, q.2.1, q.2.2.1, q.2.2.2 - 1)) (fun q => 3 * q.2.2.2) ?_ ?_ ?_ ?_
    · rintro ⟨b, c, d, e⟩ hp
      dsimp at *; omega
    · rintro ⟨b, c, d, e⟩ hq
      dsimp at *; omega
    · rintro ⟨b, c, d, e⟩ hp
      simp [show b - 2 + 2 = b from by omega]
    · rintro ⟨b, c, d, e⟩ hq
      simp [Nat.sub_add_cancel hq.2]
  have hshiftD : ∑ p ∈ {p ∈ g2SeriesIndex n k | 0 < p.2.1},
        (3 * (p.2.2.1 + 1)) • g2Monomial y z w v s n (p.1, p.2.1 - 1, p.2.2.1 + 1, p.2.2.2) =
      ∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.2.2.1},
        (3 * q.2.2.1) • g2Monomial y z w v s n q := by
    refine sum_g2Monomial_shift (fun p => (p.1, p.2.1 - 1, p.2.2.1 + 1, p.2.2.2))
      (fun q => (q.1, q.2.1 + 1, q.2.2.1 - 1, q.2.2.2)) (fun q => 3 * q.2.2.1) ?_ ?_ ?_ ?_
    · rintro ⟨b, c, d, e⟩ hp
      dsimp at *; omega
    · rintro ⟨b, c, d, e⟩ hq
      dsimp at *; omega
    · rintro ⟨b, c, d, e⟩ hp
      simp [Nat.sub_add_cancel hp.2]
    · rintro ⟨b, c, d, e⟩ hq
      simp [Nat.sub_add_cancel hq.2]
  -- Every summand of the next term is reached with total coefficient `b + 2c + 3d + 3e = k + 1`.
  have hcombine : ∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.1}, q.1 • g2Monomial y z w v s n q +
        ∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.2.1},
          (2 * q.2.1) • g2Monomial y z w v s n q +
        ∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.2.2.2},
          (3 * q.2.2.2) • g2Monomial y z w v s n q +
        ∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.2.2.1},
          (3 * q.2.2.1) • g2Monomial y z w v s n q =
      (k + 1) • g2Series y z w v s n (k + 1) := by
    rw [Finset.sum_filter_of_ne (fun q _ hq => Nat.pos_of_ne_zero fun h => hq (by simp [h])),
      Finset.sum_filter_of_ne (fun q _ hq => Nat.pos_of_ne_zero fun h => hq (by simp [h])),
      Finset.sum_filter_of_ne (fun q _ hq => Nat.pos_of_ne_zero fun h => hq (by simp [h])),
      Finset.sum_filter_of_ne (fun q _ hq => Nat.pos_of_ne_zero fun h => hq (by simp [h])),
      g2Series, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← add_smul, ← add_smul, ← add_smul]
    congr 1
    have := (mem_g2SeriesIndex.mp hq).2
    omega
  rw [g2Series, Finset.mul_sum, Finset.sum_mul, Finset.sum_congr rfl hterm]
  simp only [Finset.sum_add_distrib, ← Finset.sum_filter]
  rw [hshiftA, hshiftB, hshiftC, hshiftD, add_assoc, add_assoc, add_assoc, ← add_assoc _ _
    (∑ q ∈ {q ∈ g2SeriesIndex n (k + 1) | 0 < q.2.2.1}, (3 * q.2.2.1) • g2Monomial y z w v s n q),
    ← add_assoc, ← hcombine]
  abel

/-! ## The straightening rule -/

/-- The quadruples of exponents in the straightening rule for the type-`G₂` root string, one
coordinate for each of the roots `α + β`, `2α + β`, `3α + β`, and `3α + 2β`. -/
def chainG2Index (m n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  {p ∈ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1) |
    p.1 + p.2.1 + p.2.2.1 + 2 * p.2.2.2 ≤ n ∧
      p.1 + 2 * p.2.1 + 3 * p.2.2.1 + 3 * p.2.2.2 ≤ m}

/-- Membership in `chainG2Index` in terms of its two mathematical inequalities. -/
@[simp]
theorem mem_chainG2Index {m n : ℕ} {p : ℕ × ℕ × ℕ × ℕ} :
    p ∈ chainG2Index m n ↔
      p.1 + p.2.1 + p.2.2.1 + 2 * p.2.2.2 ≤ n ∧
        p.1 + 2 * p.2.1 + 3 * p.2.2.1 + 3 * p.2.2.2 ≤ m := by
  simp only [chainG2Index, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- **Coefficient-one normal ordering along the type-`G₂` root string.** Suppose

```text
x * y = y * x + z,   x * z = z * x + 2 • w,   x * w = w * x + 3 • v,   w * z = z * w + 3 • s,
```

that `v` and `s` commute with `x`, that `y` commutes with `z`, that `w` commutes with `v`, and that
`s` commutes with `z`, `w`, and `v`. Then

```text
x⁽ᵐ⁾ y⁽ⁿ⁾ = ∑ b + c + d + 2e ≤ n, b + 2c + 3d + 3e ≤ m,
              y⁽ⁿ⁻ᵇ⁻ᶜ⁻ᵈ⁻²ᵉ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ v⁽ᵈ⁾ s⁽ᵉ⁾ x⁽ᵐ⁻ᵇ⁻²ᶜ⁻³ᵈ⁻³ᵉ⁾.
```

Every coefficient in the divided-power basis is `1`, so the identity survives restriction to a
Kostant integral lattice and base change to a ring of arbitrary characteristic. Taking `v = 0` and
`s = 0` and discarding the terms with `d ≠ 0` or `e ≠ 0` recovers the chain rule
`dividedPower_mul_dividedPower_of_commutator_eq_two_nsmul`. -/
theorem dividedPower_mul_dividedPower_of_commutator_eq_three_nsmul (hxy : x * y = y * x + z)
    (hxz : x * z = z * x + 2 • w) (hxw : x * w = w * x + 3 • v) (hwz : w * z = z * w + 3 • s)
    (hxv : Commute x v) (hxs : Commute x s) (hyz : Commute y z) (hwv : Commute w v)
    (hzs : Commute z s) (hws : Commute w s) (hvs : Commute v s) (m n : ℕ) :
    dividedPower m x * dividedPower n y =
      ∑ p ∈ chainG2Index m n,
        dividedPower (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) y * dividedPower p.1 z *
          dividedPower p.2.1 w * dividedPower p.2.2.1 v * dividedPower p.2.2.2 s *
          dividedPower (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2) x := by
  classical
  have hseries := dividedPower_mul_of_ad_dividedPower_series (x := x)
    (d := g2Series y z w v s n)
    (fun k => mul_g2Series hxy hxz hxw hwz hxv hxs hyz hwv hzs hws hvs n k) m
  rw [g2Series_zero] at hseries
  rw [hseries]
  simp only [mul_assoc]
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun p : ℕ × ℕ × ℕ × ℕ => p.1 + 2 * p.2.1 + 3 * p.2.2.1 + 3 * p.2.2.2)
    (t := range (m + 1))
    (fun p hp => Finset.mem_range.mpr (by have := mem_chainG2Index.mp hp; omega))
    (fun p => dividedPower (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) y *
      (dividedPower p.1 z * (dividedPower p.2.1 w * (dividedPower p.2.2.1 v *
        (dividedPower p.2.2.2 s *
          dividedPower (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2) x)))))]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hfib : {p ∈ chainG2Index m n | p.1 + 2 * p.2.1 + 3 * p.2.2.1 + 3 * p.2.2.2 = k} =
      g2SeriesIndex n k := by
    ext p
    simp only [Finset.mem_filter, mem_chainG2Index, mem_g2SeriesIndex]
    omega
  rw [hfib, g2Series, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := (mem_g2SeriesIndex.mp hp).2
  have hq : m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2 = m - k := by omega
  rw [hq, g2Monomial]
  simp only [mul_assoc]

end TauCeti.Associative
