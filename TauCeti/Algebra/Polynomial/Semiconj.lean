/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Binomial

/-!
# Polynomial evaluation across a semiconjugacy relation

If `a * x = x * (a + c)` and `c` commutes with `x`, then moving a polynomial in `a` past
`x ^ n` shifts its argument by `n • c`:

```text
p(a) xⁿ = xⁿ p(a + n c).
```

The reverse reordering shifts by `-n c`.  The main application is to the generalized binomial
coefficients `Ring.choose a m`: these are the Cartan generators of a Kostant integral form, while
the powers are the numerators of its root-vector divided powers.

The first result, `SemiconjBy.smeval_right`, is the general mechanism.  It says that polynomial
evaluation preserves both right-hand entries of `SemiconjBy`.  The remaining results specialize
it to an additive shift and then to `Ring.choose`.

## Main results

* `SemiconjBy.smeval_right`: simultaneous polynomial evaluation preserves semiconjugacy.
* `Polynomial.smeval_mul_pow_eq`: the corresponding polynomial reordering identity.
* `TauCeti.ringChoose_mul_pow_eq` and `TauCeti.pow_mul_ringChoose_eq`: its two
  binomial-coefficient forms.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace SemiconjBy

universe u v

variable {R : Type u} {A : Type v}
variable [Semiring R] [Semiring A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- Polynomial evaluation preserves the two right-hand entries of a semiconjugacy relation.

This is the polynomial analogue of `SemiconjBy.pow_right`, with coefficients moved through the
semiconjugating element by the central scalar action. -/
theorem smeval_right {a x y : A} (h : SemiconjBy a x y) (p : Polynomial R) :
    SemiconjBy a (Polynomial.smeval p x) (Polynomial.smeval p y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.smeval_add] using hp.add_right hq
  | monomial n r =>
      simpa only [Polynomial.smeval_monomial] using (h.pow_right n).smul_right r

end SemiconjBy

namespace TauCeti

universe u

variable {A : Type u} [Ring A]

/-- Moving `a` across `x ^ n` accumulates `n` copies of the additive shift `c`.

The commutation hypothesis on `c` is necessary: it is what lets each newly introduced copy of
`c` pass the next copy of `x`. -/
private theorem mul_pow_eq_pow_mul_add_nsmul {a x c : A} (h : a * x = x * (a + c))
    (hc : Commute c x) (n : ℕ) :
    a * x ^ n = x ^ n * (a + n • c) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc]
      have hshift : (a + n • c) * x = x * (a + (n + 1) • c) := by
        calc
          (a + n • c) * x = a * x + (n • c) * x := add_mul _ _ _
          _ = x * (a + c) + x * (n • c) := by rw [h, (hc.smul_left n).eq]
          _ = x * ((a + c) + n • c) := (mul_add _ _ _).symm
          _ = x * (a + (n + 1) • c) := by
            congr 1
            rw [succ_nsmul]
            abel
      rw [hshift, ← mul_assoc, ← pow_succ]

/-- Moving `a` to the right across `x ^ n` produces the opposite accumulated shift. -/
private theorem pow_mul_eq_sub_nsmul_mul_pow {a x c : A} (h : a * x = x * (a + c))
    (hc : Commute c x) (n : ℕ) :
    x ^ n * a = (a - n • c) * x ^ n := by
  have hsub : (a - n • c) * x = x * ((a - n • c) + c) := by
    calc
      (a - n • c) * x = a * x - (n • c) * x := sub_mul _ _ _
      _ = x * (a + c) - x * (n • c) := by rw [h, (hc.smul_left n).eq]
      _ = x * ((a + c) - n • c) := (mul_sub _ _ _).symm
      _ = x * ((a - n • c) + c) := by
        congr 1
        abel
  have hpow := mul_pow_eq_pow_mul_add_nsmul hsub hc n
  simpa only [sub_add_cancel] using hpow.symm

namespace Polynomial

/-- A polynomial in `a` can be moved to the right across `x ^ n` by shifting its argument by
`n • c`. -/
theorem smeval_mul_pow_eq (p : _root_.Polynomial ℤ) {a x c : A}
    (h : a * x = x * (a + c))
    (hc : Commute c x) (n : ℕ) :
    _root_.Polynomial.smeval p a * x ^ n =
      x ^ n * _root_.Polynomial.smeval p (a + n • c) := by
  have hs : SemiconjBy (x ^ n) (a + n • c) a :=
    (mul_pow_eq_pow_mul_add_nsmul h hc n).symm
  exact (hs.smeval_right p).eq.symm

/-- A polynomial in `a` can be moved to the left across `x ^ n` by shifting its argument by
`-n • c`. -/
theorem pow_mul_smeval_eq (p : _root_.Polynomial ℤ) {a x c : A}
    (h : a * x = x * (a + c))
    (hc : Commute c x) (n : ℕ) :
    x ^ n * _root_.Polynomial.smeval p a =
      _root_.Polynomial.smeval p (a - n • c) * x ^ n := by
  have hs : SemiconjBy (x ^ n) a (a - n • c) :=
    pow_mul_eq_sub_nsmul_mul_pow h hc n
  exact (hs.smeval_right p).eq

end Polynomial

attribute [local instance] BinomialRing.toIsAddTorsionFree

/-- A generalized binomial coefficient in `a` can be moved to the right across `x ^ n` by
shifting its argument by `n • c`. -/
theorem ringChoose_mul_pow_eq [BinomialRing A] (m : ℕ) {a x c : A}
    (h : a * x = x * (a + c)) (hc : Commute c x) (n : ℕ) :
    Ring.choose a m * x ^ n = x ^ n * Ring.choose (a + n • c) m := by
  apply nsmul_right_injective m.factorial_ne_zero
  calc
    m.factorial • (Ring.choose a m * x ^ n) =
        (m.factorial • Ring.choose a m) * x ^ n := by
      simp only [nsmul_eq_mul, mul_assoc]
    _ = (descPochhammer ℤ m).smeval a * x ^ n := by
      rw [Ring.descPochhammer_eq_factorial_smul_choose]
    _ = x ^ n * (descPochhammer ℤ m).smeval (a + n • c) :=
      Polynomial.smeval_mul_pow_eq _ h hc n
    _ = x ^ n * (m.factorial • Ring.choose (a + n • c) m) := by
      rw [Ring.descPochhammer_eq_factorial_smul_choose]
    _ = m.factorial • (x ^ n * Ring.choose (a + n • c) m) := by
      rw [nsmul_eq_mul m.factorial]
      calc
        x ^ n * (↑m.factorial * Ring.choose (a + n • c) m) =
            (x ^ n * ↑m.factorial) * Ring.choose (a + n • c) m :=
          (mul_assoc _ _ _).symm
        _ =
            ↑m.factorial * x ^ n * Ring.choose (a + n • c) m := by
          rw [(Nat.cast_commute _ (x ^ n)).eq.symm]
        _ = ↑m.factorial * (x ^ n * Ring.choose (a + n • c) m) :=
          mul_assoc _ _ _
        _ = m.factorial • (x ^ n * Ring.choose (a + n • c) m) :=
          (nsmul_eq_mul _ _).symm

/-- A generalized binomial coefficient in `a` can be moved to the left across `x ^ n` by
shifting its argument by `-n • c`. -/
theorem pow_mul_ringChoose_eq [BinomialRing A] (m : ℕ) {a x c : A}
    (h : a * x = x * (a + c)) (hc : Commute c x) (n : ℕ) :
    x ^ n * Ring.choose a m = Ring.choose (a - n • c) m * x ^ n := by
  apply nsmul_right_injective m.factorial_ne_zero
  calc
    m.factorial • (x ^ n * Ring.choose a m) =
        x ^ n * (m.factorial • Ring.choose a m) := by
      calc
        m.factorial • (x ^ n * Ring.choose a m) =
            ↑m.factorial * (x ^ n * Ring.choose a m) := nsmul_eq_mul _ _
        _ = (↑m.factorial * x ^ n) * Ring.choose a m := (mul_assoc _ _ _).symm
        _ = (x ^ n * ↑m.factorial) * Ring.choose a m := by
          rw [(Nat.cast_commute _ (x ^ n)).eq]
        _ = x ^ n * (↑m.factorial * Ring.choose a m) := mul_assoc _ _ _
        _ = x ^ n * (m.factorial • Ring.choose a m) := by
          rw [nsmul_eq_mul]
    _ = x ^ n * (descPochhammer ℤ m).smeval a := by
      rw [Ring.descPochhammer_eq_factorial_smul_choose]
    _ = (descPochhammer ℤ m).smeval (a - n • c) * x ^ n :=
      Polynomial.pow_mul_smeval_eq _ h hc n
    _ = (m.factorial • Ring.choose (a - n • c) m) * x ^ n := by
      rw [Ring.descPochhammer_eq_factorial_smul_choose]
    _ = m.factorial • (Ring.choose (a - n • c) m * x ^ n) := by
      simp only [nsmul_eq_mul, mul_assoc]

end TauCeti
