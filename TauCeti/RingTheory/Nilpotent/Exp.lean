/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RingTheory.DividedPowers.Associative
public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# The integral exponential of a nilpotent element

Let `A` be an associative `ℚ`-algebra and `x : A` a nilpotent element. Mathlib's
`IsNilpotent.exp x` is the finite sum `∑ i, xⁱ / i!`. This file rewrites that sum in terms of the
divided powers `x⁽ⁱ⁾ = xⁱ / i!` of `TauCeti/RingTheory/DividedPowers/Associative.lean`, so that

```text
exp (t • x) = ∑ i, tⁱ • x⁽ⁱ⁾
```

has *integer* coefficients when `t` is an integer. Consequently `exp (t • x)` lies in any subring
containing the divided powers of `x`, and `t ↦ exp (t • x)` is a homomorphism from the additive
group of integers to the units of that subring.

This is the shape of a **root subgroup map** `x_α : 𝔾ₐ → G` of a Chevalley--Demazure group scheme:
the divided powers of a Chevalley root vector generate the Kostant `ℤ`-form, so the exponentials
above are exactly the elements that preserve an integral lattice. The application to the Kostant
form is in `TauCeti/Algebra/Lie/UniversalEnveloping/Exponential.lean`.

The second half of the file identifies conjugation by `exp a` with the exponential of the inner
derivation `ad a`:

```text
exp (ad a) b = exp a * b * exp (-a).
```

Mathlib already knows that the exponential of a nilpotent derivation is a Lie algebra automorphism
(`LieDerivation.exp`); what is added here is that for an *inner* derivation that automorphism is an
explicit conjugation. This is the identity that rewrites a conjugate of a root subgroup element as
another exponential, so it is the algebraic source of the Chevalley commutator relations.

## Main results

* `TauCeti.exp_eq_sum_dividedPower`: `exp x` is the sum of the divided powers of `x`.
* `TauCeti.exp_smul_eq_sum_smul_dividedPower`: the rescaled expansion `exp (r • x) = ∑ rⁱ • x⁽ⁱ⁾`.
* `TauCeti.exp_zsmul_eq_sum_zsmul_dividedPower`: the same expansion with integer coefficients.
* `TauCeti.exp_zsmul_mem`: `exp (t • x)` lies in a subring holding the divided powers of `x`.
* `TauCeti.expSMulHom`: the one-parameter group of units `t ↦ exp (t • x)`.
* `TauCeti.exp_mulLeft_sub_mulRight_apply`: conjugation by `exp a` is the exponential of the
  commutator endomorphism, and `TauCeti.exp_ad_apply` restates it for `LieAlgebra.ad`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* R. W. Carter, *Simple Groups of Lie Type*, §4.
-/

public section

namespace TauCeti

open Finset IsNilpotent

attribute [local instance 100] LieRing.ofAssociativeRing

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-! ## The divided-power expansion -/

/-- The exponential of a nilpotent element is the sum of its divided powers. -/
theorem exp_eq_sum_dividedPower {x : A} {k : ℕ} (hk : x ^ k = 0) :
    exp x = ∑ i ∈ range k, Associative.dividedPower i x := by
  rw [exp_eq_sum hk]
  exact sum_congr rfl fun i _ => (Associative.dividedPower_def i x).symm

/-- The exponential of a rational multiple of a nilpotent element, expanded in divided powers.

The divided powers themselves do not depend on the scalar: rescaling `x` only rescales the
coefficients. -/
theorem exp_smul_eq_sum_smul_dividedPower {x : A} {k : ℕ} (hk : x ^ k = 0) (r : ℚ) :
    exp (r • x) = ∑ i ∈ range k, r ^ i • Associative.dividedPower i x := by
  have hk' : (r • x) ^ k = 0 := by rw [smul_pow, hk, smul_zero]
  rw [exp_eq_sum_dividedPower hk']
  exact sum_congr rfl fun i _ => Associative.dividedPower_smul r i x

/-- The exponential of an integer multiple of a nilpotent element has integer coefficients on the
divided powers. This is the integrality that lets a root subgroup map be defined over `ℤ`. -/
theorem exp_zsmul_eq_sum_zsmul_dividedPower {x : A} {k : ℕ} (hk : x ^ k = 0) (t : ℤ) :
    exp ((t : ℚ) • x) = ∑ i ∈ range k, t ^ i • Associative.dividedPower i x := by
  rw [exp_smul_eq_sum_smul_dividedPower hk]
  refine sum_congr rfl fun i _ => ?_
  rw [← Int.cast_pow, Int.cast_smul_eq_zsmul]

/-- A subring containing every divided power of a nilpotent element contains every integral
exponential of it. -/
theorem exp_zsmul_mem {x : A} (hx : IsNilpotent x) {S : Subring A}
    (hS : ∀ i, Associative.dividedPower i x ∈ S) (t : ℤ) :
    exp ((t : ℚ) • x) ∈ S := by
  obtain ⟨k, hk⟩ := hx
  rw [exp_zsmul_eq_sum_zsmul_dividedPower hk]
  exact sum_mem fun i _ => zsmul_mem (hS i) _

/-! ## The one-parameter group of units -/

/-- Exponentiation turns addition of scalars into multiplication. -/
theorem exp_add_smul {x : A} (hx : IsNilpotent x) (r s : ℚ) :
    exp ((r + s) • x) = exp (r • x) * exp (s • x) := by
  rw [add_smul]
  exact exp_add_of_commute (((Commute.refl x).smul_left r).smul_right s) (hx.smul r) (hx.smul s)

/-- The exponential of the negated scalar multiple is a right inverse. -/
theorem exp_smul_mul_exp_neg_smul {x : A} (hx : IsNilpotent x) (r : ℚ) :
    exp (r • x) * exp (-r • x) = 1 := by
  rw [neg_smul]
  exact exp_mul_exp_neg_self (hx.smul r)

/-- The exponential of the negated scalar multiple is a left inverse. -/
theorem exp_neg_smul_mul_exp_smul {x : A} (hx : IsNilpotent x) (r : ℚ) :
    exp (-r • x) * exp (r • x) = 1 := by
  rw [neg_smul]
  exact exp_neg_mul_exp_self (hx.smul r)

/-- The one-parameter group of units `t ↦ exp (t • x)` attached to a nilpotent element `x`.

For a Chevalley root vector this is the root subgroup map `x_α` evaluated on the integral points of
the additive group. -/
@[expose]
noncomputable def expSMulHom {x : A} (hx : IsNilpotent x) : Multiplicative ℤ →* Aˣ where
  toFun t :=
    { val := exp ((((Multiplicative.toAdd t : ℤ) : ℚ)) • x)
      inv := exp ((-((Multiplicative.toAdd t : ℤ) : ℚ)) • x)
      val_inv := exp_smul_mul_exp_neg_smul hx _
      inv_val := exp_neg_smul_mul_exp_smul hx _ }
  map_one' := by
    ext
    simp
  map_mul' t u := by
    ext
    have h : ((Multiplicative.toAdd (t * u) : ℤ) : ℚ) =
        ((Multiplicative.toAdd t : ℤ) : ℚ) + ((Multiplicative.toAdd u : ℤ) : ℚ) := by
      rw [_root_.toAdd_mul, Int.cast_add]
    simpa [h] using exp_add_smul hx ((Multiplicative.toAdd t : ℤ) : ℚ)
      ((Multiplicative.toAdd u : ℤ) : ℚ)

@[simp]
theorem coe_expSMulHom {x : A} (hx : IsNilpotent x) (t : Multiplicative ℤ) :
    ((expSMulHom hx t : Aˣ) : A) = exp ((((Multiplicative.toAdd t : ℤ) : ℚ)) • x) :=
  rfl

/-- Conjugating by an integral exponential stays inside any subring holding the divided powers. -/
theorem exp_zsmul_conj_mem {x : A} (hx : IsNilpotent x) {S : Subring A}
    (hS : ∀ i, Associative.dividedPower i x ∈ S) (t : ℤ) {b : A} (hb : b ∈ S) :
    exp ((t : ℚ) • x) * b * exp (((-t : ℤ) : ℚ) • x) ∈ S :=
  mul_mem (mul_mem (exp_zsmul_mem hx hS t) hb) (exp_zsmul_mem hx hS (-t))

/-! ## Conjugation and the adjoint action -/

/-- Left multiplication by a nilpotent element is a nilpotent endomorphism. -/
theorem isNilpotent_mulLeft {a : A} (ha : IsNilpotent a) :
    IsNilpotent (LinearMap.mulLeft ℚ a) := by
  obtain ⟨k, hk⟩ := ha
  exact ⟨k, by simp [LinearMap.pow_mulLeft, hk]⟩

/-- Right multiplication by a nilpotent element is a nilpotent endomorphism. -/
theorem isNilpotent_mulRight {a : A} (ha : IsNilpotent a) :
    IsNilpotent (LinearMap.mulRight ℚ a) := by
  obtain ⟨k, hk⟩ := ha
  exact ⟨k, by simp [LinearMap.pow_mulRight, hk]⟩

/-- The exponential of left multiplication by a nilpotent element is left multiplication by its
exponential. -/
theorem exp_mulLeft {a : A} (ha : IsNilpotent a) :
    exp (LinearMap.mulLeft ℚ a) = LinearMap.mulLeft ℚ (exp a) := by
  obtain ⟨k, hk⟩ := ha
  have h : (LinearMap.mulLeft ℚ a) ^ k = 0 := by simp [LinearMap.pow_mulLeft, hk]
  ext b
  rw [exp_eq_sum h, exp_eq_sum hk]
  simp [LinearMap.pow_mulLeft, sum_mul]

/-- The exponential of right multiplication by a nilpotent element is right multiplication by its
exponential. -/
theorem exp_mulRight {a : A} (ha : IsNilpotent a) :
    exp (LinearMap.mulRight ℚ a) = LinearMap.mulRight ℚ (exp a) := by
  obtain ⟨k, hk⟩ := ha
  have h : (LinearMap.mulRight ℚ a) ^ k = 0 := by simp [LinearMap.pow_mulRight, hk]
  ext b
  rw [exp_eq_sum h, exp_eq_sum hk]
  simp [LinearMap.pow_mulRight, mul_sum]

/-- The commutator endomorphism attached to a nilpotent element is nilpotent. -/
theorem isNilpotent_mulLeft_sub_mulRight {a : A} (ha : IsNilpotent a) :
    IsNilpotent (LinearMap.mulLeft ℚ a - LinearMap.mulRight ℚ a) :=
  (LinearMap.commute_mulLeft_right (R := ℚ) a a).isNilpotent_sub
    (isNilpotent_mulLeft ha) (isNilpotent_mulRight ha)

/-- **Conjugation is the exponential of the commutator endomorphism.** For a nilpotent `a`, the
exponential of `b ↦ a * b - b * a` is conjugation by the unit `exp a`.

This is the identity behind the Chevalley commutator relations: a conjugate of a root subgroup
element is again an exponential, of an explicitly computable element. -/
theorem exp_mulLeft_sub_mulRight_apply {a : A} (ha : IsNilpotent a) (b : A) :
    exp (LinearMap.mulLeft ℚ a - LinearMap.mulRight ℚ a) b = exp a * b * exp (-a) := by
  have hneg : LinearMap.mulRight ℚ (-a) = -LinearMap.mulRight ℚ a := by
    ext c
    simp
  have hcomm : Commute (LinearMap.mulLeft ℚ a) (LinearMap.mulRight ℚ (-a)) :=
    LinearMap.commute_mulLeft_right (R := ℚ) a (-a)
  rw [sub_eq_add_neg, ← hneg,
    exp_add_of_commute hcomm (isNilpotent_mulLeft ha) (isNilpotent_mulRight ha.neg),
    exp_mulLeft ha, exp_mulRight ha.neg]
  simp [mul_assoc]

/-- The inner derivation attached to an element, as the difference of left and right
multiplication. -/
theorem ad_eq_mulLeft_sub_mulRight (a : A) :
    LieAlgebra.ad ℚ A a = LinearMap.mulLeft ℚ a - LinearMap.mulRight ℚ a :=
  congrFun (LieAlgebra.ad_eq_lmul_left_sub_lmul_right (R := ℚ) A) a

/-- The inner derivation attached to a nilpotent element is nilpotent. -/
theorem isNilpotent_ad {a : A} (ha : IsNilpotent a) : IsNilpotent (LieAlgebra.ad ℚ A a) := by
  rw [ad_eq_mulLeft_sub_mulRight]
  exact isNilpotent_mulLeft_sub_mulRight ha

/-- **Conjugation is the exponential of the adjoint action.** For a nilpotent `a`, the automorphism
`exp (ad a)` of the Lie algebra underlying `A` is conjugation by the unit `exp a`. -/
theorem exp_ad_apply {a : A} (ha : IsNilpotent a) (b : A) :
    exp (LieAlgebra.ad ℚ A a) b = exp a * b * exp (-a) := by
  rw [ad_eq_mulLeft_sub_mulRight]
  exact exp_mulLeft_sub_mulRight_apply ha b

/-- Moving an exponential of a nilpotent element past a ring element rewrites it through the
adjoint action. -/
theorem exp_mul_eq_exp_ad_mul {a : A} (ha : IsNilpotent a) (b : A) :
    exp a * b = exp (LieAlgebra.ad ℚ A a) b * exp a := by
  rw [exp_ad_apply ha, mul_assoc, exp_neg_mul_exp_self ha, mul_one]

end TauCeti
