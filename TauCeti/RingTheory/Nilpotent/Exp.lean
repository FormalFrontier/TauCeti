/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RingTheory.DividedPowers.Associative
public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# The integral exponential of a nilpotent element

Let `A` be an associative `ℚ`-algebra and `x : A` a nilpotent element. Mathlib's
`IsNilpotent.exp x` is the finite sum `∑ i, xⁱ / i!`. This file rewrites that sum in terms of the
divided powers `x⁽ⁱ⁾ = xⁱ / i!` of `TauCeti/RingTheory/DividedPowers/Associative.lean`, so that

```text
exp (t • x) = ∑ i, tⁱ • x⁽ⁱ⁾
```

has *integer* coefficients when `t` is an integer. Consequently `exp (t • x)` lies in any
additive subgroup containing the divided powers of `x`, and it fixes any additive subgroup of a
module that the divided powers of `x` fix. The map `t ↦ exp (t • x)` is a homomorphism from the
additive group of integers to `Aˣ`, whose values lie in such an additive subgroup.

This is the shape of a **root subgroup map** `x_α : 𝔾ₐ → G` of a Chevalley--Demazure group scheme:
the divided powers of a Chevalley root vector generate the Kostant `ℤ`-form, so the exponentials
above preserve an integral lattice. The application to the Kostant form is in
`TauCeti/Algebra/Lie/UniversalEnveloping/Kostant/Exponential.lean`.

The second half of the file identifies conjugation by `exp a` with the exponential of the
commutator endomorphism `b ↦ a * b - b * a`:

```text
exp (mulLeft a - mulRight a) b = exp a * b * exp (-a).
```

Mathlib already knows that the exponential of a nilpotent derivation is a Lie algebra automorphism
(`LieDerivation.exp`); what is added here is that for an *inner* derivation that automorphism is an
explicit conjugation. This is the identity that rewrites a conjugate of a root subgroup element as
another exponential, so it is the algebraic source of the Chevalley commutator relations.

## Main results

* `TauCeti.exp_smul_eq_sum_smul_dividedPower`: the rescaled expansion `exp (r • x) = ∑ rⁱ • x⁽ⁱ⁾`.
* `TauCeti.exp_zsmul_eq_sum_zsmul_dividedPower`: the same expansion with integer coefficients.
* `TauCeti.exp_zsmul_mem`: `exp (t • x)` lies in an additive subgroup holding the divided powers
  of `x`.
* `TauCeti.exp_zsmul_apply_mem`: `exp (t • x)` fixes an additive subgroup that the divided powers
  of `x` fix.
* `TauCeti.expSMulHom`: the one-parameter group of units `t ↦ exp (t • x)`.
* `TauCeti.exp_mulLeft_sub_mulRight_apply`: conjugation by `exp a` is the exponential of the
  commutator endomorphism.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* R. W. Carter, *Simple Groups of Lie Type*, §4.
-/

public section

namespace TauCeti

open Finset IsNilpotent

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-! ## The divided-power expansion -/

/-- The exponential of a rational multiple of a nilpotent element, expanded in divided powers.

The divided powers themselves do not depend on the scalar: rescaling `x` only rescales the
coefficients. -/
theorem exp_smul_eq_sum_smul_dividedPower {x : A} {k : ℕ} (hk : x ^ k = 0) (r : ℚ) :
    exp (r • x) = ∑ i ∈ range k, r ^ i • Associative.dividedPower i x := by
  have hk' : (r • x) ^ k = 0 := by rw [smul_pow, hk, smul_zero]
  rw [exp_eq_sum hk']
  exact sum_congr rfl fun i _ =>
    (Associative.dividedPower_def i (r • x)).symm.trans
      (Associative.dividedPower_smul r i x)

/-- The exponential of an integer multiple of a nilpotent element has integer coefficients on the
divided powers. This is the integrality that lets a root subgroup map be defined over `ℤ`. -/
theorem exp_zsmul_eq_sum_zsmul_dividedPower {x : A} {k : ℕ} (hk : x ^ k = 0) (t : ℤ) :
    exp (t • x) = ∑ i ∈ range k, t ^ i • Associative.dividedPower i x := by
  rw [← Int.cast_smul_eq_zsmul ℚ t x, exp_smul_eq_sum_smul_dividedPower hk]
  refine sum_congr rfl fun i _ => ?_
  rw [← Int.cast_pow, Int.cast_smul_eq_zsmul]

/-- An additive subgroup containing every divided power of a nilpotent element contains every
integral exponential of it. -/
theorem exp_zsmul_mem {x : A} (hx : IsNilpotent x) {S : AddSubgroup A}
    (hS : ∀ i, Associative.dividedPower i x ∈ S) (t : ℤ) :
    exp (t • x) ∈ S := by
  obtain ⟨k, hk⟩ := hx
  rw [exp_zsmul_eq_sum_zsmul_dividedPower hk]
  exact sum_mem fun i _ => zsmul_mem (hS i) _

section Endomorphisms

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- An additive subgroup of a module that is stable under every divided power of a nilpotent
endomorphism is stable under every integral exponential of it.

For the divided powers of a Chevalley root vector this says that a root subgroup element preserves
an admissible lattice. -/
theorem exp_zsmul_apply_mem {x : Module.End ℚ V} (hx : IsNilpotent x) {M : AddSubgroup V}
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x v ∈ M) (t : ℤ) {v : V} (hv : v ∈ M) :
    exp (t • x) v ∈ M := by
  obtain ⟨k, hk⟩ := hx
  rw [exp_zsmul_eq_sum_zsmul_dividedPower hk]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  exact sum_mem fun n _ => zsmul_mem (hM n v hv) _

end Endomorphisms

/-! ## The one-parameter group of units -/

/-- The one-parameter group of units `t ↦ exp (t • x)` attached to a nilpotent element `x`.

For a Chevalley root vector this is the root subgroup map `x_α` evaluated on the integral points of
the additive group. -/
noncomputable def expSMulHom {x : A} (hx : IsNilpotent x) : Multiplicative ℤ →* Aˣ where
  toFun t :=
    { val := exp ((Multiplicative.toAdd t : ℤ) • x)
      inv := exp (-((Multiplicative.toAdd t : ℤ) • x))
      val_inv := exp_mul_exp_neg_self (hx.smul _)
      inv_val := exp_neg_mul_exp_self (hx.smul _) }
  map_one' := by
    ext
    simp
  map_mul' t u := by
    ext
    simpa [_root_.toAdd_mul, add_zsmul, add_mul] using exp_add_of_commute
      (((Commute.refl x).smul_left (Multiplicative.toAdd t : ℤ)).smul_right
        (Multiplicative.toAdd u : ℤ)) (hx.smul _) (hx.smul _)

/-- Coercing the one-parameter-group value `expSMulHom hx t` to `A` yields
`exp (Multiplicative.toAdd t • x)`. -/
@[simp]
theorem coe_expSMulHom {x : A} (hx : IsNilpotent x) (t : Multiplicative ℤ) :
    ((expSMulHom hx t : Aˣ) : A) = exp ((Multiplicative.toAdd t : ℤ) • x) :=
  -- The parentheses opt out of the exported-theorem exposure check, so that `expSMulHom` can stay
  -- sealed and this `@[simp]` lemma remain its public characterization.
  (rfl)

/-! ## Conjugation and the commutator endomorphism -/

/-- The exponential of left multiplication by a nilpotent element is left multiplication by its
exponential. -/
@[simp]
theorem exp_mulLeft {a : A} (ha : IsNilpotent a) :
    exp (LinearMap.mulLeft ℚ a) = LinearMap.mulLeft ℚ (exp a) := by
  have hlmul : ∀ c : A, Algebra.lmul ℚ A c = LinearMap.mulLeft ℚ c := fun c => by
    ext d
    simp
  rw [← hlmul a, ← hlmul (exp a), map_exp ha (Algebra.lmul ℚ A)]

/-- The exponential of right multiplication by a nilpotent element is right multiplication by its
exponential. -/
@[simp]
theorem exp_mulRight {a : A} (ha : IsNilpotent a) :
    exp (LinearMap.mulRight ℚ a) = LinearMap.mulRight ℚ (exp a) := by
  obtain ⟨k, hk⟩ := ha
  have h : (LinearMap.mulRight ℚ a) ^ k = 0 := by simp [LinearMap.pow_mulRight, hk]
  ext b
  rw [exp_eq_sum h, exp_eq_sum hk]
  simp [LinearMap.pow_mulRight, mul_sum]

/-- **Conjugation is the exponential of the commutator endomorphism.** For a nilpotent `a`, the
exponential of `b ↦ a * b - b * a` is conjugation by the unit `exp a`.

This is the identity behind the Chevalley commutator relations: a conjugate of a root subgroup
element is again an exponential, of an explicitly computable element. -/
@[simp]
theorem exp_mulLeft_sub_mulRight_apply {a : A} (ha : IsNilpotent a) (b : A) :
    exp (LinearMap.mulLeft ℚ a - LinearMap.mulRight ℚ a) b = exp a * b * exp (-a) := by
  have hneg : LinearMap.mulRight ℚ (-a) = -LinearMap.mulRight ℚ a :=
    (LinearMap.mul ℚ A).flip.map_neg a
  have hcomm : Commute (LinearMap.mulLeft ℚ a) (LinearMap.mulRight ℚ (-a)) :=
    LinearMap.commute_mulLeft_right (R := ℚ) a (-a)
  rw [sub_eq_add_neg, ← hneg,
    exp_add_of_commute hcomm ((LinearMap.isNilpotent_mulLeft_iff ℚ a).mpr ha)
      ((LinearMap.isNilpotent_mulRight_iff ℚ (-a)).mpr ha.neg),
    exp_mulLeft ha, exp_mulRight ha.neg]
  simp [mul_assoc]

end TauCeti
