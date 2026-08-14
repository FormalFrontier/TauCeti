/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RingTheory.DividedPowers.Associative
public import Mathlib.RingTheory.Nilpotent.Exp

/-!
# The integral exponential of a nilpotent element

Let `A` be an associative `ℚ`-algebra and `x : A` a nilpotent element. Mathlib's
`IsNilpotent.exp x` is the finite sum `∑ i, xⁱ / i!`. This file rewrites that sum in terms of the
divided powers `x⁽ⁱ⁾ = xⁱ / i!` of `TauCeti/RingTheory/DividedPowers/Associative.lean`, so that

```text
exp (t • x) = ∑ i, tⁱ • x⁽ⁱ⁾
```

has *integer* coefficients when `t` is an integer. Consequently `exp (t • x)` lies in any
additive subgroup containing the divided powers of `x`, and it preserves any additive subgroup of a
module that the divided powers of `x` preserve. The map `t ↦ exp (t • x)` is a homomorphism from the
additive group of integers to `Aˣ`, whose values lie in such an additive subgroup.

This is the shape of a **root subgroup map** `x_α : 𝔾ₐ → G` of a Chevalley--Demazure group scheme:
the divided powers of Chevalley root vectors are among the generators of the Kostant `ℤ`-form, so
the exponentials above preserve an integral lattice. The application to the Kostant form is in
`TauCeti/Algebra/Lie/UniversalEnveloping/Kostant/Exponential.lean`.

## Main results

* `TauCeti.exp_smul_eq_sum_smul_dividedPower`: the rescaled expansion `exp (r • x) = ∑ rⁱ • x⁽ⁱ⁾`.
* `TauCeti.exp_zsmul_eq_sum_zsmul_dividedPower`: the same expansion with integer coefficients.
* `TauCeti.exp_zsmul_mem`: `exp (t • x)` lies in an additive subgroup holding the divided powers
  of `x`.
* `TauCeti.exp_zsmul_smul_mem`: `exp (t • x)` preserves an additive subgroup that the divided
  powers of `x` preserve.
* `TauCeti.expZSMulHom`: the integer-parameter group of units `t ↦ exp (t • x)`.
* `TauCeti.expZSMulAddAut`: the induced action by additive automorphisms on an additive subgroup
  preserved by the divided powers of `x`.

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
theorem exp_zsmul_mem {x : A} (hx : IsNilpotent x) {S : Type*} [SetLike S A]
    [AddSubgroupClass S A] {T : S} (hT : ∀ i, Associative.dividedPower i x ∈ T) (t : ℤ) :
    exp (t • x) ∈ T := by
  obtain ⟨k, hk⟩ := hx
  rw [exp_zsmul_eq_sum_zsmul_dividedPower hk]
  exact sum_mem fun i _ => zsmul_mem (hT i) _

section Modules

variable {V : Type*} [AddCommGroup V] [Module A V]

/-- An additive subgroup of a module that is stable under the action of every divided power of a
nilpotent element is stable under the action of every integral exponential of it.

For the divided powers of a Chevalley root vector this says that a root subgroup element preserves
an admissible lattice. -/
theorem exp_zsmul_smul_mem {x : A} (hx : IsNilpotent x) {S : Type*} [SetLike S V]
    [AddSubgroupClass S V] {M : S}
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (t : ℤ)
    {v : V} (hv : v ∈ M) : exp (t • x) • v ∈ M := by
  obtain ⟨k, hk⟩ := hx
  rw [exp_zsmul_eq_sum_zsmul_dividedPower hk, Finset.sum_smul]
  exact sum_mem fun n _ => by
    rw [← Int.cast_smul_eq_zsmul A, smul_assoc, Int.cast_smul_eq_zsmul]
    exact zsmul_mem (hM n v hv) _

end Modules

/-! ## The one-parameter group of units -/

/-- The one-parameter group of units `t ↦ exp (t • x)` attached to a nilpotent element `x`.

For a Chevalley root vector this is the root subgroup map `x_α` evaluated on the integral points of
the additive group. -/
noncomputable def expZSMulHom {x : A} (hx : IsNilpotent x) : Multiplicative ℤ →* Aˣ where
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

/-- Coercing the integer-parameter-group value `expZSMulHom hx t` to `A` yields
`exp (Multiplicative.toAdd t • x)`. -/
@[simp]
theorem coe_expZSMulHom {x : A} (hx : IsNilpotent x) (t : Multiplicative ℤ) :
    ((expZSMulHom hx t : Aˣ) : A) = exp ((Multiplicative.toAdd t : ℤ) • x) :=
  -- The parentheses opt out of the exported-theorem exposure check, so that `expZSMulHom` can stay
  -- sealed and this `@[simp]` lemma remain its public characterization.
  (rfl)

/-! ## The action on an invariant additive subgroup -/

variable {V : Type*} [AddCommGroup V] [Module A V]

/-- The additive automorphism induced on a subgroup preserved by every divided power of a
nilpotent element.

The inverse is the action of the inverse unit, equivalently the exponential with the negated
integer parameter. The preservation hypothesis is deliberately stated only for the divided powers
of `x`; `exp_zsmul_smul_mem` supplies preservation by every integral exponential. -/
noncomputable def expZSMulAddEquiv {x : A} (hx : IsNilpotent x) (M : AddSubgroup V)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (t : Multiplicative ℤ) : M ≃+ M where
  toFun v := ⟨(expZSMulHom hx t : Aˣ) • (v : V), by
    simpa only [Units.smul_def, coe_expZSMulHom] using
      exp_zsmul_smul_mem hx hM (Multiplicative.toAdd t) v.2⟩
  invFun v := ⟨(expZSMulHom hx t)⁻¹ • (v : V), by
    simpa only [← map_inv, Units.smul_def, coe_expZSMulHom] using
      exp_zsmul_smul_mem hx hM (Multiplicative.toAdd t⁻¹) v.2⟩
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    simp
  map_add' v w := by
    apply Subtype.ext
    exact smul_add _ _ _

/-- The automorphism `expZSMulAddEquiv hx M hM t` acts by the unit `expZSMulHom hx t` on the
ambient module. -/
@[simp]
theorem coe_expZSMulAddEquiv {x : A} (hx : IsNilpotent x) (M : AddSubgroup V)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (t : Multiplicative ℤ) (v : M) :
    (expZSMulAddEquiv hx M hM t v : V) = (expZSMulHom hx t : Aˣ) • (v : V) :=
  (rfl)

/-- Integral exponentials act on a divided-power-stable additive subgroup by additive
automorphisms. This is the restriction of `expZSMulHom hx` from units of the ambient algebra to
automorphisms of the invariant subgroup. -/
noncomputable def expZSMulAddAut {x : A} (hx : IsNilpotent x) (M : AddSubgroup V)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) :
    Multiplicative ℤ →* Multiplicative (AddAut M) where
  toFun t := Multiplicative.ofAdd (expZSMulAddEquiv hx M hM t)
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext v
    simp
  map_mul' t u := by
    apply Multiplicative.toAdd.injective
    ext v
    simp [mul_smul]

/-- Evaluating `expZSMulAddAut` recovers the corresponding restricted additive equivalence. -/
@[simp]
theorem expZSMulAddAut_apply {x : A} (hx : IsNilpotent x) (M : AddSubgroup V)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (t : Multiplicative ℤ) :
    Multiplicative.toAdd (expZSMulAddAut hx M hM t) = expZSMulAddEquiv hx M hM t :=
  (rfl)

end TauCeti
