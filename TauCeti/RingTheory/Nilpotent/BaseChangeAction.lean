/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.Nilpotent.Exp
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Base change of integral nilpotent exponentials

Let `V` be an `A`-module for a `ℚ`-algebra `A`, let `M ≤ V` be an additive subgroup, and suppose
that every divided power of an element `x : A` preserves `M`. Restricting those divided powers gives
integral endomorphisms of `M`. After extension of scalars to any commutative ring `R`, the finite
sum

```text
E_R(t) = ∑ n, tⁿ (x⁽ⁿ⁾|_M)_R
```

is therefore defined without dividing by a factorial in `R`. The divided-power multiplication law
proves `E_R(t + u) = E_R(t) E_R(u)`, so `E_R(-t)` is its inverse. Consequently the additive group
of every commutative ring acts on `R ⊗[ℤ] M` by `R`-linear automorphisms.

This is the base-ring-valued form of a root subgroup action in the Chevalley--Demazure
construction, and an arbitrary-ring analogue of the earlier integer exponential from
`TauCeti/RingTheory/Nilpotent/Exp.lean`. The new content here is that the integral divided-power
operators make the same family available over every parameter ring, even when the ring has positive
characteristic.

## Main definitions and results

* `TauCeti.integralDividedPower`: a divided-power operator restricted to an invariant additive
  subgroup.
* `TauCeti.mul_integralDividedPower`: multiplication formula for restricted divided powers.
* `TauCeti.baseChangeExp`: the finite divided-power exponential on `R ⊗[ℤ] M` for an element of `A`.
* `TauCeti.map_baseChangeExp`: naturality of the exponential under a map of parameter rings.
* `TauCeti.baseChangeExp_add`: its one-parameter group law.
* `TauCeti.baseChangeExpLinearEquiv`: the resulting linear automorphism.
* `TauCeti.baseChangeExpHom`: the additive one-parameter subgroup over `R`.
* `TauCeti.integralUnitRestrict`: a unit of `A` preserving `M` restricted to an integral
  automorphism of `M`.
* `TauCeti.baseChangeExp_intCast`: at an integer parameter the exponential is the base change of a
  single integral automorphism.
* `TauCeti.baseChange_integralUnitRestrict_conj_baseChangeExp`: conjugating a one-parameter
  subgroup by such a unit gives the one-parameter subgroup of the conjugated element.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* The proof of `sum_pow_smul_mul_sum_pow_smul` adapts Mathlib's `IsNilpotent.exp_add_of_commute` in
  `Mathlib/RingTheory/Nilpotent/Exp.lean` (Janos Wolosz), replacing powers/factorials by integral
  divided powers.
-/

public section

namespace TauCeti

open Finset TensorProduct

universe u v

variable {A : Type*} [Ring A] [Algebra ℚ A]
variable {V : Type u} [AddCommGroup V] [Module A V]
variable {S : Type*} [SetLike S V] [AddSubgroupClass S V]

/-! ## Integral divided-power operators -/

/-- The restriction to `M` of the `n`-th divided power of `x`, given that this divided power maps
`M` into `M`.

This is an integral linear map: the rational division by `n!` has already taken place in the
ambient representation, while the preservation hypothesis says that its value lands back in
`M`. -/
noncomputable def integralDividedPower (x : A) (M : S)
    (n : ℕ) (hM : ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) : Module.End ℤ M where
  toFun v := ⟨Associative.dividedPower n x • (v : V), hM v v.2⟩
  map_add' a b := by
    ext
    exact smul_add _ _ _
  map_smul' t a := by
    ext
    exact smul_comm _ _ _

/-- The value of `integralDividedPower x M n hM v` coerced to `V` is
`Associative.dividedPower n x • v`. -/
@[simp]
theorem coe_integralDividedPower_apply (x : A) (M : S)
    (n : ℕ) (hM : ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (v : M) :
    ((integralDividedPower x M n hM v : M) : V) = Associative.dividedPower n x • (v : V) := by
  rfl

/-- The zeroth restricted divided power is the identity. -/
@[simp]
theorem integralDividedPower_zero (x : A) (M : S)
    (hM0 : ∀ v ∈ M, Associative.dividedPower 0 x • v ∈ M) :
    integralDividedPower x M 0 hM0 = 1 := by
  ext v
  simp

/-- Multiplication formula for restricted divided powers. -/
theorem mul_integralDividedPower (x : A) (M : S)
    (m n : ℕ) (hm : ∀ v ∈ M, Associative.dividedPower m x • v ∈ M)
    (hn : ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hmn : ∀ v ∈ M, Associative.dividedPower (m + n) x • v ∈ M) :
    integralDividedPower x M m hm * integralDividedPower x M n hn =
      Nat.choose (m + n) m • integralDividedPower x M (m + n) hmn := by
  ext v
  dsimp [integralDividedPower]
  rw [smul_smul, Associative.mul_dividedPower, smul_assoc]

/-- The restricted divided power vanishes for degrees greater than or equal to a nilpotency
bound. -/
theorem integralDividedPower_eq_zero_of_le (x : A)
    (M : S) (n : ℕ) (hn : ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    {k : ℕ} (hk : x ^ k = 0) (hkn : k ≤ n) :
    integralDividedPower x M n hn = 0 := by
  ext v
  simp [coe_integralDividedPower_apply, Associative.dividedPower_def,
    pow_eq_zero_of_le hkn hk]

/-! ## Restricting a unit to an invariant additive subgroup -/

/-- The restriction to `M` of the action of a unit of `A` that preserves `M` together with its
inverse, as an integral linear automorphism.

Scalar multiplication by a ring element is additive, and an additive map of abelian groups is
exactly a `ℤ`-linear map, so no divisibility is involved: this automorphism survives base change to
an arbitrary commutative ring. -/
noncomputable def integralUnitRestrict (u : Aˣ) (M : S)
    (hu : ∀ v ∈ M, (u : A) • v ∈ M) (hu' : ∀ v ∈ M, ((u⁻¹ : Aˣ) : A) • v ∈ M) : M ≃ₗ[ℤ] M :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun v => ⟨(u : A) • (v : V), hu v v.2⟩
      invFun := fun v => ⟨((u⁻¹ : Aˣ) : A) • (v : V), hu' v v.2⟩
      left_inv := fun v => Subtype.ext (by simp [smul_smul])
      right_inv := fun v => Subtype.ext (by simp [smul_smul])
      map_add' := fun a b => Subtype.ext (smul_add _ _ _) }

omit [Algebra ℚ A] in
@[simp]
theorem coe_integralUnitRestrict_apply (u : Aˣ) (M : S)
    (hu : ∀ v ∈ M, (u : A) • v ∈ M) (hu' : ∀ v ∈ M, ((u⁻¹ : Aˣ) : A) • v ∈ M) (v : M) :
    ((integralUnitRestrict u M hu hu' v : M) : V) = (u : A) • (v : V) :=
  (rfl)

omit [Algebra ℚ A] in
@[simp]
theorem coe_integralUnitRestrict_symm_apply (u : Aˣ) (M : S)
    (hu : ∀ v ∈ M, (u : A) • v ∈ M) (hu' : ∀ v ∈ M, ((u⁻¹ : Aˣ) : A) • v ∈ M) (v : M) :
    (((integralUnitRestrict u M hu hu').symm v : M) : V) = ((u⁻¹ : Aˣ) : A) • (v : V) :=
  (rfl)

/-- The restriction to `M` of the exponential `exp (t • x)` of an integral multiple of a nilpotent
element whose divided powers preserve `M`.

The coefficients of the divided-power expansion of `exp (t • x)` are the integers `tⁿ`, so this
automorphism is defined over `ℤ` even though the exponential itself divides by factorials. -/
noncomputable def integralExpZSMul (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x) (t : ℤ) :
    M ≃ₗ[ℤ] M :=
  integralUnitRestrict (nilpotentExpUnit (hx.smul t)) M
    (fun _ hv => by simpa using exp_zsmul_smul_mem hx hM t hv)
    (fun _ hv => by simpa [neg_zsmul] using exp_zsmul_smul_mem hx hM (-t) hv)

@[simp]
theorem coe_integralExpZSMul_apply (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x) (t : ℤ)
    (v : M) :
    ((integralExpZSMul x M hM hx t v : M) : V) = IsNilpotent.exp (t • x) • (v : V) := by
  simp [integralExpZSMul]

/-- Negating the element leaves the even restricted divided powers unchanged. -/
theorem integralDividedPower_neg_of_even (x : A) (M : S) {n : ℕ} (hn : Even n)
    (hM' : ∀ v ∈ M, Associative.dividedPower n (-x) • v ∈ M)
    (hM : ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) :
    integralDividedPower (-x) M n hM' = integralDividedPower x M n hM := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [coe_integralDividedPower_apply, coe_integralDividedPower_apply,
    Associative.dividedPower_neg, hn.neg_one_pow, one_smul]

/-- Negating the element negates the odd restricted divided powers. -/
theorem integralDividedPower_neg_of_odd (x : A) (M : S) {n : ℕ} (hn : Odd n)
    (hM' : ∀ v ∈ M, Associative.dividedPower n (-x) • v ∈ M)
    (hM : ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) :
    integralDividedPower (-x) M n hM' = -integralDividedPower x M n hM := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [coe_integralDividedPower_apply, LinearMap.neg_apply, NegMemClass.coe_neg,
    coe_integralDividedPower_apply, Associative.dividedPower_neg, hn.neg_one_pow, neg_one_smul,
    neg_smul]

/-- The integral exponential expanded over any truncation bound. -/
theorem integralExpZSMul_eq_sum (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x)
    {k : ℕ} (hk : x ^ k = 0) (t : ℤ) :
    (integralExpZSMul x M hM hx t : M →ₗ[ℤ] M) =
      ∑ n ∈ range k, t ^ n • integralDividedPower x M n (hM n) := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  have hsum : (((∑ n ∈ range k, t ^ n • integralDividedPower x M n (hM n)) v : M) : V) =
      ∑ n ∈ range k, t ^ n • (Associative.dividedPower n x • (v : V)) := by
    rw [LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun n _ => by
      rw [LinearMap.smul_apply, AddSubgroupClass.coe_zsmul, coe_integralDividedPower_apply]
  rw [hsum, LinearEquiv.coe_coe, coe_integralExpZSMul_apply,
    exp_zsmul_eq_sum_zsmul_dividedPower hk, Finset.sum_smul]
  exact Finset.sum_congr rfl fun n _ => (smul_assoc _ _ _)

/-! ## The divided-power exponential after base change -/

-- Use the module structure carried by the explicit `ℤ`-algebra. Although an algebra structure
-- over `ℤ` is unique, category objects need not store the canonical instance definitionally.
attribute [local instance high] Algebra.toModule

section ExplicitAlgebra

variable {R : Type v} [CommRing R] [Algebra ℤ R]

/-- The finite integral divided-power exponential on the scalar extension `R ⊗[ℤ] M`
for an element `x`.

Although `x` acts on a rational vector space, this definition uses only the integral operators on
`M` and therefore makes sense over an arbitrary commutative parameter ring `R`. -/
noncomputable def baseChangeExp (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (t : R) :
    Module.End R (R ⊗[ℤ] M) :=
  ∑ n ∈ range (nilpotencyClass x),
    t ^ n • (integralDividedPower x M n (hM n)).baseChange R

/-- The base-changed exponential acts on a pure tensor by the expected finite divided-power
formula. -/
@[simp]
theorem baseChangeExp_tmul (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (t r : R) (v : M) :
    baseChangeExp x M hM t (r ⊗ₜ[ℤ] v) =
      ∑ n ∈ range (nilpotencyClass x), (t ^ n * r) ⊗ₜ[ℤ]
        integralDividedPower x M n (hM n) v := by
  simp [baseChangeExp, smul_tmul']

/-- The base-changed divided-power exponential is natural under maps of parameter rings carrying
explicit `ℤ`-algebra structures. -/
theorem map_baseChangeExp_algHom {T : Type*} [CommRing T] [Algebra ℤ T] (φ : R →ₐ[ℤ] T)
    (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (t : R) :
    ∀ z : R ⊗[ℤ] M,
      TensorProduct.map φ.toLinearMap LinearMap.id (baseChangeExp x M hM t z) =
        baseChangeExp x M hM (φ t)
          (TensorProduct.map φ.toLinearMap LinearMap.id z) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
      rw [TensorProduct.map_tmul, baseChangeExp_tmul, baseChangeExp_tmul]
      simp only [map_sum, TensorProduct.map_tmul, LinearMap.id_apply,
        AlgHom.toLinearMap_apply, map_pow, map_mul]
  | add y z hy hz => simp [hy, hz]

private theorem baseChange_mul_integralDividedPower
    (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (m n : ℕ) :
    (integralDividedPower x M m (hM m)).baseChange R *
        (integralDividedPower x M n (hM n)).baseChange R =
      Nat.choose (m + n) m • (integralDividedPower x M (m + n) (hM (m + n))).baseChange R := by
  rw [← LinearMap.baseChange_mul, mul_integralDividedPower]
  exact map_nsmul (Module.End.baseChangeHom ℤ R M) _ _

private theorem baseChange_integralDividedPower_eq_zero_of_le
    (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    {k n : ℕ} (hk : x ^ k = 0) (hkn : k ≤ n) :
    (integralDividedPower x M n (hM n)).baseChange R = 0 := by
  rw [integralDividedPower_eq_zero_of_le x M n (hM n) hk hkn, LinearMap.baseChange_zero]

/-- The base-changed exponential expanded over any truncation bound `k` satisfying `x ^ k = 0`. -/
theorem baseChangeExp_of_pow_eq_zero (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) {k : ℕ} (hk : x ^ k = 0) (t : R) :
    baseChangeExp x M hM t =
      ∑ n ∈ range k, t ^ n • (integralDividedPower x M n (hM n)).baseChange R := by
  have hle : nilpotencyClass x ≤ k := Nat.sInf_le hk
  rw [baseChangeExp]
  apply sum_subset (range_mono hle)
  intro n hn hnot
  rw [mem_range] at hn hnot
  have hn_ge : nilpotencyClass x ≤ n := not_lt.1 hnot
  have hpow : x ^ nilpotencyClass x = 0 := pow_nilpotencyClass ⟨k, hk⟩
  rw [baseChange_integralDividedPower_eq_zero_of_le x M hM hpow hn_ge, smul_zero]

/-- The base-changed exponential acts on a pure tensor by the divided-power formula over any
truncation bound `k` satisfying `x ^ k = 0`. -/
theorem baseChangeExp_tmul_of_pow_eq_zero (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) {k : ℕ} (hk : x ^ k = 0)
    (t r : R) (v : M) :
    baseChangeExp x M hM t (r ⊗ₜ[ℤ] v) =
      ∑ n ∈ range k, (t ^ n * r) ⊗ₜ[ℤ] integralDividedPower x M n (hM n) v := by
  simp [baseChangeExp_of_pow_eq_zero x M hM hk, smul_tmul']

omit [Algebra ℤ R] in
/-- Binomial convolution identity for truncated divided-power series.

Adapted from Mathlib's `IsNilpotent.exp_add_of_commute` in
`Mathlib/RingTheory/Nilpotent/Exp.lean` (Janos Wolosz). -/
private theorem sum_pow_smul_mul_sum_pow_smul
    {B : Type*} [Ring B] [Algebra R B] (D : ℕ → B) (k : ℕ)
    (hzero : ∀ n, k ≤ n → D n = 0)
    (hmul : ∀ m n, D m * D n = Nat.choose (m + n) m • D (m + n))
    (t u : R) :
    (∑ n ∈ range k, t ^ n • D n) * (∑ n ∈ range k, u ^ n • D n) =
      ∑ n ∈ range k, (t + u) ^ n • D n := by
  rw [sum_mul_sum]
  simp_rw [smul_mul_smul, hmul, ← Nat.cast_smul_eq_nsmul R, smul_smul]
  rw [← sum_product']
  -- Step 1: Vanishing of high-degree terms above the nilpotency bound k.
  have hlarge : ∑ ij ∈ range k ×ˢ range k with k ≤ ij.1 + ij.2,
      (t ^ ij.1 * u ^ ij.2 * Nat.choose (ij.1 + ij.2) ij.1) • D (ij.1 + ij.2) = 0 := by
    exact sum_eq_zero fun ij hij => by
      rw [mem_filter] at hij
      rw [hzero _ hij.2, smul_zero]
  -- Step 2: Split the double sum into low-degree (< k) and high-degree (≥ k) parts.
  have hsplit := sum_filter_add_sum_filter_not (range k ×ˢ range k)
    (fun ij => k ≤ ij.1 + ij.2)
    (fun ij => (t ^ ij.1 * u ^ ij.2 * Nat.choose (ij.1 + ij.2) ij.1) •
      D (ij.1 + ij.2))
  rw [hlarge, zero_add] at hsplit
  rw [← hsplit]
  symm
  -- Step 3: Expand (t + u)^n by the binomial theorem and reindex via antidiagonals.
  calc
    ∑ n ∈ range k, (t + u) ^ n • D n =
        ∑ n ∈ range k, (∑ ij ∈ antidiagonal n,
          t ^ ij.1 * u ^ ij.2 * Nat.choose n ij.1) • D n := by
      refine sum_congr rfl fun n _ => ?_
      rw [(Commute.all t u).add_pow']
      simp only [sum_smul]
      apply sum_congr rfl
      intro ij hij
      simp only [nsmul_eq_mul]
      rw [mul_comm (Nat.choose n ij.1 : R), mul_assoc]
    _ = ∑ ij ∈ range k ×ˢ range k with ¬k ≤ ij.1 + ij.2,
        (t ^ ij.1 * u ^ ij.2 * Nat.choose (ij.1 + ij.2) ij.1) •
          D (ij.1 + ij.2) := by
      simp_rw [sum_smul]
      rw [sum_sigma']
      symm
      -- Step 4: Bijection between the disjoint antidiagonals and the filtered product range.
      apply sum_bij (fun (ij : ℕ × ℕ) _ =>
        (⟨ij.1 + ij.2, (ij.1, ij.2)⟩ : Sigma fun _ => ℕ × ℕ))
      · intro ij hij
        rw [mem_filter] at hij
        exact mem_sigma.2 ⟨mem_range.2 (Nat.lt_of_not_ge hij.2),
          mem_antidiagonal.2 rfl⟩
      · intro a ha b hb hab
        have hsnd : (a.1, a.2) = (b.1, b.2) :=
          congrArg (fun z : Sigma fun _ => ℕ × ℕ => z.2) hab
        exact Prod.ext (congrArg Prod.fst hsnd) (congrArg Prod.snd hsnd)
      · rintro ⟨n, ij⟩ hij
        rw [mem_sigma] at hij
        have hn : n < k := mem_range.1 hij.1
        have hij_sum : ij.1 + ij.2 = n := mem_antidiagonal.1 hij.2
        exact ⟨ij, by
          rw [mem_filter, mem_product]
          exact ⟨⟨mem_range.2 (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (hij_sum ▸ hn)),
            mem_range.2 (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (hij_sum ▸ hn))⟩,
            not_le.2 (hij_sum ▸ hn)⟩, by
          apply Sigma.ext hij_sum
          rfl⟩
      · intro ij _
        rfl

/-- The integral divided-power exponential satisfies the additive one-parameter group law over
every commutative base ring. -/
@[simp]
theorem baseChangeExp_add (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x)
    (t u : R) :
    baseChangeExp x M hM (t + u) = baseChangeExp x M hM t * baseChangeExp x M hM u := by
  rw [baseChangeExp, baseChangeExp, baseChangeExp]
  symm
  apply sum_pow_smul_mul_sum_pow_smul (fun n => (integralDividedPower x M n (hM n)).baseChange R)
  · intro n hn
    exact baseChange_integralDividedPower_eq_zero_of_le x M hM
      (pow_nilpotencyClass hx) hn
  · exact baseChange_mul_integralDividedPower x M hM

/-- The base-changed divided-power exponential at zero is the identity. -/
@[simp]
theorem baseChangeExp_zero (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x) :
    baseChangeExp (R := R) x M hM 0 = 1 := by
  classical
  by_cases h0 : nilpotencyClass x = 0
  · have hpow := pow_nilpotencyClass hx
    rw [h0, pow_zero] at hpow
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul r m =>
        have hm : (m : V) = 0 := by
          have h1 : (m : V) = (1 : A) • (m : V) := (one_smul A (m : V)).symm
          rw [hpow, zero_smul] at h1
          exact h1
        have hm0 : m = 0 := SetLike.coe_eq_coe.mp (by simp [hm])
        subst hm0
        simp
    | add a b ha hb => simp [ha, hb]
  · rw [baseChangeExp, sum_eq_single 0]
    · simp
    · intro n _ hn0
      simp [hn0]
    · intro hn0
      exact False.elim (h0 (by simpa using hn0))

/-- The base-changed divided-power exponential as a linear equivalence, with inverse given by the
negative parameter. -/
noncomputable def baseChangeExpLinearEquiv (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x) (t : R) :
    R ⊗[ℤ] M ≃ₗ[R] R ⊗[ℤ] M :=
  LinearEquiv.ofLinearMap (baseChangeExp x M hM t) (baseChangeExp x M hM (-t))
    (by
      have h := baseChangeExp_add x M hM hx t (-t)
      simp only [add_neg_cancel, baseChangeExp_zero x M hM hx] at h
      exact h.symm)
    (by
      have h := baseChangeExp_add x M hM hx (-t) t
      simp only [neg_add_cancel, baseChangeExp_zero x M hM hx] at h
      exact h.symm)

/-- The linear map underlying `baseChangeExpLinearEquiv` is `baseChangeExp`. -/
@[simp]
theorem baseChangeExpLinearEquiv_toLinearMap (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x) (t : R) :
    (baseChangeExpLinearEquiv x M hM hx t).toLinearMap = baseChangeExp x M hM t :=
  (rfl)

/-- Coercing `baseChangeExpLinearEquiv` to a function yields `baseChangeExp`. -/
@[simp]
theorem coe_baseChangeExpLinearEquiv (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x) (t : R) :
    ⇑(baseChangeExpLinearEquiv x M hM hx t) = ⇑(baseChangeExp x M hM t) :=
  (rfl)

/-- The inverse of `baseChangeExpLinearEquiv` is given by the negative parameter. -/
@[simp]
theorem baseChangeExpLinearEquiv_symm (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x) (t : R) :
    (baseChangeExpLinearEquiv x M hM hx t).symm = baseChangeExpLinearEquiv x M hM hx (-t) := by
  ext
  rfl

/-- The additive group of a commutative ring acts on the scalar extension of a
divided-power-stable additive subgroup by the integral nilpotent exponential. -/
noncomputable def baseChangeExpHom (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x) :
    Multiplicative R →* (R ⊗[ℤ] M ≃ₗ[R] R ⊗[ℤ] M) where
  toFun t := baseChangeExpLinearEquiv x M hM hx (Multiplicative.toAdd t)
  map_one' := by
    ext v
    simp [baseChangeExp_zero x M hM hx]
  map_mul' t u := by
    ext v
    simp [baseChangeExp_add x M hM hx]

/-- The linear map underlying the base-changed one-parameter subgroup is the corresponding
divided-power exponential. -/
theorem baseChangeExpHom_toLinearMap (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x)
    (t : Multiplicative R) :
    (baseChangeExpHom x M hM hx t).toLinearMap =
      baseChangeExp x M hM (Multiplicative.toAdd t) :=
  (rfl)

/-- Evaluating `baseChangeExpHom` at `t` yields `baseChangeExpLinearEquiv` at `toAdd t`. -/
@[simp]
theorem baseChangeExpHom_apply (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x)
    (t : Multiplicative R) :
    baseChangeExpHom x M hM hx t =
      baseChangeExpLinearEquiv x M hM hx (Multiplicative.toAdd t) :=
  (rfl)

/-- Coercing `baseChangeExpHom` to a function yields `baseChangeExp`. -/
theorem coe_baseChangeExpHom (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x)
    (t : Multiplicative R) :
    ⇑(baseChangeExpHom x M hM hx t) =
      ⇑(baseChangeExp x M hM (Multiplicative.toAdd t)) :=
  (rfl)

/-- The base-changed exponential depends only on the element, not on the stability proof. -/
theorem baseChangeExp_congr {x y : A} (hxy : x = y) (M : S)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M) (t : R) :
    baseChangeExp x M hMx t = baseChangeExp y M hMy t := by
  subst hxy
  rfl

/-- Negating the element inverts the parameter: `E_{-x}(t) = E_x(-t)`. -/
theorem baseChangeExp_neg (x : A) (M : S)
    (hM' : ∀ n, ∀ v ∈ M, Associative.dividedPower n (-x) • v ∈ M)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x) (t : R) :
    baseChangeExp (-x) M hM' t = baseChangeExp x M hM (-t) := by
  obtain ⟨k, hk⟩ := id hx
  have hk' : (-x) ^ k = 0 := by rw [neg_pow, hk, mul_zero]
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r v =>
      rw [baseChangeExp_tmul_of_pow_eq_zero (-x) M hM' hk',
        baseChangeExp_tmul_of_pow_eq_zero x M hM hk]
      refine Finset.sum_congr rfl fun n _ => ?_
      rcases Nat.even_or_odd n with hn | hn
      · rw [integralDividedPower_neg_of_even x M hn (hM' n) (hM n), hn.neg_pow]
      · rw [integralDividedPower_neg_of_odd x M hn (hM' n) (hM n), hn.neg_pow,
          LinearMap.neg_apply, TensorProduct.tmul_neg, neg_mul, TensorProduct.neg_tmul]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-! ## Conjugating the exponential by an integral unit -/

-- Moving an integer scalar across `⊗[ℤ]` by hand. The `ℤ`-module structure on `R` here is the one
-- carried by its explicit `ℤ`-algebra, so it is not the `AddCommGroup.toIntModule` structure that
-- `TensorProduct.CompatibleSMul.int` is stated for, and `TensorProduct.smul_tmul` does not apply.
private theorem intCast_mul_tmul (M : S) (z : ℤ) (r : R) (w : M) :
    (((z : R) * r) ⊗ₜ[ℤ] w : R ⊗[ℤ] M) = r ⊗ₜ[ℤ] (z • w) := by
  induction z using Int.induction_on with
  | zero =>
      rw [Int.cast_zero, zero_mul, TensorProduct.zero_tmul, zero_smul, TensorProduct.tmul_zero]
  | succ i ih =>
      rw [Int.cast_add, Int.cast_one, add_mul, one_mul, TensorProduct.add_tmul, ih,
        add_smul, one_smul, TensorProduct.tmul_add]
  | pred i ih =>
      rw [Int.cast_sub, Int.cast_one, sub_mul, one_mul, TensorProduct.sub_tmul, ih,
        sub_smul, one_smul, TensorProduct.tmul_sub]

/-- At an integer parameter the base-changed exponential is the base change of a single integral
automorphism of `M`, namely the restriction of `exp (t • x)`.

This is what makes a Chevalley group element defined over `ℤ`: its value at an integral parameter
does not depend on the ring the points are taken in. -/
theorem baseChangeExp_intCast (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (hx : IsNilpotent x) (t : ℤ) :
    baseChangeExp x M hM ((t : R)) =
      ((integralExpZSMul x M hM hx t : M →ₗ[ℤ] M).baseChange R) := by
  obtain ⟨k, hk⟩ := id hx
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r v =>
      have hE : ((integralExpZSMul x M hM hx t : M →ₗ[ℤ] M) v : M) =
          ∑ n ∈ range k, t ^ n • integralDividedPower x M n (hM n) v := by
        rw [integralExpZSMul_eq_sum x M hM hx hk t, LinearMap.sum_apply]
        exact Finset.sum_congr rfl fun n _ => LinearMap.smul_apply _ _ _
      rw [baseChangeExp_tmul_of_pow_eq_zero x M hM hk, LinearMap.baseChange_tmul, hE,
        TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Int.cast_pow, intCast_mul_tmul]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- **Conjugating a base-changed exponential by an integral unit.** If a unit `u` of `A` preserves
`M` together with its inverse, then conjugating the one-parameter subgroup of `x` by the induced
automorphism of `R ⊗[ℤ] M` gives the one-parameter subgroup of the conjugate `u x u⁻¹`.

For the Weyl element `n_α` and a root vector `eα` this is Chevalley's relation
`n_α x_α(t) n_α⁻¹ = x_{-α}(-t)`, obtained from the Lie-algebra identity `n_α eα n_α⁻¹ = -e_{-α}`
alone: conjugation is an algebra automorphism, so it passes through the divided powers. -/
theorem baseChange_integralUnitRestrict_conj_baseChangeExp (x : A) (M : S) (u : Aˣ)
    (hu : ∀ v ∈ M, (u : A) • v ∈ M) (hu' : ∀ v ∈ M, ((u⁻¹ : Aˣ) : A) • v ∈ M)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hM' : ∀ n, ∀ v ∈ M, Associative.dividedPower n ((u : A) * x * ↑u⁻¹) • v ∈ M)
    (hx : IsNilpotent x) (t : R) :
    ((integralUnitRestrict u M hu hu' : M →ₗ[ℤ] M).baseChange R) * baseChangeExp x M hM t *
        (((integralUnitRestrict u M hu hu').symm : M →ₗ[ℤ] M).baseChange R) =
      baseChangeExp ((u : A) * x * ↑u⁻¹) M hM' t := by
  obtain ⟨k, hk⟩ := id hx
  have hk' : ((u : A) * x * ↑u⁻¹) ^ k = 0 := by rw [Units.conj_pow, hk, mul_zero, zero_mul]
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r v =>
      rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.baseChange_tmul,
        baseChangeExp_tmul_of_pow_eq_zero x M hM hk,
        baseChangeExp_tmul_of_pow_eq_zero ((u : A) * x * ↑u⁻¹) M hM' hk', map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [LinearMap.baseChange_tmul]
      refine congrArg _ (Subtype.ext ?_)
      simp only [LinearEquiv.coe_coe, coe_integralUnitRestrict_apply,
        coe_integralDividedPower_apply, coe_integralUnitRestrict_symm_apply,
        Associative.dividedPower_units_conj, mul_smul]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

end ExplicitAlgebra

variable {R : Type v} [CommRing R]

/-- The base-changed divided-power exponential is natural under every map of parameter rings. -/
theorem map_baseChangeExp {T : Type*} [CommRing T] (φ : R →+* T) (x : A) (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) (t : R) :
    ∀ z : R ⊗[ℤ] M,
      TensorProduct.map φ.toIntAlgHom.toLinearMap LinearMap.id (baseChangeExp x M hM t z) =
        baseChangeExp x M hM (φ t)
          (TensorProduct.map φ.toIntAlgHom.toLinearMap LinearMap.id z) := by
  exact map_baseChangeExp_algHom φ.toIntAlgHom x M hM t

end TauCeti
