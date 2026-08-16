/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.DividedPowers.Associative
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
