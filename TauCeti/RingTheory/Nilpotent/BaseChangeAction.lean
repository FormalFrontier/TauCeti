/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.DividedPowers.Associative
public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Base change of integral nilpotent exponentials

Let `V` be a rational representation, let `M ≤ V` be an additive subgroup, and suppose that every
divided power of a nilpotent endomorphism `x` preserves `M`. Restricting those divided powers gives
integral endomorphisms of `M`. After extension of scalars to any commutative ring `R`, the finite
sum

```text
E_R(t) = ∑ n, tⁿ (x⁽ⁿ⁾|_M)_R
```

is therefore defined without dividing by a factorial in `R`. The divided-power multiplication law
proves `E_R(t + u) = E_R(t) E_R(u)`, so `E_R(-t)` is its inverse. Consequently the additive group
of every commutative ring acts on `R ⊗[ℤ] M` by `R`-linear automorphisms.

This is the base-ring-valued form of a root subgroup action in the Chevalley--Demazure
construction. The integer specialization is the nilpotent exponential from
`TauCeti/RingTheory/Nilpotent/Exp.lean`; the new content here is that the integral divided-power
operators make the same family available over every parameter ring, even when the ring has positive
characteristic.

## Main definitions and results

* `TauCeti.integralDividedPower`: a divided-power operator restricted to an invariant additive
  subgroup.
* `TauCeti.integralDividedPower_mul`: multiplication formula for restricted divided powers.
* `TauCeti.baseChangeExp`: the finite divided-power exponential on `R ⊗[ℤ] M` for a nilpotent
  endomorphism.
* `TauCeti.baseChangeExp_add`: its one-parameter group law.
* `TauCeti.baseChangeExpLinearEquiv`: the resulting linear automorphism.
* `TauCeti.baseChangeExpHom`: the additive one-parameter subgroup over `R`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
-/

public section

namespace TauCeti

open Finset IsNilpotent TensorProduct

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-! ## Integral divided-power operators -/

/-- The restriction to `M` of the `n`-th divided power of an endomorphism preserving `M`.

This is an integral linear map: the rational division by `n!` has already taken place in the
ambient representation, while the preservation hypothesis says that its value lands back in
`M`. -/
noncomputable def integralDividedPower (x : Module.End ℚ V) (M : AddSubgroup V)
    (n : ℕ) (hM : ∀ v ∈ M, Associative.dividedPower n x v ∈ M) : Module.End ℤ M where
  toFun v := ⟨Associative.dividedPower n x v, hM v v.2⟩
  map_add' a b := by
    apply Subtype.ext
    exact LinearMap.map_add _ _ _
  map_smul' t a := by
    apply Subtype.ext
    exact map_zsmul _ _ _

/-- The value of `integralDividedPower x M n hM v` coerced to `V` is
`Associative.dividedPower n x v`. -/
@[simp]
theorem integralDividedPower_apply (x : Module.End ℚ V) (M : AddSubgroup V)
    (n : ℕ) (hM : ∀ v ∈ M, Associative.dividedPower n x v ∈ M) (v : M) :
    ((integralDividedPower x M n hM v : M) : V) = Associative.dividedPower n x v := by
  rfl

/-- The zeroth restricted divided power is the identity. -/
@[simp]
theorem integralDividedPower_zero (x : Module.End ℚ V) (M : AddSubgroup V)
    (hM0 : ∀ v ∈ M, Associative.dividedPower 0 x v ∈ M) :
    integralDividedPower x M 0 hM0 = 1 := by
  ext v
  simp

/-- Multiplication formula for restricted divided powers. -/
theorem integralDividedPower_mul (x : Module.End ℚ V) (M : AddSubgroup V)
    (m n : ℕ) (hm : ∀ v ∈ M, Associative.dividedPower m x v ∈ M)
    (hn : ∀ v ∈ M, Associative.dividedPower n x v ∈ M)
    (hmn : ∀ v ∈ M, Associative.dividedPower (m + n) x v ∈ M) :
    integralDividedPower x M m hm * integralDividedPower x M n hn =
      Nat.choose (m + n) m • integralDividedPower x M (m + n) hmn := by
  ext v
  -- The underlying vectors in V match by the ambient divided-power multiplication law
  exact LinearMap.congr_fun (Associative.mul_dividedPower m n x) (v : V)

/-- The restricted divided power vanishes for degrees greater than or equal to a nilpotency
bound. -/
theorem integralDividedPower_eq_zero_of_le (x : Module.End ℚ V)
    (M : AddSubgroup V) (n : ℕ) (hn : ∀ v ∈ M, Associative.dividedPower n x v ∈ M)
    {k : ℕ} (hk : x ^ k = 0) (hkn : k ≤ n) :
    integralDividedPower x M n hn = 0 := by
  ext v
  simp [integralDividedPower_apply, Associative.dividedPower_def,
    pow_eq_zero_of_le hkn hk]

/-! ## The divided-power exponential after base change -/

variable {R : Type v} [CommRing R]

/-- The finite integral divided-power exponential on the scalar extension `R ⊗[ℤ] M`
for a nilpotent endomorphism `x`.

Although `x` acts on a rational vector space, this definition uses only the integral operators on
`M` and therefore makes sense over an arbitrary commutative parameter ring `R`. -/
noncomputable def baseChangeExp (x : Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x v ∈ M) (_hx : IsNilpotent x) (t : R) :
    Module.End R (R ⊗[ℤ] M) :=
  ∑ n ∈ range (nilpotencyClass x),
    t ^ n • (integralDividedPower x M n (hM n)).baseChange R

/-- The base-changed exponential acts on a pure tensor by the expected finite divided-power
formula. -/
@[simp]
theorem baseChangeExp_tmul (x : Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x v ∈ M) (hx : IsNilpotent x)
    (t r : R) (v : M) :
    baseChangeExp x M hM hx t (r ⊗ₜ[ℤ] v) =
      ∑ n ∈ range (nilpotencyClass x), (t ^ n * r) ⊗ₜ[ℤ]
        integralDividedPower x M n (hM n) v := by
  simp [baseChangeExp, smul_tmul']


private theorem baseChange_integralDividedPower_mul
    (x : Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x v ∈ M) (m n : ℕ) :
    (integralDividedPower x M m (hM m)).baseChange R *
        (integralDividedPower x M n (hM n)).baseChange R =
      Nat.choose (m + n) m • (integralDividedPower x M (m + n) (hM (m + n))).baseChange R := by
  rw [← LinearMap.baseChange_mul, integralDividedPower_mul]
  exact map_nsmul (Module.End.baseChangeHom ℤ R M) _ _

private theorem baseChange_integralDividedPower_eq_zero_of_le
    (x : Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x v ∈ M)
    {k n : ℕ} (hk : x ^ k = 0) (hkn : k ≤ n) :
    (integralDividedPower x M n (hM n)).baseChange R = 0 := by
  rw [integralDividedPower_eq_zero_of_le x M n (hM n) hk hkn, LinearMap.baseChange_zero]

/-- Binomial convolution identity for truncated divided-power series. -/
private theorem sum_pow_smul_mul_sum_pow_smul
    {W : Type*} [AddCommGroup W] (D : ℕ → Module.End R (R ⊗[ℤ] W)) (k : ℕ)
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
theorem baseChangeExp_add (x : Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x v ∈ M) (hx : IsNilpotent x)
    (t u : R) :
    baseChangeExp x M hM hx (t + u) = baseChangeExp x M hM hx t * baseChangeExp x M hM hx u := by
  rw [baseChangeExp, baseChangeExp, baseChangeExp]
  symm
  apply sum_pow_smul_mul_sum_pow_smul
  · intro n hn
    exact baseChange_integralDividedPower_eq_zero_of_le x M hM
      (pow_nilpotencyClass hx) hn
  · exact baseChange_integralDividedPower_mul x M hM

/-- The base-changed divided-power exponential at zero is the identity. -/
@[simp]
theorem baseChangeExp_zero (x : Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x v ∈ M) (hx : IsNilpotent x) :
    baseChangeExp (R := R) x M hM hx 0 = 1 := by
  classical
  cases subsingleton_or_nontrivial V with
  | inl hV =>
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r m =>
          have hm : m = 0 := Subtype.ext (hV.elim _ _)
          subst m
          simp
      | add a b ha hb => simp [ha, hb]
  | inr hV =>
      let _ := hV
      rw [baseChangeExp, sum_eq_single 0]
      · simp
      · intro n hn hn0
        simp [hn0]
      · simp [pos_nilpotencyClass_iff.2 hx]

/-- The base-changed divided-power exponential as a linear equivalence, with inverse given by the
negative parameter. -/
noncomputable def baseChangeExpLinearEquiv (x : Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x v ∈ M) (hx : IsNilpotent x) (t : R) :
    R ⊗[ℤ] M ≃ₗ[R] R ⊗[ℤ] M where
  toLinearMap := baseChangeExp x M hM hx t
  invFun := baseChangeExp x M hM hx (-t)
  left_inv v := by
    have h := LinearMap.congr_fun (baseChangeExp_add x M hM hx (-t) t) v
    simpa [baseChangeExp_zero x M hM hx] using h.symm
  right_inv v := by
    have h := LinearMap.congr_fun (baseChangeExp_add x M hM hx t (-t)) v
    simpa [baseChangeExp_zero x M hM hx] using h.symm

/-- The linear map underlying `baseChangeExpLinearEquiv` is `baseChangeExp`. -/
@[simp]
theorem baseChangeExpLinearEquiv_toLinearMap (x : Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x v ∈ M) (hx : IsNilpotent x) (t : R) :
    (baseChangeExpLinearEquiv x M hM hx t).toLinearMap = baseChangeExp x M hM hx t := by
  rfl

/-- The additive group of a commutative ring acts on the scalar extension of a
divided-power-stable additive subgroup by the integral nilpotent exponential. -/
noncomputable def baseChangeExpHom (x : Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x v ∈ M) (hx : IsNilpotent x) :
    Multiplicative R →* (R ⊗[ℤ] M ≃ₗ[R] R ⊗[ℤ] M) where
  toFun t := baseChangeExpLinearEquiv x M hM hx (Multiplicative.toAdd t)
  map_one' := by
    ext v
    exact LinearMap.congr_fun (baseChangeExp_zero x M hM hx) v
  map_mul' t u := by
    ext v
    exact LinearMap.congr_fun (baseChangeExp_add x M hM hx
      (Multiplicative.toAdd t) (Multiplicative.toAdd u)) v

/-- The linear map underlying the base-changed one-parameter subgroup is the corresponding
divided-power exponential. -/
@[simp]
theorem baseChangeExpHom_toLinearMap (x : Module.End ℚ V) (M : AddSubgroup V)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x v ∈ M) (hx : IsNilpotent x)
    (t : Multiplicative R) :
    (baseChangeExpHom x M hM hx t).toLinearMap =
      baseChangeExp x M hM hx (Multiplicative.toAdd t) := by
  rfl

end TauCeti
