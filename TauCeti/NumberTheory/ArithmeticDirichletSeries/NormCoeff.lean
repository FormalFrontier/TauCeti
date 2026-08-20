/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Basic
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Regrouping ideal arithmetic functions by absolute norm

This file defines `TauCeti.normCoeff`, the ordinary arithmetic function obtained by summing an
`IdealArithmeticFunction` over each fibre of the absolute norm.  These fibres are finite by
`Ideal.finite_setOfPred_absNorm_eq`, so the coefficients are honest finite sums.  The resulting
function has value zero at `0`, as required by Mathlib's `ArithmeticFunction` carrier.

The basic API records the values at zero and one and compatibility with the additive operations,
complex scalar multiplication, and complex conjugation.  For the constant-one ideal arithmetic
function, the positive coefficients are the numbers of integral ideals of the corresponding norm;
hence its `LSeries` is Mathlib's `NumberField.dedekindZeta`.

## Roadmap role

This is the finite-norm-fibre part of Layer **1.1** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  The next layer step uses these coefficients
to regroup an absolutely convergent series over nonzero ideals into a Mathlib `LSeries`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapters II--III.
-/

public section

namespace TauCeti

open scoped nonZeroDivisors NumberField

variable (K : Type*) [Field K] [NumberField K]

private theorem finite_normFiber (n : ℕ) :
    {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}.Finite := by
  exact (Ideal.finite_setOfPred_absNorm_eq n).preimage Subtype.val_injective.injOn

/-- Regroup an ideal arithmetic function by absolute norm.

The coefficient at `n` is the finite sum of `f I` over the nonzero integral ideals `I` whose
absolute norm is `n`.  Use `normCoeff_apply` for this formula. -/
noncomputable def normCoeff (f : IdealArithmeticFunction K) : ArithmeticFunction ℂ where
  toFun n := ∑ᶠ I ∈ {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}, f I
  map_zero' := by
    apply finsum_mem_eq_zero_of_forall_eq_zero
    intro I hI
    exact (mem_nonZeroDivisors_iff_ne_zero.mp I.property (Ideal.absNorm_eq_zero_iff.mp hI)).elim

/-- The value of `normCoeff f` is the finite sum of `f` over the corresponding absolute-norm
fibre. -/
theorem normCoeff_apply (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n =
      ∑ᶠ I ∈ {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}, f I :=
  (rfl)

/-- The summand defining a norm coefficient has finite support. -/
theorem normCoeff_summand_hasFiniteSupport (f : IdealArithmeticFunction K) (n : ℕ) :
    (Set.indicator
      {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n} f).HasFiniteSupport :=
  (finite_normFiber K n).subset Set.support_indicator_subset

/-- The zeroth norm coefficient is zero. -/
@[simp]
theorem normCoeff_zero (f : IdealArithmeticFunction K) : normCoeff K f 0 = 0 := by
  rw [normCoeff_apply]
  apply finsum_mem_eq_zero_of_forall_eq_zero
  intro I hI
  exact (mem_nonZeroDivisors_iff_ne_zero.mp I.property (Ideal.absNorm_eq_zero_iff.mp hI)).elim

/-- There is a unique nonzero integral ideal of absolute norm one, namely the unit ideal. -/
@[simp]
theorem normCoeff_one (f : IdealArithmeticFunction K) : normCoeff K f 1 = f 1 := by
  rw [normCoeff_apply]
  have hfiber :
      {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = 1} = {1} := by
    ext I
    simp [Ideal.absNorm_eq_one_iff, Subtype.ext_iff]
  rw [hfiber]
  simp

/-- Regrouping the zero ideal arithmetic function gives the zero arithmetic function. -/
@[simp]
theorem normCoeff_zero_fun : normCoeff K (0 : IdealArithmeticFunction K) = 0 := by
  ext n
  simp [normCoeff_apply]

/-- Regrouping commutes with pointwise addition. -/
@[simp]
theorem normCoeff_add (f g : IdealArithmeticFunction K) :
    normCoeff K (f + g) = normCoeff K f + normCoeff K g := by
  ext n
  simp only [normCoeff_apply, Pi.add_apply, ArithmeticFunction.add_apply]
  exact finsum_mem_add_distrib (finite_normFiber K n)

/-- Regrouping commutes with pointwise negation. -/
@[simp]
theorem normCoeff_neg (f : IdealArithmeticFunction K) :
    normCoeff K (-f) = -normCoeff K f := by
  ext n
  simp only [normCoeff_apply, Pi.neg_apply, ArithmeticFunction.neg_apply]
  exact finsum_mem_neg_distrib f (finite_normFiber K n)

/-- Regrouping commutes with pointwise subtraction. -/
@[simp]
theorem normCoeff_sub (f g : IdealArithmeticFunction K) :
    normCoeff K (f - g) = normCoeff K f - normCoeff K g := by
  rw [sub_eq_add_neg, normCoeff_add, normCoeff_neg, sub_eq_add_neg]

/-- Regrouping commutes with complex scalar multiplication. -/
@[simp]
theorem normCoeff_smul (c : ℂ) (f : IdealArithmeticFunction K) :
    normCoeff K (c • f) = c • normCoeff K f := by
  ext n
  simp only [normCoeff_apply, Pi.smul_apply, ArithmeticFunction.smul_map]
  exact (DistribSMul.toAddMonoidHom ℂ c).map_finsum_mem f (finite_normFiber K n) |>.symm

/-- Regrouping commutes with coefficientwise complex conjugation. -/
theorem normCoeff_conj_apply (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K (fun I ↦ star (f I)) n = star (normCoeff K f n) := by
  simp only [normCoeff_apply]
  exact ((starAddEquiv : ℂ ≃+ ℂ).map_finsum_mem f (finite_normFiber K n)).symm

private noncomputable def normFiberEquiv (n : ℕ) (hn : n ≠ 0) :
    {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n} ≃
      {I : Ideal (𝓞 K) // Ideal.absNorm I = n} where
  toFun I := ⟨I.1, I.2⟩
  invFun I := ⟨⟨I.1, by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hI
    apply hn
    rw [← I.2, Ideal.absNorm_eq_zero_iff]
    simpa only [Submodule.zero_eq_bot] using hI⟩, I.2⟩
  left_inv I := rfl
  right_inv I := rfl

/-- For positive `n`, the coefficient of the constant-one ideal arithmetic function is the number
of integral ideals of absolute norm `n`. -/
theorem normCoeff_one_apply_of_ne_zero (n : ℕ) (hn : n ≠ 0) :
    normCoeff K (1 : IdealArithmeticFunction K) n =
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) := by
  rw [normCoeff_apply]
  rw [finsum_mem_eq_finite_toFinset_sum _ (finite_normFiber K n)]
  simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  norm_cast
  rw [← Set.ncard_eq_toFinset_card
    {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n} (finite_normFiber K n),
    ← Nat.card_coe_set_eq]
  exact Nat.card_congr (normFiberEquiv K n hn)

/-- The `LSeries` obtained from the constant-one ideal arithmetic function is Mathlib's Dedekind
zeta function.  The two coefficient functions differ at `0`, which `LSeries` ignores. -/
theorem LSeries_normCoeff_one (s : ℂ) :
    LSeries (normCoeff K (1 : IdealArithmeticFunction K)) s = NumberField.dedekindZeta K s := by
  unfold NumberField.dedekindZeta
  exact LSeries_congr (fun hn ↦ normCoeff_one_apply_of_ne_zero K _ hn) s

end TauCeti
