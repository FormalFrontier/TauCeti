/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Regrouping ideal arithmetic functions by absolute norm

This file defines `TauCeti.normCoeff`, the ordinary arithmetic function obtained by summing an
`IdealArithmeticFunction` over each fibre of the absolute norm.  These fibres are finite by
`Ideal.finite_setOfPred_absNorm_eq`, so the coefficients are honest finite sums.  The resulting
function has value zero at `0`, as required by Mathlib's `ArithmeticFunction` carrier; that value
is available from `ArithmeticFunction.map_zero`.

The construction is bundled as a complex-linear map.  The basic API exposes the finite norm fibre
`TauCeti.normFiber` and its finiteness, records the value at one, proves compatibility with
complex conjugation, and records in `TauCeti.norm_normCoeff_eq_sum_norm_of_nonneg` that no
cancellation occurs inside a fibre when the values of `f` are nonnegative.

Regrouping loses information as soon as a norm fibre has more than one element:
`TauCeti.exists_forall_normCoeff_nonneg_not_forall_nonneg` produces a nonzero ideal arithmetic
function, with a negative value, whose norm coefficients all vanish.  This is the rejection test
that forbids weakening the nonnegativity hypothesis of the converse regrouping theorem to
nonnegativity of the coefficients themselves.

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

open scoped nonZeroDivisors NumberField ComplexOrder

variable (K : Type*) [Field K] [NumberField K]

/-- The fibre of nonzero integral ideals with a fixed absolute norm is finite. -/
theorem finite_normFiber (n : ℕ) :
    {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}.Finite := by
  exact (Ideal.finite_setOfPred_absNorm_eq n).preimage Subtype.val_injective.injOn

/-- The finite set of nonzero integral ideals with a fixed absolute norm. -/
noncomputable def normFiber (n : ℕ) : Finset ((Ideal (𝓞 K))⁰) :=
  (finite_normFiber K n).toFinset

/-- Membership in an absolute-norm fibre. -/
@[simp]
theorem mem_normFiber {I : (Ideal (𝓞 K))⁰} {n : ℕ} :
    I ∈ normFiber K n ↔ Ideal.absNorm (I : Ideal (𝓞 K)) = n := by
  simp [normFiber]

/-- The absolute-norm fibre, viewed as a set, is the preimage of `{n}` under the absolute norm. -/
theorem coe_normFiber (n : ℕ) :
    (normFiber K n : Set ((Ideal (𝓞 K))⁰))
      = (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))) ⁻¹' {n} := by
  ext I
  simp

/-- No nonzero integral ideal has absolute norm zero. -/
@[simp]
theorem normFiber_zero : normFiber K 0 = ∅ := by
  ext I
  rw [mem_normFiber]
  constructor
  · intro hI
    exact mem_nonZeroDivisors_iff_ne_zero.mp I.property (Ideal.absNorm_eq_zero_iff.mp hI) |>.elim
  · simp

/-- The unit ideal is the unique nonzero integral ideal of absolute norm one. -/
@[simp]
theorem normFiber_one : normFiber K 1 = {1} := by
  ext I
  simp [Ideal.absNorm_eq_one_iff, Subtype.ext_iff]

/-- Regroup ideal arithmetic functions by absolute norm as a complex-linear map.

The coefficient at `n` is the finite sum of `f I` over the nonzero integral ideals `I` whose
absolute norm is `n`.  Use `normCoeff_apply` for this formula. -/
noncomputable def normCoeff : IdealArithmeticFunction K →ₗ[ℂ] ArithmeticFunction ℂ where
  toFun f :=
    { toFun n := ∑ᶠ I ∈ {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}, f I
      map_zero' := by
        apply finsum_mem_eq_zero_of_forall_eq_zero
        intro I hI
        exact
          (mem_nonZeroDivisors_iff_ne_zero.mp I.property (Ideal.absNorm_eq_zero_iff.mp hI)).elim }
  map_add' f g := by
    ext n
    simp only [Pi.add_apply]
    exact finsum_mem_add_distrib (finite_normFiber K n)
  map_smul' c f := by
    ext n
    simp only [Pi.smul_apply]
    exact (DistribSMul.toAddMonoidHom ℂ c).map_finsum_mem f (finite_normFiber K n) |>.symm

/-- The value of `normCoeff f` is the finite sum of `f` over the corresponding absolute-norm
fibre. -/
theorem normCoeff_apply (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n =
      ∑ᶠ I ∈ {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}, f I :=
  (rfl)

/-- The value of `normCoeff f` as a sum over the finite absolute-norm fibre. -/
theorem normCoeff_eq_sum_normFiber (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n = ∑ I ∈ normFiber K n, f I := by
  rw [normCoeff_apply, finsum_mem_eq_finite_toFinset_sum _ (finite_normFiber K n)]
  simp only [normFiber]

/-- The summand defining a norm coefficient has finite support. -/
theorem hasFiniteSupport_normCoeff_summand (f : IdealArithmeticFunction K) (n : ℕ) :
    (Set.indicator
      {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n} f).HasFiniteSupport :=
  (finite_normFiber K n).subset Set.support_indicator_subset

/-- The norm coefficient at `1` is the value at the unit ideal. -/
@[simp]
theorem normCoeff_apply_one (f : IdealArithmeticFunction K) : normCoeff K f 1 = f 1 := by
  rw [normCoeff_eq_sum_normFiber, normFiber_one]
  simp

/-- Regrouping commutes with coefficientwise complex conjugation. -/
@[simp]
theorem normCoeff_star_apply (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K (fun I ↦ (starRingEnd ℂ) (f I)) n = star (normCoeff K f n) := by
  simp only [normCoeff_apply]
  exact ((starAddEquiv : ℂ ≃+ ℂ).map_finsum_mem f (finite_normFiber K n)).symm

/-- **Absence of cancellation inside norm fibres**, for a nonnegative ideal arithmetic function:
the absolute value of a norm coefficient is the sum of the absolute values over the fibre. -/
theorem norm_normCoeff_eq_sum_norm_of_nonneg (f : IdealArithmeticFunction K) (hf : ∀ I, 0 ≤ f I)
    (n : ℕ) : ‖normCoeff K f n‖ = ∑ I ∈ normFiber K n, ‖f I‖ := by
  have h : normCoeff K f n = ((∑ I ∈ normFiber K n, ‖f I‖ : ℝ) : ℂ) := by
    rw [normCoeff_eq_sum_normFiber]
    push_cast
    exact Finset.sum_congr rfl fun I _ ↦ Complex.eq_coe_norm_of_nonneg (hf I)
  rw [h, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]

/-! ### The cancellation rejection test -/

/-- **Rejection test.** A nonnegative sum over an absolute-norm fibre does not force the individual
ideal summands to be nonnegative. As soon as two distinct nonzero integral ideals share an absolute
norm — for instance the two primes above `5` in `ℚ(i)` — the two-summand witness `-1 + 1 = 0`
produces a nonzero ideal arithmetic function with a negative value whose regrouping is the zero
arithmetic function, hence has nonnegative coefficients.

So the hypothesis of `TauCeti.summable_idealTerm_of_nonneg` cannot be weakened to nonnegativity of
`TauCeti.normCoeff f`, and `TauCeti.normCoeff` is not injective. -/
theorem exists_forall_normCoeff_nonneg_not_forall_nonneg {A B : (Ideal (𝓞 K))⁰} (hAB : A ≠ B)
    (hN : Ideal.absNorm (A : Ideal (𝓞 K)) = Ideal.absNorm (B : Ideal (𝓞 K))) :
    ∃ f : IdealArithmeticFunction K, f ≠ 0 ∧ normCoeff K f = 0 ∧ ¬ ∀ I, 0 ≤ f I := by
  classical
  set f : IdealArithmeticFunction K := fun I ↦ if I = A then -1 else if I = B then 1 else 0
    with hfdef
  have hfA : f A = -1 := by simp [hfdef]
  have hfB : f B = 1 := by simp [hfdef, Ne.symm hAB]
  have hf0 : ∀ I, I ≠ A → I ≠ B → f I = 0 := by
    intro I h₁ h₂
    simp [hfdef, h₁, h₂]
  refine ⟨f, fun h ↦ ?_, ?_, fun h ↦ ?_⟩
  · rw [h] at hfA
    norm_num at hfA
  · ext n
    rw [normCoeff_eq_sum_normFiber, ArithmeticFunction.zero_apply]
    by_cases hn : Ideal.absNorm (A : Ideal (𝓞 K)) = n
    · rw [Finset.sum_eq_add_of_mem A B ((mem_normFiber K).mpr hn)
        ((mem_normFiber K).mpr (hN ▸ hn)) hAB fun I _ hI ↦ hf0 I hI.1 hI.2, hfA, hfB]
      ring
    · refine Finset.sum_eq_zero fun I hI ↦ hf0 I ?_ ?_
      · exact fun h ↦ hn (h ▸ (mem_normFiber K).mp hI)
      · exact fun h ↦ hn (hN.trans (h ▸ (mem_normFiber K).mp hI))
  · have := (Complex.le_def.mp (h A)).1
    rw [hfA] at this
    norm_num at this

end TauCeti
