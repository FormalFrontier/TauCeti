/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Regrouping ideal arithmetic functions by absolute norm

This file defines `TauCeti.normCoeff`, the ordinary arithmetic function obtained by summing an
`IdealArithmeticFunction` over each fibre of the absolute norm.  These fibres are finite by
`Ideal.finite_setOfPred_absNorm_eq`, so the coefficients are honest finite sums.  The resulting
function has value zero at `0`, as required by Mathlib's `ArithmeticFunction` carrier; that value
is available from `ArithmeticFunction.map_zero`.

The construction is bundled as a complex-linear map.  The basic API records the value at one and
compatibility with complex conjugation.

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

/-- The fibre of nonzero integral ideals with a fixed absolute norm is finite. -/
theorem finite_normFiber (n : ℕ) :
    {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}.Finite := by
  exact (Ideal.finite_setOfPred_absNorm_eq n).preimage Subtype.val_injective.injOn

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

/-- The summand defining a norm coefficient has finite support. -/
theorem hasFiniteSupport_normCoeff_summand (f : IdealArithmeticFunction K) (n : ℕ) :
    (Set.indicator
      {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n} f).HasFiniteSupport :=
  (finite_normFiber K n).subset Set.support_indicator_subset

/-- There is a unique nonzero integral ideal of absolute norm one, namely the unit ideal. -/
@[simp]
theorem normCoeff_apply_one (f : IdealArithmeticFunction K) : normCoeff K f 1 = f 1 := by
  rw [normCoeff_apply]
  have hfiber :
      {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = 1} = {1} := by
    ext I
    simp [Ideal.absNorm_eq_one_iff, Subtype.ext_iff]
  rw [hfiber]
  simp

/-- Regrouping commutes with coefficientwise complex conjugation. -/
@[simp]
theorem normCoeff_star_apply (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K (fun I ↦ (starRingEnd ℂ) (f I)) n = star (normCoeff K f n) := by
  simp only [normCoeff_apply]
  exact ((starAddEquiv : ℂ ≃+ ℂ).map_finsum_mem f (finite_normFiber K n)).symm

end TauCeti
