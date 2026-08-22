/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convolution
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Regrouping ideal arithmetic functions by absolute norm

This file defines `TauCeti.normCoeff`, the ordinary arithmetic function obtained by summing an
`IdealArithmeticFunction` over each fibre of the absolute norm.  These fibres are finite by
`Ideal.finite_setOfPred_absNorm_eq`, so the coefficients are honest finite sums.  The resulting
function has value zero at `0`, as required by Mathlib's `ArithmeticFunction` carrier; that value
is available from `ArithmeticFunction.map_zero`.

The construction is bundled as a complex-linear map.  The basic API records the value at one,
compatibility with complex conjugation, and the fact that regrouping transports ideal convolution
to Mathlib's Dirichlet convolution of arithmetic functions.

## Roadmap role

This is the finite-norm-fibre part of Layer **1.1** and the convolution-transport part of Layer
**2.1** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  The next Layer 1 step uses these
coefficients to regroup an absolutely convergent series over nonzero ideals into a Mathlib
`LSeries`; the next Layer 2 step uses the convolution formula for ideal Möbius inversion.

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

/-! ## Compatibility with Dirichlet convolution -/

private noncomputable def normFiber (n : ℕ) : Finset ((Ideal (𝓞 K))⁰) :=
  (finite_normFiber K n).toFinset

@[simp]
private theorem mem_normFiber {I : (Ideal (𝓞 K))⁰} {n : ℕ} :
    I ∈ normFiber K n ↔ Ideal.absNorm (I : Ideal (𝓞 K)) = n := by
  simp [normFiber]

private theorem normCoeff_eq_sum_normFiber (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n = ∑ I ∈ normFiber K n, f I := by
  rw [normCoeff_apply, finsum_mem_eq_finite_toFinset_sum _ (finite_normFiber K n)]
  rfl

/-- Regrouping sends the identity for ideal convolution to the identity for Mathlib's Dirichlet
convolution. -/
@[simp]
theorem normCoeff_delta : normCoeff K IdealArithmeticFunction.delta = 1 := by
  classical
  ext n
  by_cases hn : n = 1
  · subst n
    rw [normCoeff_apply_one, IdealArithmeticFunction.delta_one]
    simp
  · simp only [normCoeff_eq_sum_normFiber, ArithmeticFunction.one_apply, hn]
    apply Finset.sum_eq_zero
    intro I hI
    apply IdealArithmeticFunction.delta_of_ne_one
    intro hI_one
    subst I
    have hnorm : 1 = n := by simpa [normFiber] using hI
    exact hn hnorm.symm

/-- Regrouping by absolute norm transports ideal convolution to Mathlib's Dirichlet convolution
of arithmetic functions. -/
@[simp]
theorem normCoeff_convolution (f g : IdealArithmeticFunction K) :
    normCoeff K (f.convolution g) = normCoeff K f * normCoeff K g := by
  ext n
  rcases n with _ | n
  · simp
  simp only [normCoeff_eq_sum_normFiber, IdealArithmeticFunction.convolution_apply,
    ArithmeticFunction.mul_apply, Finset.sum_mul_sum, Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun ⟨A, p⟩ ↦
      ⟨(Ideal.absNorm (p.1 : Ideal (𝓞 K)), Ideal.absNorm (p.2 : Ideal (𝓞 K))),
        ⟨p.1, p.2⟩⟩)
    (fun ⟨_d, ⟨B, C⟩⟩ ↦ ⟨B * C, (B, C)⟩) ?_ ?_ ?_ ?_ ?_ <;>
    simp only [Finset.mem_sigma, mem_normFiber, Ideal.mem_divisorsAntidiagonal,
      Nat.mem_divisorsAntidiagonal] <;>
    aesop

/-- Regrouping transports iterated ideal convolution to powers under Mathlib's Dirichlet
convolution. -/
@[simp]
theorem normCoeff_convolutionPow (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K (f.convolutionPow n) = normCoeff K f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [IdealArithmeticFunction.convolutionPow_succ, normCoeff_convolution, ih,
      pow_succ]

end TauCeti
