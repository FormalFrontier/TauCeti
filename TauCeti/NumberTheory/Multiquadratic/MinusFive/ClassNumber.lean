/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.AdjoinRoot
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers
import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification
import TauCeti.NumberTheory.NumberField.IntegralSqrt
import TauCeti.RingTheory.Norm.Quadratic

/-!
# The class number of `ℚ(√-5)`

This file proves that the imaginary quadratic field `ℚ(√-5)` has class number `2`, the
class-group calculation in the first genus-field worked example of the multiquadratic roadmap.

The proof uses Minkowski's theorem in the form
`NumberField.exists_ideal_in_class_of_norm_le`.  Since the discriminant is `-20` and there is one
complex place, every ideal class has an integral representative of norm less than `3`.  A nonzero
ideal of norm `1` is the unit ideal, while one of norm `2` is the unique prime above the ramified
prime `2`.  Thus there are at most two ideal classes.  The prime above `2` is not principal:
`𝓞_{ℚ(√-5)} = ℤ[√-5]`, and a generator would give an integer solution of
`a² + 5b² = 2`.

The main theorem is stated for any number field with an integral generator of minimal polynomial
`X² + 5`; the final theorem applies it to Mathlib's `AdjoinRoot` model.

The argument follows the standard Minkowski proof; see D. A. Cox, *Primes of the Form
x² + ny²*, Chapter 5.

## Main results

* `TauCeti.NumberField.classNumber_eq_two_of_minpoly_eq_X_sq_add_five`: every presentation of
  `ℚ(√-5)` by an integral generator has class number two.
* `TauCeti.NumberField.classNumber_adjoinRoot_sqrt_neg_five_eq_two`: the result for the concrete
  `AdjoinRoot (X² + 5)` model.
-/

public section

open Ideal Module NumberField Polynomial
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

omit [NumberField K] in
/-- The generator of a presentation of `ℚ(√-5)` squares to `-5` in its ring of integers. -/
private theorem gen_sq_eq_neg_five
    (hmin : minpoly ℤ θ = X ^ 2 - C (-5 : ℤ)) :
    θ ^ 2 = algebraMap ℤ (𝓞 K) (-5) := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [map_pow, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]
  exact coe_gen_sq hmin

/-- Every algebraic integer in `ℚ(√-5)` has integral coordinates `a + b√-5`. -/
private theorem exists_eq_intCast_add_intCast_mul
    (hmin : minpoly ℤ θ = X ^ 2 - C (-5 : ℤ))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (z : 𝓞 K) :
    ∃ a b : ℤ, z = algebraMap ℤ (𝓞 K) a + algebraMap ℤ (𝓞 K) b * θ := by
  have htop : Algebra.adjoin ℤ {θ} = (⊤ : Subalgebra ℤ (𝓞 K)) :=
    adjoin_gen_eq_top_of_mod_four_ne_one hmin hgen
      ((Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree) (by norm_num)
  have hz : z ∈ Algebra.adjoin ℤ {θ} := by rw [htop]; trivial
  have hθ := gen_sq_eq_neg_five hmin
  refine Algebra.adjoin_induction (p := fun x _ =>
      ∃ a b : ℤ, x = algebraMap ℤ (𝓞 K) a + algebraMap ℤ (𝓞 K) b * θ)
    (fun x hx => ?_) (fun a => ?_) (fun x y _ _ hx hy => ?_)
      (fun x y _ _ hx hy => ?_) hz
  · rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨0, 1, by simp⟩
  · exact ⟨a, 0, by simp⟩
  · obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    refine ⟨a + c, b + e, ?_⟩
    simp only [map_add]
    ring
  · obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, e, rfl⟩ := hy
    refine ⟨a * c - 5 * b * e, a * e + b * c, ?_⟩
    apply RingOfIntegers.coe_injective
    simp only [map_sub, map_add, map_mul, map_ofNat]
    simp_rw [← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]
    ring_nf
    rw [coe_gen_sq hmin]
    norm_num
    ring

/-- The norm form on the ring of integers of `ℚ(√-5)` is `a² + 5b²`. -/
private theorem exists_norm_eq_sq_add_five_mul_sq
    (hmin : minpoly ℤ θ = X ^ 2 - C (-5 : ℤ))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (z : 𝓞 K) :
    ∃ a b : ℤ, Algebra.norm ℤ z = a ^ 2 + 5 * b ^ 2 := by
  obtain ⟨a, b, hz⟩ := exists_eq_intCast_add_intCast_mul hmin hgen z
  let hquad : Algebra.IsQuadraticExtension ℚ K := ⟨finrank_rat_eq_two hmin hgen⟩
  let pb : PowerBasis ℚ K := PowerBasis.ofAdjoinEqTop' θ.isIntegral_coe.tower_top hgen
  have hpbgen : pb.gen = (θ : K) :=
    PowerBasis.ofAdjoinEqTop'_gen θ.isIntegral_coe.tower_top hgen
  have hpbdim : pb.dim = 2 := by rw [← pb.finrank, finrank_rat_eq_two hmin hgen]
  have hnormθ : Algebra.norm ℚ (θ : K) = 5 := by
    have hnorm := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    rw [hpbgen, hpbdim, minpoly_rat_quadratic hmin] at hnorm
    norm_num at hnorm
    exact hnorm
  let _ := hquad
  have hnormQ : Algebra.norm ℚ (z : K) = (a : ℚ) ^ 2 + 5 * (b : ℚ) ^ 2 := by
    have hzK := congrArg (algebraMap (𝓞 K) K) hz
    simp only [map_add, map_mul] at hzK
    simp_rw [← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K] at hzK
    have hZQ (n : ℤ) : algebraMap ℤ K n = algebraMap ℚ K (n : ℚ) := by
      rw [IsScalarTower.algebraMap_apply ℤ ℚ K]
      norm_num
    -- Name the coercion as the ring-of-integers algebra map so that `hzK` rewrites it.
    change Algebra.norm ℚ (algebraMap (𝓞 K) K z) =
      (a : ℚ) ^ 2 + 5 * (b : ℚ) ^ 2
    rw [hzK, hZQ, hZQ]
    rw [Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul,
      trace_gen_eq_zero hmin, hnormθ]
    ring
  refine ⟨a, b, ?_⟩
  have hcast : ((Algebra.norm ℤ z : ℤ) : ℚ) = ((a ^ 2 + 5 * b ^ 2 : ℤ) : ℚ) := by
    rw [Algebra.coe_norm_int, hnormQ]
    push_cast
    ring
  exact Int.cast_injective hcast

/-- The discriminant of a presentation of `ℚ(√-5)` is `-20`. -/
private theorem discr_eq_neg_twenty
    (hmin : minpoly ℤ θ = X ^ 2 - C (-5 : ℤ))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    NumberField.discr K = -20 := by
  simpa using discr_eq_four_mul_of_mod_four_ne_one hmin hgen
    ((Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree) (by norm_num)

/-- The Minkowski bound of `ℚ(√-5)` is strictly less than `3`. -/
private theorem minkowski_bound_lt_three
    (hmin : minpoly ℤ θ = X ^ 2 - C (-5 : ℤ))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
        ((finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) *
          Real.sqrt |(NumberField.discr K : ℝ)|) < 3 := by
  have hfin : finrank ℚ K = 2 := finrank_rat_eq_two hmin hgen
  have _ : IsTotallyComplex K :=
    isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg hmin (by norm_num)
  have hreal : InfinitePlace.nrRealPlaces K = 0 :=
    NumberField.IsTotallyComplex.nrRealPlaces_eq_zero K
  have hcomplex : InfinitePlace.nrComplexPlaces K = 1 := by
    have hsignature := InfinitePlace.card_add_two_mul_card_eq_rank K
    rw [hreal, hfin] at hsignature
    omega
  have hdisc := discr_eq_neg_twenty hmin hgen
  have hsqrt : Real.sqrt 20 < 9 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  rw [hcomplex, hfin, hdisc]
  norm_num [abs_of_nonneg]
  calc
    4 / Real.pi * (1 / 2 * Real.sqrt 20) = 2 * Real.sqrt 20 / Real.pi := by ring
    _ < 3 := by
      rw [div_lt_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three]

/-- The unique prime above `2` in `ℚ(√-5)` is not principal. -/
private theorem not_isPrincipal_primeAboveTwo
    (hmin : minpoly ℤ θ = X ^ 2 - C (-5 : ℤ))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] :
    ¬ Submodule.IsPrincipal P := by
  have hfin : finrank ℚ K = 2 := finrank_rat_eq_two hmin hgen
  have hdisc := discr_eq_neg_twenty hmin hgen
  have hram : 2 ∈ ramifiedPrimes K := by
    rw [mem_ramifiedPrimes_iff_dvd_discr (K := K) Nat.prime_two, hdisc]
    norm_num
  intro hprincipal
  let _ : Submodule.IsPrincipal P := hprincipal
  let z : 𝓞 K := Submodule.IsPrincipal.generator P
  have hnormP : P.absNorm = 2 := absNorm_eq_of_mem_ramifiedPrimes hfin hram P
  have hnormz : (Algebra.norm ℤ z).natAbs = 2 := by
    have hzspan : Ideal.span {z} = P := by
      exact Submodule.IsPrincipal.span_singleton_generator P
    rw [← Ideal.absNorm_span_singleton z, hzspan, hnormP]
  obtain ⟨a, b, hab⟩ := exists_norm_eq_sq_add_five_mul_sq hmin hgen z
  rw [hab, Int.natAbs_eq_iff] at hnormz
  have heq : a ^ 2 + 5 * b ^ 2 = 2 := by
    rcases hnormz with h | h
    · exact_mod_cast h
    · have : (0 : ℤ) ≤ a ^ 2 + 5 * b ^ 2 := by positivity
      omega
  by_cases hb : b = 0
  · subst b
    norm_num at heq
    have hprimeTwo : Prime (2 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by decide)
    exact (Prime.not_isSquare hprimeTwo)
      ⟨a, by simpa [pow_two] using heq.symm⟩
  · have hbpos : 0 < b ^ 2 := sq_pos_of_ne_zero hb
    have hb1 : (1 : ℤ) ≤ b ^ 2 := by omega
    nlinarith [sq_nonneg a]

/-- **The class number of `ℚ(√-5)` is two.** This presentation-independent statement assumes an
integral generator with minimal polynomial `X² + 5` which generates the field over `ℚ`. -/
theorem classNumber_eq_two_of_minpoly_eq_X_sq_add_five
    (hmin : minpoly ℤ θ = X ^ 2 - C (-5 : ℤ))
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : NumberField.classNumber K = 2 := by
  classical
  have hfin : finrank ℚ K = 2 := finrank_rat_eq_two hmin hgen
  have hdisc := discr_eq_neg_twenty hmin hgen
  have hram : 2 ∈ ramifiedPrimes K := by
    rw [mem_ramifiedPrimes_iff_dvd_discr (K := K) Nat.prime_two, hdisc]
    norm_num
  let _ : (span {(2 : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).mpr
      (Int.prime_iff_natAbs_prime.mpr Nat.prime_two)
  obtain ⟨⟨P, hPprime, hPover⟩⟩ :=
    (inferInstance : Nonempty ((span {(2 : ℤ)} : Ideal ℤ).primesOver (𝓞 K)))
  let _ : P.IsPrime := hPprime
  let _ : P.LiesOver (span {(2 : ℤ)}) := hPover
  have hPne : P ≠ 0 := by
    rw [Ideal.zero_eq_bot]
    exact Ideal.ne_bot_of_liesOver_of_ne_bot (p := span {(2 : ℤ)}) (by norm_num) P
  let P0 : nonZeroDivisors (Ideal (𝓞 K)) :=
    ⟨P, mem_nonZeroDivisors_of_ne_zero hPne⟩
  have hPclass : ClassGroup.mk0 P0 ≠ 1 := by
    intro h
    apply not_isPrincipal_primeAboveTwo hmin hgen P
    exact (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_of_ne_zero hPne)).mp
      (by simpa [P0] using h)
  have hM := minkowski_bound_lt_three hmin hgen
  have hclasses : ∀ C : ClassGroup (𝓞 K), C = 1 ∨ C = ClassGroup.mk0 P0 := by
    intro C
    obtain ⟨I, hIC, hIle⟩ := NumberField.exists_ideal_in_class_of_norm_le C
    have hIlt : (I.1.absNorm : ℝ) < 3 := hIle.trans_lt hM
    have hIleTwo : I.1.absNorm ≤ 2 := by
      exact_mod_cast (Nat.lt_succ_iff.mp (by exact_mod_cast hIlt))
    have hIpos : 0 < I.1.absNorm := absNorm_pos_of_nonZeroDivisors I
    rcases (by omega : I.1.absNorm = 1 ∨ I.1.absNorm = 2) with hnorm | hnorm
    · left
      rw [← hIC]
      exact (ClassGroup.mk0_eq_one_iff I.2).mpr <| by
        rw [Ideal.absNorm_eq_one_iff.mp hnorm]
        exact top_isPrincipal
    · right
      rw [← hIC]
      have hIP : I.1 = P :=
        eq_of_absNorm_eq_of_mem_ramifiedPrimes hfin hram P I.1 hnorm
      apply congrArg ClassGroup.mk0
      exact Subtype.ext hIP
  have hupper : NumberField.classNumber K ≤ 2 := by
    rw [NumberField.classNumber]
    calc
      Fintype.card (ClassGroup (𝓞 K)) = Finset.univ.card := by simp
      _ ≤ ({1, ClassGroup.mk0 P0} : Finset (ClassGroup (𝓞 K))).card :=
        Finset.card_le_card fun C _ => by simpa using hclasses C
      _ ≤ 2 := Finset.card_le_two
  have _ : Nontrivial (ClassGroup (𝓞 K)) :=
    nontrivial_iff.mpr ⟨ClassGroup.mk0 P0, 1, hPclass⟩
  have hlower : 2 ≤ NumberField.classNumber K := by
    rw [NumberField.classNumber]
    exact Fintype.one_lt_card
  omega

local instance : Fact (Irreducible (X ^ 2 - C (-5 : ℚ))) := ⟨by
  exact (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
    (fun q _ => by nlinarith [sq_nonneg q])⟩

/-- **Worked example.** The concrete number field `AdjoinRoot (X² + 5)`, modelling `ℚ(√-5)`,
has class number `2`. -/
@[simp]
theorem classNumber_adjoinRoot_sqrt_neg_five_eq_two :
    NumberField.classNumber (AdjoinRoot (X ^ 2 - C (-5 : ℚ))) = 2 := by
  let K := AdjoinRoot (X ^ 2 - C (-5 : ℚ))
  let x : K := AdjoinRoot.root (X ^ 2 - C (-5 : ℚ))
  have hx : x ^ 2 = algebraMap ℤ K (-5 : ℤ) := by
    have hroot := AdjoinRoot.eval₂_root (X ^ 2 - C (-5 : ℚ))
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, ← AdjoinRoot.algebraMap_eq, sub_eq_zero] at hroot
    rw [hroot, IsScalarTower.algebraMap_apply ℤ ℚ K]
    norm_num
  let θ : 𝓞 K := integralSqrt hx
  have hmin : minpoly ℤ θ = X ^ 2 - C (-5 : ℤ) :=
    minpoly_integralSqrt hx (fun ⟨q, hq⟩ => by
      norm_num at hq
      nlinarith [mul_self_nonneg q])
  have hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤ := by
    have hfne : (X ^ 2 - C (-5 : ℚ)) ≠ 0 :=
      (monic_X_pow_sub_C (-5 : ℚ) (by norm_num)).ne_zero
    have hpb := (AdjoinRoot.powerBasis (f := X ^ 2 - C (-5 : ℚ)) hfne).adjoin_gen_eq_top
    rw [AdjoinRoot.powerBasis_gen] at hpb
    have hθx : (θ : K) = x := algebraMap_integralSqrt hx
    rw [hθx]
    exact hpb
  exact classNumber_eq_two_of_minpoly_eq_X_sq_add_five hmin hgen

end TauCeti.NumberField
