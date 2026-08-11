/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.EffectiveBounds.IdealCount.Basic
public import TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic
import TauCeti.NumberTheory.EffectiveBounds.Discriminant.Basic
import TauCeti.NumberTheory.EffectiveBounds.UnitSquares.Basic

/-!
# An effective class-number bound

For a number field `F` of degree `n`, the class number is bounded by

`h_F ≤ |d_F| · 4ⁿ`.

By Mathlib's Minkowski bound (`NumberField.exists_ideal_in_class_of_norm_le`) every ideal
class contains an integral ideal of norm at most `(4/π)^s · (n!/nⁿ) · √|d_F| ≤ √|d_F|`, so the
classes inject into the ideals of norm `≤ √|d_F|`, of which there are at most `|d_F| · 2ⁿ` by
`card_ideal_absNorm_le`.

## Main result

* `TauCeti.NumberField.classNumber_le_bound`: `h_F ≤ |d_F| · 4^[F:ℚ]`.
* `TauCeti.NumberField.classNumber_le_of_abs_discr_le_of_finrank_le`: the monotone
  corollary from separate discriminant and degree bounds.

The remaining declarations package this bound with the unit-square index bound
`TauCeti.NumberField.units_sq_index_le`. The `classNumber_mul_units_sq_index_le` family records
the product estimate `h_F · [O_F^× : (O_F^×)²] ≤ |d_F| · 8^[F:ℚ]` (and the same for the
elementary-2 quotient), and the quadratic square-root specializations
`classNumber_le_of_sq_intCast`, `classNumber_le_natAbs_of_sq_intCast`, and
`classNumber_mul_units_sq_index_le_natAbs_of_sq_intCast` compose these with the quadratic
discriminant bound `TauCeti.NumberField.abs_discr_le_of_sq_intCast` to turn a square-root model
`x² = a ∈ ℤ` of a quadratic field directly into `h_K ≤ 64·|a|` and
`h_K · [O_K^× : (O_K^×)²] ≤ 256·|a|`. These are the closed forms the roadmap's `ℚ(√-5)` worked
example needs.

## Provenance

The general class-number estimate was migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the
formalization of L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture.
The product and quadratic specializations are local corollaries combining that estimate with the
migrated discriminant and unit-square bounds.
-/

public section

open scoped NumberField

open Module _root_.NumberField

namespace TauCeti.NumberField

/-- The squared Minkowski covolume factor, times `2 ^ n`, is at most `4 ^ n` whenever
`2 * s ≤ n`. -/
private lemma minkowski_factor_sq_mul_two_pow_le_four_pow {n s : ℕ} (h : 2 * s ≤ n) :
    (4 / Real.pi) ^ (2 * s) * ((n.factorial / n ^ n : ℝ)) ^ 2 * 2 ^ n ≤ 4 ^ n := by
  refine le_trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) ?_)
    (by positivity)) ?_
  · have h_factorial_le_pow : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
      exact_mod_cast Nat.factorial_le_pow n
    exact pow_le_one₀ (by positivity) (div_le_one_of_le₀ h_factorial_le_pow (by positivity))
  · have h_pi_le_two : (4 : ℝ) / Real.pi ≤ 2 := by
      rw [div_le_iff₀] <;> linarith [Real.pi_gt_three]
    have h_four : (4 : ℝ) = 2 ^ 2 := by norm_num
    refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity)
      h_pi_le_two _)
      (by positivity)) ?_
    rw [h_four, ← pow_mul, ← pow_add]
    gcongr <;> norm_num
    linarith

/-- **Class number bound.** The class number of a number field `F` is at most
`|discr F| * 4 ^ [F : ℚ]`. -/
theorem classNumber_le_bound (F : Type*) [Field F] [NumberField F] :
    (NumberField.classNumber F : ℝ) ≤
      |(NumberField.discr F : ℝ)| * 4 ^ Module.finrank ℚ F := by
  have := @NumberField.exists_ideal_in_class_of_norm_le F _ _
  choose f hf using this
  have h_card : (Set.ncard (Set.image (fun C => (f C : Ideal (𝓞 F))) Set.univ)) ≤
      (4 / Real.pi) ^ (2 * InfinitePlace.nrComplexPlaces F) *
        ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F) ^ 2 *
        |(discr F : ℝ)| * 2 ^ Module.finrank ℚ F := by
    have h_card : (Set.ncard {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤
        (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces F *
          ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F *
            Real.sqrt |(discr F : ℝ)|)}) ≤
        (4 / Real.pi) ^ (2 * InfinitePlace.nrComplexPlaces F) *
          ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F) ^ 2 *
          |(discr F : ℝ)| * 2 ^ Module.finrank ℚ F := by
      convert card_ideal_absNorm_le F _ |>.2 using 1
      · ring_nf; norm_num [Real.sq_sqrt <| abs_nonneg _]
      · refine le_trans ?_ (hf 1 |>.2)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors _)
    refine le_trans ?_ h_card
    gcongr
    · convert card_ideal_absNorm_le F _ |>.1 using 1
      refine le_trans ?_ (hf 1 |>.2)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_ne_zero_of_nonZeroDivisors _)
    · simp only [Set.image_univ]
      exact Set.range_subset_iff.mpr fun C =>
        ⟨by intro h; simpa [h] using f C |>.2, hf C |>.2⟩
  refine le_trans ?_ (h_card.trans ?_)
  · rw [Set.ncard_image_of_injective _ fun x y hxy => ?_, Set.ncard_univ]
    · norm_num [classNumber]
    · have := hf x; have := hf y; aesop
  · -- Simplify the right-hand side of the inequality.
    suffices h_simp : (4 / Real.pi) ^ (2 * InfinitePlace.nrComplexPlaces F) *
        ((Module.finrank ℚ F).factorial / (Module.finrank ℚ F) ^ Module.finrank ℚ F) ^ 2 *
        2 ^ Module.finrank ℚ F ≤ 4 ^ Module.finrank ℚ F by
      convert mul_le_mul_of_nonneg_left h_simp (abs_nonneg (discr F : ℝ)) using 1; ring
    have := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank F
    exact minkowski_factor_sq_mul_two_pow_le_four_pow (by linarith)

/-- If a number field has discriminant bounded by `D` and degree bounded by `n`, then its class
number is bounded by `D * 4^n`.

This is the monotone form of `TauCeti.NumberField.classNumber_le_bound`, useful when the
discriminant and degree have already been bounded separately. -/
theorem classNumber_le_of_abs_discr_le_of_finrank_le (F : Type*) [Field F] [NumberField F]
    {D : ℝ} {n : ℕ} (hD : |(NumberField.discr F : ℝ)| ≤ D) (hn : Module.finrank ℚ F ≤ n) :
    (NumberField.classNumber F : ℝ) ≤ D * 4 ^ n := by
  calc
    (NumberField.classNumber F : ℝ)
        ≤ |(NumberField.discr F : ℝ)| * 4 ^ Module.finrank ℚ F :=
          classNumber_le_bound F
    _ ≤ D * 4 ^ n := by
      gcongr
      · exact le_trans (abs_nonneg (NumberField.discr F : ℝ)) hD
      · norm_num

/-- A version of `classNumber_le_of_abs_discr_le_of_finrank_le` with a natural-number
discriminant bound and a natural-number conclusion.

Here `|NumberField.discr F|` is the integer absolute value of the discriminant, compared with
the natural-number bound `D` coerced to `ℤ`, so this is the form to use when the available
discriminant estimate is stated in `ℕ`. -/
theorem classNumber_le_nat_of_abs_discr_le_of_finrank_le (F : Type*) [Field F] [NumberField F]
    {D n : ℕ} (hD : |NumberField.discr F| ≤ D) (hn : Module.finrank ℚ F ≤ n) :
    NumberField.classNumber F ≤ D * 4 ^ n := by
  have hD_real : |(NumberField.discr F : ℝ)| ≤ (D : ℝ) := by
    rw [← Int.cast_abs]
    exact_mod_cast hD
  exact_mod_cast classNumber_le_of_abs_discr_le_of_finrank_le F hD_real hn

/-- If `|d_F| ≤ D`, then `h_F ≤ D * 4^[F:ℚ]`. -/
theorem classNumber_le_of_abs_discr_le (F : Type*) [Field F] [NumberField F] {D : ℝ}
    (hD : |(NumberField.discr F : ℝ)| ≤ D) :
    (NumberField.classNumber F : ℝ) ≤ D * 4 ^ Module.finrank ℚ F :=
  classNumber_le_of_abs_discr_le_of_finrank_le F hD le_rfl

/-- Natural-number version of `classNumber_le_of_abs_discr_le`. -/
theorem classNumber_le_nat_of_abs_discr_le (F : Type*) [Field F] [NumberField F] {D : ℕ}
    (hD : |NumberField.discr F| ≤ D) :
    NumberField.classNumber F ≤ D * 4 ^ Module.finrank ℚ F :=
  classNumber_le_nat_of_abs_discr_le_of_finrank_le F hD le_rfl

/-! ### Product bounds for class groups and unit-square quotients -/

private lemma abs_discr_le_natAbs (F : Type*) [Field F] [NumberField F] :
    |NumberField.discr F| ≤ (NumberField.discr F).natAbs := by
  rw [Int.abs_eq_natAbs]

private lemma four_pow_mul_two_pow (n : ℕ) : 4 ^ n * 2 ^ n = 8 ^ n := by
  rw [← mul_pow]
  norm_num

/-- **Class-number/unit-square product bound.** For a number field `F`, the product of its class
number and the index of squares in its unit group is at most `|d_F| * 8^[F:ℚ]`. -/
theorem classNumber_mul_units_sq_index_le (F : Type*) [Field F] [NumberField F] :
    NumberField.classNumber F * (Subgroup.square (𝓞 F)ˣ).index ≤
      (NumberField.discr F).natAbs * 8 ^ finrank ℚ F := by
  have hclass :
      NumberField.classNumber F ≤ (NumberField.discr F).natAbs * 4 ^ finrank ℚ F :=
    classNumber_le_nat_of_abs_discr_le F (abs_discr_le_natAbs F)
  have hunits : (Subgroup.square (𝓞 F)ˣ).index ≤ 2 ^ finrank ℚ F :=
    units_sq_index_le F
  calc
    NumberField.classNumber F * (Subgroup.square (𝓞 F)ˣ).index
        ≤ ((NumberField.discr F).natAbs * 4 ^ finrank ℚ F) * 2 ^ finrank ℚ F :=
          Nat.mul_le_mul hclass hunits
    _ = (NumberField.discr F).natAbs * 8 ^ finrank ℚ F := by
      rw [mul_assoc, four_pow_mul_two_pow]

/-- Monotone form of `TauCeti.NumberField.classNumber_mul_units_sq_index_le`: if `|d_F| ≤ D`
and `[F : ℚ] ≤ n`, then
`h_F * [O_F^× : (O_F^×)^2] ≤ D * 8^n`. -/
theorem classNumber_mul_units_sq_index_le_of_abs_discr_le_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {D n : ℕ}
    (hD : |NumberField.discr F| ≤ D) (hn : finrank ℚ F ≤ n) :
    NumberField.classNumber F * (Subgroup.square (𝓞 F)ˣ).index ≤ D * 8 ^ n := by
  have hclass : NumberField.classNumber F ≤ D * 4 ^ n :=
    classNumber_le_nat_of_abs_discr_le_of_finrank_le F hD hn
  have hunits : (Subgroup.square (𝓞 F)ˣ).index ≤ 2 ^ n :=
    units_sq_index_le_of_finrank_le F hn
  calc
    NumberField.classNumber F * (Subgroup.square (𝓞 F)ˣ).index
        ≤ (D * 4 ^ n) * 2 ^ n := Nat.mul_le_mul hclass hunits
    _ = D * 8 ^ n := by
      rw [mul_assoc, four_pow_mul_two_pow]

/-- If `|d_F| ≤ D`, then
`h_F * [O_F^× : (O_F^×)^2] ≤ D * 8^[F:ℚ]`. -/
theorem classNumber_mul_units_sq_index_le_of_abs_discr_le
    (F : Type*) [Field F] [NumberField F] {D : ℕ} (hD : |NumberField.discr F| ≤ D) :
    NumberField.classNumber F * (Subgroup.square (𝓞 F)ˣ).index ≤
      D * 8 ^ finrank ℚ F :=
  classNumber_mul_units_sq_index_le_of_abs_discr_le_of_finrank_le F hD le_rfl

/-- If `[F : ℚ] ≤ n`, then
`h_F * [O_F^× : (O_F^×)^2] ≤ |d_F| * 8^n`. -/
theorem classNumber_mul_units_sq_index_le_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {n : ℕ} (hn : finrank ℚ F ≤ n) :
    NumberField.classNumber F * (Subgroup.square (𝓞 F)ˣ).index ≤
      (NumberField.discr F).natAbs * 8 ^ n :=
  classNumber_mul_units_sq_index_le_of_abs_discr_le_of_finrank_le F
    (abs_discr_le_natAbs F) hn

/-- The same product bound expressed using the elementary-2 quotient of units:
`h_F * #(O_F^×/(O_F^×)^2) ≤ |d_F| * 8^[F:ℚ]`. -/
theorem classNumber_mul_card_units_elementaryTwoQuotient_le (F : Type*) [Field F] [NumberField F] :
    NumberField.classNumber F * Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) ≤
      (NumberField.discr F).natAbs * 8 ^ finrank ℚ F := by
  rw [TauCeti.card_elementaryTwoQuotient_eq_index_square]
  exact classNumber_mul_units_sq_index_le F

/-- Monotone elementary-2 quotient form: if `|d_F| ≤ D` and `[F : ℚ] ≤ n`, then
`h_F * #(O_F^×/(O_F^×)^2) ≤ D * 8^n`. -/
theorem classNumber_mul_card_units_elementaryTwoQuotient_le_of_abs_discr_le_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {D n : ℕ}
    (hD : |NumberField.discr F| ≤ D) (hn : finrank ℚ F ≤ n) :
    NumberField.classNumber F * Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) ≤
      D * 8 ^ n := by
  rw [TauCeti.card_elementaryTwoQuotient_eq_index_square]
  exact classNumber_mul_units_sq_index_le_of_abs_discr_le_of_finrank_le F hD hn

/-- If `|d_F| ≤ D`, then
`h_F * #(O_F^×/(O_F^×)^2) ≤ D * 8^[F:ℚ]`. -/
theorem classNumber_mul_card_units_elementaryTwoQuotient_le_of_abs_discr_le
    (F : Type*) [Field F] [NumberField F] {D : ℕ} (hD : |NumberField.discr F| ≤ D) :
    NumberField.classNumber F * Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) ≤
      D * 8 ^ finrank ℚ F := by
  rw [TauCeti.card_elementaryTwoQuotient_eq_index_square]
  exact classNumber_mul_units_sq_index_le_of_abs_discr_le F hD

/-- If `[F : ℚ] ≤ n`, then
`h_F * #(O_F^×/(O_F^×)^2) ≤ |d_F| * 8^n`. -/
theorem classNumber_mul_card_units_elementaryTwoQuotient_le_of_finrank_le
    (F : Type*) [Field F] [NumberField F] {n : ℕ} (hn : finrank ℚ F ≤ n) :
    NumberField.classNumber F * Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 F)ˣ) ≤
      (NumberField.discr F).natAbs * 8 ^ n := by
  rw [TauCeti.card_elementaryTwoQuotient_eq_index_square]
  exact classNumber_mul_units_sq_index_le_of_finrank_le F hn

/-! ### Quadratic square-root specializations

For a quadratic number field `K = ℚ(x)` presented by an algebraic-integer square root
`x² = a ∈ ℤ` with `x ∉ ℚ`, the quadratic discriminant bound
`TauCeti.NumberField.abs_discr_le_of_sq_intCast` gives `|d_K| ≤ 4·|a|`, and composing it with the
bounds above yields the closed forms `h_K ≤ 64·|a|` and
`h_K · [O_K^× : (O_K^×)²] ≤ 256·|a|`. -/

private lemma intCast_four_mul_natAbs (a : ℤ) : ((4 * a.natAbs : ℕ) : ℤ) = 4 * |a| := by
  rw [Nat.cast_mul, Int.abs_eq_natAbs]
  norm_num

private lemma four_mul_natAbs_mul_four_sq (a : ℤ) :
    4 * a.natAbs * 4 ^ 2 = 64 * a.natAbs := by
  omega

private lemma four_mul_natAbs_mul_eight_sq (a : ℤ) :
    4 * a.natAbs * 8 ^ 2 = 256 * a.natAbs := by
  omega

/-- **Quadratic square-root class-number bound.** If `K` is a quadratic number field
generated by an algebraic integer `x` with `x² = a ∈ ℤ` and `x ∉ ℚ`, then
`h_K ≤ 64·|a|`. This is the specialization of the general effective class-number bound
using the square-root discriminant estimate `|d_K| ≤ 4·|a|` and `[K : ℚ] = 2`. -/
theorem classNumber_le_of_sq_intCast {K : Type*} [Field K] [NumberField K]
    {x : K} {a : ℤ} (hfin : finrank ℚ K = 2)
    (hx2 : x ^ 2 = algebraMap ℤ K a) (hx : x ∉ (algebraMap ℚ K).range) :
    (NumberField.classNumber K : ℝ) ≤ 64 * |(a : ℝ)| := by
  have hD : |(NumberField.discr K : ℝ)| ≤ 4 * |(a : ℝ)| := by
    exact_mod_cast abs_discr_le_int_of_sq_intCast hfin hx2 hx
  have hclass :
      (NumberField.classNumber K : ℝ) ≤ (4 * |(a : ℝ)|) * 4 ^ 2 :=
    classNumber_le_of_abs_discr_le_of_finrank_le K hD (le_of_eq hfin)
  nlinarith [hclass]

/-- Natural-number form of `TauCeti.NumberField.classNumber_le_of_sq_intCast`:
for a quadratic number field generated by an algebraic integer square root `x² = a`,
`h_K ≤ 64 * a.natAbs`. -/
theorem classNumber_le_natAbs_of_sq_intCast {K : Type*} [Field K] [NumberField K]
    {x : K} {a : ℤ} (hfin : finrank ℚ K = 2)
    (hx2 : x ^ 2 = algebraMap ℤ K a) (hx : x ∉ (algebraMap ℚ K).range) :
    NumberField.classNumber K ≤ 64 * a.natAbs := by
  have hD : |NumberField.discr K| ≤ (4 * a.natAbs : ℕ) := by
    rw [intCast_four_mul_natAbs]
    exact abs_discr_le_int_of_sq_intCast hfin hx2 hx
  have hclass :=
    classNumber_le_nat_of_abs_discr_le_of_finrank_le K hD (le_of_eq hfin)
  rw [← four_mul_natAbs_mul_four_sq]
  exact hclass

/-- A version of `TauCeti.NumberField.classNumber_le_of_sq_intCast` with a separate
natural-number bound for `|a|`. -/
theorem classNumber_le_of_sq_intCast_of_natAbs_le {K : Type*} [Field K] [NumberField K]
    {x : K} {a : ℤ} {A : ℕ} (hfin : finrank ℚ K = 2)
    (hx2 : x ^ 2 = algebraMap ℤ K a) (hx : x ∉ (algebraMap ℚ K).range) (hA : a.natAbs ≤ A) :
    NumberField.classNumber K ≤ 64 * A :=
  (classNumber_le_natAbs_of_sq_intCast hfin hx2 hx).trans (Nat.mul_le_mul_left 64 hA)

/-- **Quadratic square-root class-number/unit-square product bound.** If `K` is a quadratic
number field generated by an algebraic integer `x` with `x² = a ∈ ℤ` and `x ∉ ℚ`, then
`h_K * [O_K^× : (O_K^×)^2] ≤ 256 * |a|`. This is the specialization of the general product
bound using `|d_K| ≤ 4 * |a|` and `[K : ℚ] = 2`. -/
theorem classNumber_mul_units_sq_index_le_natAbs_of_sq_intCast
    {K : Type*} [Field K] [NumberField K] {x : K} {a : ℤ}
    (hfin : finrank ℚ K = 2) (hx2 : x ^ 2 = algebraMap ℤ K a) (hx : x ∉ (algebraMap ℚ K).range) :
    NumberField.classNumber K * (Subgroup.square (𝓞 K)ˣ).index ≤ 256 * a.natAbs := by
  have hD : |NumberField.discr K| ≤ (4 * a.natAbs : ℕ) := by
    rw [intCast_four_mul_natAbs]
    exact abs_discr_le_int_of_sq_intCast hfin hx2 hx
  have hprod :=
    classNumber_mul_units_sq_index_le_of_abs_discr_le_of_finrank_le K hD (le_of_eq hfin)
  rw [← four_mul_natAbs_mul_eight_sq]
  exact hprod

/-- A version of
`TauCeti.NumberField.classNumber_mul_units_sq_index_le_natAbs_of_sq_intCast` with a separate
natural-number bound for `|a|`. -/
theorem classNumber_mul_units_sq_index_le_of_sq_intCast_of_natAbs_le
    {K : Type*} [Field K] [NumberField K] {x : K} {a : ℤ} {A : ℕ}
    (hfin : finrank ℚ K = 2) (hx2 : x ^ 2 = algebraMap ℤ K a)
    (hx : x ∉ (algebraMap ℚ K).range) (hA : a.natAbs ≤ A) :
    NumberField.classNumber K * (Subgroup.square (𝓞 K)ˣ).index ≤ 256 * A :=
  (classNumber_mul_units_sq_index_le_natAbs_of_sq_intCast hfin hx2 hx).trans
    (Nat.mul_le_mul_left 256 hA)

/-- **Quadratic square-root elementary-2 quotient product bound.** If `K` is a quadratic number
field generated by an algebraic integer `x` with `x² = a ∈ ℤ` and `x ∉ ℚ`, then
`h_K * #(O_K^×/(O_K^×)^2) ≤ 256 * |a|`. This is the elementary-2 quotient form of
`TauCeti.NumberField.classNumber_mul_units_sq_index_le_natAbs_of_sq_intCast`. -/
theorem classNumber_mul_card_units_elementaryTwoQuotient_le_natAbs_of_sq_intCast
    {K : Type*} [Field K] [NumberField K] {x : K} {a : ℤ}
    (hfin : finrank ℚ K = 2) (hx2 : x ^ 2 = algebraMap ℤ K a) (hx : x ∉ (algebraMap ℚ K).range) :
    NumberField.classNumber K * Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 K)ˣ) ≤
      256 * a.natAbs := by
  rw [TauCeti.card_elementaryTwoQuotient_eq_index_square]
  exact classNumber_mul_units_sq_index_le_natAbs_of_sq_intCast hfin hx2 hx

/-- A version of
`TauCeti.NumberField.classNumber_mul_card_units_elementaryTwoQuotient_le_natAbs_of_sq_intCast`
with a separate natural-number bound for `|a|`. -/
theorem classNumber_mul_card_units_elementaryTwoQuotient_le_of_sq_intCast_of_natAbs_le
    {K : Type*} [Field K] [NumberField K] {x : K} {a : ℤ} {A : ℕ}
    (hfin : finrank ℚ K = 2) (hx2 : x ^ 2 = algebraMap ℤ K a)
    (hx : x ∉ (algebraMap ℚ K).range) (hA : a.natAbs ≤ A) :
    NumberField.classNumber K * Nat.card (TauCeti.ElementaryTwoQuotient (𝓞 K)ˣ) ≤
      256 * A :=
  (classNumber_mul_card_units_elementaryTwoQuotient_le_natAbs_of_sq_intCast hfin hx2 hx).trans
    (Nat.mul_le_mul_left 256 hA)

end TauCeti.NumberField
