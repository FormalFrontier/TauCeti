/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import TauCeti.FieldTheory.Trace
import TauCeti.NumberTheory.NumberField.Internal.QuadraticIntegralBasis
import Mathlib.Algebra.Polynomial.Monic

/-!
# An effective discriminant bound from a basis of algebraic integers

For a number field `K`, the discriminant of any `ℚ`-basis consisting of algebraic integers
is a nonzero-integer-square multiple of the field discriminant `d_K`, so it bounds `|d_K|`
from above:

`|d_K| ≤ |disc b|`  for every `ℚ`-basis `b` of `𝒪_K`-integers.

This is the elementary upper half of the effective-bounds roadmap (the deep content is the
matching Minkowski lower bound).

## Main results

* `TauCeti.NumberField.abs_discr_le_of_basis_isIntegral`: `|d_K| ≤ |disc b|` for a
  `ℚ`-basis `b` consisting of algebraic integers.

The remaining declarations are its consumer forms, converting the rational basis-discriminant
bound into the natural-number and integer-absolute-value shapes that concrete trace-form
computations (for example the roadmap's `ℚ(i)` worked example) carry:
`abs_discr_le_of_basis_isIntegral_of_abs_discr_le`,
`natAbs_discr_le_of_basis_isIntegral_of_discr_eq_int` and its `_of_natAbs_le`/`_eq_nat` variants,
and `abs_discr_le_int_of_basis_isIntegral_of_discr_eq_int_of_natAbs_le`.

The final section evaluates the bound on a quadratic square-root field: for `K = ℚ(x)` with
`x² = a ∈ ℤ` and `x ∉ ℚ`, the `{1, x}` trace-form discriminant is `4·a`, giving the closed form
`|d_K| ≤ 4·|a|` (`abs_discr_le_of_sq_intCast`, and its integer form
`abs_discr_le_int_of_sq_intCast`). This is the tool the roadmap's quadratic worked examples need:
`ℚ(i)` (`a = -1`) gives `|d_K| ≤ 4`, and `ℚ(√-5)` (`a = -5`) gives `|d_K| ≤ 20`.

## Provenance

The general algebraic-integer basis discriminant bound was migrated from
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the
formalization of L. Alpöge's disproof of the uniform-constant Erdős unit-distance
conjecture, where this was a discriminant input to a class-number bound; the statement holds
over an arbitrary number field. The quadratic closed-form bounds are local compositions of this
bound with the trace-form calculation for a square-root basis.
-/

public section

open Module

namespace TauCeti

namespace NumberField

/-- If `b` is a `ℚ`-basis of a number field `K` consisting of algebraic integers, then
`|d_K| ≤ |disc b|`. -/
theorem abs_discr_le_of_basis_isIntegral {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) :
    |(NumberField.discr K : ℚ)| ≤ |Algebra.discr ℚ (b : ι → K)| := by
  classical
  -- `c` is the canonical integral basis of `K`.
  set c := NumberField.integralBasis K with hc
  -- Reindex `c` to `ι` (both have `[K : ℚ]` elements).
  obtain ⟨e, -⟩ : ∃ _ : Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers K) ≃ ι, True := by
    refine ⟨Fintype.equivOfCardEq ?_, trivial⟩
    rw [← Module.finrank_eq_card_basis c, ← Module.finrank_eq_card_basis b]
  -- Change of basis: `disc b = (det P)² · disc c = (det P)² · d_K`, with `P = c'.toMatrix b`.
  set P : Matrix ι ι ℚ := (c.reindex e).toMatrix b with hPdef
  have hdiscc : Algebra.discr ℚ (c.reindex e) = (NumberField.discr K : ℚ) := by
    rw [Module.Basis.coe_reindex, Algebra.discr_reindex, hc, NumberField.coe_discr]
  have hP : Algebra.discr ℚ b = P.det ^ 2 * (NumberField.discr K : ℚ) := by
    rw [← hdiscc]
    convert Algebra.discr_of_matrix_vecMul (c.reindex e) P using 2
    convert (Module.Basis.toMatrix_map_vecMul (c.reindex e) b).symm using 1
  -- `P` has integer entries (the `b j` are algebraic integers), so `det P` is an integer.
  obtain ⟨d, hd⟩ : ∃ d : ℤ, P.det = d := by
    have hP_int : ∀ i j, ∃ z : ℤ, P i j = z := by
      intro i j
      obtain ⟨y, hy⟩ : ∃ y : NumberField.RingOfIntegers K, b j = algebraMap _ K y :=
        ⟨⟨b j, hb j⟩, rfl⟩
      refine ⟨(NumberField.RingOfIntegers.basis K).repr y (e.symm i), ?_⟩
      rw [hPdef, Module.Basis.toMatrix_apply, Module.Basis.repr_reindex_apply, hc, hy]
      simp
    choose f hf using hP_int
    exact ⟨(Matrix.of f).det, by simp [hf, Matrix.det_apply']⟩
  rw [hP, abs_mul, hd]
  rcases eq_or_ne d 0 with hd0 | hd0
  · exact absurd (by rw [hP, hd, hd0]; push_cast; ring)
      (Algebra.discr_not_zero_of_basis ℚ b)
  · refine le_mul_of_one_le_left (abs_nonneg _) ?_
    rw [abs_pow]
    exact one_le_pow₀ (by exact_mod_cast Int.one_le_abs hd0)

/-- If the discriminant of an algebraic-integer basis is bounded by `B`, then the number-field
discriminant is bounded by the same rational number. -/
theorem abs_discr_le_of_basis_isIntegral_of_abs_discr_le {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) {B : ℚ} (hB : |Algebra.discr ℚ (b : ι → K)| ≤ B) :
    |(NumberField.discr K : ℚ)| ≤ B :=
  (abs_discr_le_of_basis_isIntegral b hb).trans hB

/-- If the trace-form discriminant of an algebraic-integer basis computes to the integer `d`, then
the natural absolute discriminant of the number field is at most `d.natAbs`. -/
theorem natAbs_discr_le_of_basis_isIntegral_of_discr_eq_int {K : Type*} [Field K] [NumberField K]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ K)
    (hb : ∀ i, IsIntegral ℤ (b i)) {d : ℤ} (hdisc : Algebra.discr ℚ (b : ι → K) = (d : ℚ)) :
    (NumberField.discr K).natAbs ≤ d.natAbs := by
  have hq : |(NumberField.discr K : ℚ)| ≤ |(d : ℚ)| := by
    simpa [hdisc] using abs_discr_le_of_basis_isIntegral b hb
  rw [← Nat.cast_le (α := ℤ), Nat.cast_natAbs, Nat.cast_natAbs]
  exact_mod_cast hq

/-- If the trace-form discriminant of an algebraic-integer basis computes to the integer `d`, and
`d.natAbs ≤ D`, then `(NumberField.discr K).natAbs ≤ D`. -/
theorem natAbs_discr_le_of_basis_isIntegral_of_discr_eq_int_of_natAbs_le
    {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i)) {d : ℤ} {D : ℕ}
    (hdisc : Algebra.discr ℚ (b : ι → K) = (d : ℚ)) (hd : d.natAbs ≤ D) :
    (NumberField.discr K).natAbs ≤ D :=
  (natAbs_discr_le_of_basis_isIntegral_of_discr_eq_int b hb hdisc).trans hd

/-- If the trace-form discriminant of an algebraic-integer basis computes to the natural number
`D`, then `(NumberField.discr K).natAbs ≤ D`. -/
theorem natAbs_discr_le_of_basis_isIntegral_of_discr_eq_nat
    {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i)) {D : ℕ}
    (hdisc : Algebra.discr ℚ (b : ι → K) = (D : ℚ)) : (NumberField.discr K).natAbs ≤ D := by
  exact natAbs_discr_le_of_basis_isIntegral_of_discr_eq_int_of_natAbs_le
    b hb (d := (D : ℤ)) (by simpa using hdisc) (by simp)

/-- If the trace-form discriminant of an algebraic-integer basis computes to an integer `d` with
`d.natAbs ≤ D`, the same natural-number discriminant bound may be read as an integer absolute-value
bound. -/
theorem abs_discr_le_int_of_basis_isIntegral_of_discr_eq_int_of_natAbs_le
    {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i)) {d : ℤ} {D : ℕ}
    (hdisc : Algebra.discr ℚ (b : ι → K) = (d : ℚ)) (hd : d.natAbs ≤ D) :
    |NumberField.discr K| ≤ (D : ℤ) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast
    natAbs_discr_le_of_basis_isIntegral_of_discr_eq_int_of_natAbs_le b hb hdisc hd

/-- For a quadratic number field `K` and an element `x : K` whose square is an integer
`a` and which is not rational, the field discriminant satisfies `|d_K| ≤ 4·|a|`. -/
theorem abs_discr_le_of_sq_intCast {K : Type*} [Field K] [NumberField K]
    {x : K} {a : ℤ} (hfin : finrank ℚ K = 2)
    (hx2 : x ^ 2 = algebraMap ℤ K a) (hx : x ∉ (algebraMap ℚ K).range) :
    |(NumberField.discr K : ℚ)| ≤ 4 * |(a : ℚ)| := by
  classical
  -- The square root also satisfies `x² = (a : ℚ)` through the `ℚ`-algebra structure.
  have hcast : algebraMap ℤ K a = algebraMap ℚ K (a : ℚ) := by
    rw [IsScalarTower.algebraMap_apply ℤ ℚ K, eq_intCast (algebraMap ℤ ℚ) a]
  have hx2' : x ^ 2 = algebraMap ℚ K (a : ℚ) := hx2.trans hcast
  -- `x` is an algebraic integer: a root of `X² - a`.
  have hxint : IsIntegral ℤ x := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C a,
      Polynomial.monic_X_pow_sub_C a (by norm_num), ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, ← hx2, sub_self]
  -- The shared `{1, x}` rational basis of the quadratic field, whose vectors are algebraic
  -- integers.
  obtain ⟨b, hbcoe, hb_int⟩ :=
    Internal.exists_basis_eq_one_self_of_notMem_range_of_isIntegral hfin hx hxint
  -- Combine the effective bound with the trace-form evaluation `disc ℚ {1, x} = 4·a`.
  have hmain := TauCeti.NumberField.abs_discr_le_of_basis_isIntegral b hb_int
  rw [hbcoe, TauCeti.Algebra.discr_one_elem_eq_of_sq_algebraMap hfin hx2' hx] at hmain
  simpa [abs_mul] using hmain

/-- The integer form of the quadratic discriminant bound: `|d_K| ≤ 4·|a|` over `ℤ`, for a
quadratic field `K` with `x² = a ∈ ℤ` and `x ∉ ℚ`. -/
theorem abs_discr_le_int_of_sq_intCast {K : Type*} [Field K] [NumberField K]
    {x : K} {a : ℤ} (hfin : finrank ℚ K = 2)
    (hx2 : x ^ 2 = algebraMap ℤ K a) (hx : x ∉ (algebraMap ℚ K).range) :
    |NumberField.discr K| ≤ 4 * |a| := by
  exact_mod_cast abs_discr_le_of_sq_intCast hfin hx2 hx

end TauCeti.NumberField
