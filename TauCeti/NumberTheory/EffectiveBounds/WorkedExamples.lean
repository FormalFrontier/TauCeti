/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import TauCeti.NumberTheory.EffectiveBounds.ClassNumber.Basic
import TauCeti.NumberTheory.EffectiveBounds.Discriminant.Equality
import TauCeti.FieldTheory.Trace
import TauCeti.NumberTheory.NumberField.Internal.QuadraticIntegralBasis
import Mathlib.FieldTheory.KummerPolynomial

/-!
# Worked examples: the effective bounds on the named quadratic fields

The effective-bounds roadmap keeps its estimates honest with two arithmetic worked examples,
each asking that a general bound be exercised on a *named* number field rather than a
same-shape analogue:

* the discriminant bound recovers `|d_{ℚ(i)}| = 4` from the integral basis `{1, i}`;
* the class-number bound is non-vacuous on `ℚ(√-5)`, giving `h ≤ 64·5`.

This file realises both worked examples on concrete `NumberField` instances, each exercising
the repo's own effective-bound machinery rather than citing a closed formula from Mathlib.

For `ℚ(√-5)` we take `AdjoinRoot (X² + 5)` over `ℚ` (a field because `X² + 5` is irreducible,
having no rational root), a degree-two number field with a square root of `-5`, and feed it to
`TauCeti.NumberField.classNumber_le_natAbs_of_sq_intCast`.

For `ℚ(i)` we take the fourth cyclotomic field `CyclotomicField 4 ℚ`, whose primitive fourth
root of unity `ζ` satisfies `ζ² = -1` and generates `ℚ(i)`. The pair `{1, ζ}` is a `ℤ`-basis
of the ring of integers (Mathlib's integral power basis of a cyclotomic `𝒪_K`), so the repo's
equality companion of the discriminant bound
(`TauCeti.NumberField.discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int`) turns the
trace-form evaluation `disc ℚ {1, ζ} = 4·(-1) = -4`
(`TauCeti.Algebra.discr_one_elem_eq_of_sq_algebraMap`) into `d_{ℚ(i)} = -4` exactly, whence
`|d_{ℚ(i)}| = 4`.

## Main results

* `TauCeti.NumberField.WorkedExamples.classNumber_adjoinRoot_sqrt_neg_five_le`: `h ≤ 320` for
  `ℚ(√-5)`.
* `TauCeti.NumberField.WorkedExamples.discr_cyclotomicField_four`: `d_{ℚ(i)} = -4`.
* `TauCeti.NumberField.WorkedExamples.abs_discr_cyclotomicField_four`: `|d_{ℚ(i)}| = 4`.
* `TauCeti.NumberField.WorkedExamples.natAbs_discr_cyclotomicField_four`: `|d_{ℚ(i)}| = 4`.

## Provenance

No formal code is vendored. The effective bounds consumed here (`classNumber_le_bound`, the
quadratic class-number corollary, the discriminant-equality companion, and the square-root
trace-form diagonalisation) carry their own attribution to `kim-em/erdos-unit-distance`; the
`NumberField` constructions for `ℚ(√-5)` and `ℚ(i)` and the arithmetic specialisations are new.
-/

public section

open Polynomial Module
open scoped NumberField

namespace TauCeti.NumberField.WorkedExamples

/-! ### `ℚ(√-5)`: the class-number bound is non-vacuous -/

/-- `X² + 5` is irreducible over `ℚ`: a monic quadratic with no rational root (a rational
square is nonnegative, but `-5 < 0`). -/
instance : Fact (Irreducible (X ^ 2 - C (-5 : ℚ))) := ⟨by
  exact (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).mpr
    (fun q hq => by nlinarith [sq_nonneg q])⟩

/-- **The class-number bound on `ℚ(√-5)`.** The class number of `ℚ(√-5)`, modelled as
`AdjoinRoot (X² + 5)`, is at most `64·5 = 320`; this is the roadmap's non-vacuity worked
example for the effective class-number bound. -/
theorem classNumber_adjoinRoot_sqrt_neg_five_le :
    NumberField.classNumber (AdjoinRoot (X ^ 2 - C (-5 : ℚ))) ≤ 320 := by
  set f : ℚ[X] := X ^ 2 - C (-5 : ℚ) with hf
  have hfne : f ≠ 0 := (monic_X_pow_sub_C _ (two_ne_zero)).ne_zero
  -- `[K : ℚ] = 2`.
  have hfin : finrank ℚ (AdjoinRoot f) = 2 := by
    rw [(AdjoinRoot.powerBasis hfne).finrank, AdjoinRoot.powerBasis_dim hfne, hf,
      natDegree_X_pow_sub_C]
  -- The image of `AdjoinRoot.root f` is a square root of `-5`.
  have hx2 : (AdjoinRoot.root f) ^ 2 = algebraMap ℤ (AdjoinRoot f) (-5 : ℤ) := by
    have hroot := AdjoinRoot.eval₂_root f
    rw [hf, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, ← AdjoinRoot.algebraMap_eq, sub_eq_zero]
      at hroot
    rw [hroot, IsScalarTower.algebraMap_apply ℤ ℚ (AdjoinRoot f)]
    norm_num
  -- The root is not rational: else `-5` would be a rational square.
  have hx : AdjoinRoot.root f ∉ (algebraMap ℚ (AdjoinRoot f)).range := by
    rintro ⟨q, hq⟩
    have h1 : algebraMap ℚ (AdjoinRoot f) (q ^ 2) = algebraMap ℚ (AdjoinRoot f) (-5 : ℚ) := by
      rw [map_pow, hq, hx2, IsScalarTower.algebraMap_apply ℤ ℚ (AdjoinRoot f)]; norm_num
    nlinarith [sq_nonneg q, (algebraMap ℚ (AdjoinRoot f)).injective h1]
  have := classNumber_le_natAbs_of_sq_intCast hfin hx2 hx
  simpa using this

/-! ### `ℚ(i)`: the discriminant bound recovers `|d| = 4` from the basis `{1, i}` -/

/-- The `ℤ`-span of any set containing `1` and a primitive fourth root of unity is all of `𝓞 K`:
those two elements are the vectors of the integral power basis. -/
private theorem span_eq_top_of_one_mem_of_toInteger_mem {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {4} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ 4) {s : Set (𝓞 K)}
    (h1 : (1 : 𝓞 K) ∈ s) (hi : hζ.toInteger ∈ s) : Submodule.span ℤ s = ⊤ := by
  set pb := hζ.integralPowerBasis with hpb
  have hdim : pb.dim = 2 := by rw [hpb, hζ.integralPowerBasis_dim]; decide
  -- Every vector of the integral power basis is `ζ ^ 0 = 1` or `ζ ^ 1 = ζ`.
  have hpow : ∀ i : Fin pb.dim, pb.basis i ∈ Submodule.span ℤ s := by
    intro i
    rw [pb.basis_eq_pow, hζ.integralPowerBasis_gen]
    have hlt : (i : ℕ) < 2 := hdim ▸ i.isLt
    rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h | h <;> rw [h]
    · rw [pow_zero]; exact Submodule.subset_span h1
    · rw [pow_one]; exact Submodule.subset_span hi
  exact le_antisymm le_top (le_trans (le_of_eq pb.basis.span_eq.symm)
    (Submodule.span_le.mpr (Set.range_subset_iff.mpr hpow)))

/-- The discriminant of a fourth cyclotomic field is `-4`, recovered from the integral basis
`{1, i}`: the equality companion of the effective discriminant bound turns the trace-form value
`disc ℚ {1, i} = 4·(-1) = -4` into the field discriminant. -/
private theorem discr_eq_neg_four_of_isCyclotomicExtension {K : Type*} [Field K]
    [NumberField K] [IsCyclotomicExtension {4} ℚ K] :
    NumberField.discr K = -4 := by
  classical
  set ζ : K := IsCyclotomicExtension.zeta 4 ℚ K with hζdef
  have hζ : IsPrimitiveRoot ζ 4 := IsCyclotomicExtension.zeta_spec 4 ℚ K
  -- `[ℚ(i) : ℚ] = φ 4 = 2`.
  have hfin : finrank ℚ K = 2 := by
    rw [IsCyclotomicExtension.finrank K
      (Polynomial.cyclotomic.irreducible_rat (n := 4) (by norm_num))]
    decide
  -- The primitive fourth root of unity is a square root of `-1`: its square is a primitive
  -- second root of unity.
  have hζ2K : ζ ^ 2 = -1 := (hζ.pow (by norm_num) (by norm_num)).eq_neg_one_of_two_right
  have hζ2 : ζ ^ 2 = algebraMap ℚ K (-1) := by rw [hζ2K]; simp
  -- `i` is not rational, else `-1` would be a rational square.
  have hζnotmem : ζ ∉ (algebraMap ℚ K).range := by
    rintro ⟨q, hq⟩
    have hcast : algebraMap ℚ K (q ^ 2) = algebraMap ℚ K (-1) := by rw [map_pow, hq]; exact hζ2
    have hq2 : q ^ 2 = -1 := RingHom.injective _ hcast
    nlinarith [sq_nonneg q]
  have hζint : IsIntegral ℤ ζ := hζ.isIntegral (by norm_num)
  -- `{1, i}` is a `ℚ`-basis of algebraic integers.
  rcases Internal.exists_basis_eq_one_self_of_notMem_range_of_isIntegral hfin hζnotmem hζint with
    ⟨b, hbcoe, hb_int⟩
  -- `{1, i}` is the integral power basis of `𝒪_{ℚ(i)}`, so its `ℤ`-span is all of `𝒪_{ℚ(i)}`.
  have hb0 : b 0 = (1 : K) := by rw [hbcoe]; rfl
  have hb1 : b 1 = ζ := by rw [hbcoe]; rfl
  have hspan : Submodule.span ℤ (Set.range fun i => (⟨b i, hb_int i⟩ : 𝓞 K)) = ⊤ :=
    span_eq_top_of_one_mem_of_toInteger_mem hζ ⟨0, Subtype.ext hb0⟩ ⟨1, Subtype.ext hb1⟩
  -- The trace form evaluates `disc ℚ {1, i} = -4`.
  have hdiscr : Algebra.discr ℚ (b : Fin 2 → K) = ((-4 : ℤ) : ℚ) := by
    rw [hbcoe, TauCeti.Algebra.discr_one_elem_eq_of_sq_algebraMap hfin hζ2 hζnotmem]
    push_cast
    norm_num
  exact discr_eq_of_basis_isIntegral_of_span_eq_top_of_discr_eq_int b hb_int hspan hdiscr

/-- **The discriminant of `ℚ(i)`.** Recovering `d_{ℚ(i)} = -4` from the integral basis
`{1, i}` of the fourth cyclotomic field: the equality companion of the effective discriminant
bound turns the trace-form value `disc ℚ {1, i} = 4·(-1) = -4` into the field discriminant. -/
@[simp]
theorem discr_cyclotomicField_four : NumberField.discr (CyclotomicField 4 ℚ) = -4 := by
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  exact discr_eq_neg_four_of_isCyclotomicExtension

/-- **The integer absolute discriminant of `ℚ(i)`.** The fourth cyclotomic field has
`|d_{ℚ(i)}| = 4`, obtained from the signed discriminant worked example. -/
theorem abs_discr_cyclotomicField_four :
    |NumberField.discr (CyclotomicField 4 ℚ)| = (4 : ℤ) := by
  rw [discr_cyclotomicField_four]
  norm_num

/-- **The absolute discriminant of `ℚ(i)`.** The fourth cyclotomic field has absolute
discriminant `4`, obtained from the signed discriminant worked example. -/
theorem natAbs_discr_cyclotomicField_four :
    (NumberField.discr (CyclotomicField 4 ℚ)).natAbs = 4 := by
  rw [discr_cyclotomicField_four]
  norm_num

end TauCeti.NumberField.WorkedExamples
