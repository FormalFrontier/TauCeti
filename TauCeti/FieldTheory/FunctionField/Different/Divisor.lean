/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Basic
public import TauCeti.FieldTheory.FunctionField.Divisor.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre
public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.AlmostEverywhere
public import TauCeti.RingTheory.DedekindDomain.Different

/-!
# The different divisor of an extension of algebraic function fields

Let `F' / k'` be an extension of the algebraic function field `F / k` with `F' / F` finite and
separable.  Stichtenoth attaches to it the **different divisor**

`Diff(F' / F) = ∑_{P'} d(P' ∣ P) · P'`

of `F' / k'`, the effective divisor whose coefficient at a place `P'` is the different exponent
of `P'` over the place `P = P'.restrict k F` below it.  The exponents themselves are
`TauCeti.Place.differentExponent`; what this file supplies is the finiteness that turns the
family into a divisor, and the divisor itself.

Finiteness is Stichtenoth's Remark 3.4.4, and it is where the almost-everywhere theory of
integral bases is spent.  Fix an `F`-basis `b` of `F'`.  At a place `P` at which both `b` and its
trace-dual basis are integral bases, the local model `𝒪'_P` is the `𝒪_P`-span of `b` and its
complementary module is the span of the trace dual, so the two coincide and the different ideal
of `𝒪_P ⊆ 𝒪'_P` is the unit ideal: every place of `F' / k'` over such a `P` has different
exponent `0`.  All but finitely many places of `F / k` are of that kind
(`TauCeti.Place.finite_setOf_not_isIntegralBasis`), and each of the remaining ones carries only
finitely many places of `F' / k'` (`TauCeti.Place.finite_setOf_restrict_eq`), so only finitely
many `P'` have a nonzero exponent.

The step that reads the unit different ideal off a self-dual integral basis has no function-field
content and is `TauCeti.differentIdeal_eq_top_of_span_eq_one`, in
`TauCeti/RingTheory/DedekindDomain/Different.lean`; what this file adds to it is the place at
which to apply it.

No affine model of `F / k` is used, so no normalization theorem is needed: the argument runs over
the local models `𝒪_P ⊆ 𝒪'_P` only.  In particular this is not an instance of
`Algebra.finite_compl_unramifiedLocus`, which bounds the ramification locus of a single extension
of Dedekind domains — here the extension varies with the place, and each individual local model,
being semi-local, has a finite ramification locus for trivial reasons.

## Main definitions

* `TauCeti.Divisor.different`: the different divisor `Diff(F' / F)` (Stichtenoth,
  Definition 3.4.3).

## Main results

* `TauCeti.Place.differentIdeal_eq_top_of_isIntegralBasis`: the different ideal of the local
  model at `P` is the unit ideal as soon as some basis and its trace dual are integral bases
  at `P`.
* `TauCeti.Place.finite_setOf_differentExponent_ne_zero`: only finitely many places of `F' / k'`
  have a nonzero different exponent (Stichtenoth, Remark 3.4.4).
* `TauCeti.Divisor.zero_le_different`: the different divisor is effective, `Diff(F' / F) ≥ 0`.
* `TauCeti.Divisor.mem_support_different_iff` and `TauCeti.Divisor.different_eq_zero_iff`: its
  support consists of the places where the local model is ramified (Stichtenoth,
  Corollary 3.5.5), so it vanishes exactly when `F' / F` is everywhere unramified.

## Implementation notes

The upper field `F' / k'` is an explicit argument of `TauCeti.Divisor.different` and the lower
field `F / k` is read off the function-field hypothesis, the convention of
`TauCeti.Divisor.conorm`.  That hypothesis `IsFunctionField k F` is an explicit argument rather
than a typeclass, following the rest of this directory; it is what makes the support finite, so
it cannot be avoided in the definition, and since it is a `Prop`, two spellings of it give the
same divisor.

Like the conorm, the different divisor is built from its coefficients through
`Finsupp.ofSupportFinite`, which makes the coefficient formula definitional.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 3.4.3, Remark 3.4.4 and Corollary 3.5.5.
-/

public section

open Module

namespace TauCeti

open AlgebraicGeometry

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F'] [Algebra k F] [Algebra F F']

namespace Place

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section LocalModel

variable [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (P : Place k F)

/-- **The different ideal of the local model at a place with an integral basis is trivial.**  If
an `F`-basis `b` of `F'` and its trace dual are both integral bases at `P`, then `𝒪'_P` is its own
complementary module, so `differentIdeal 𝒪_P 𝒪'_P` is the unit ideal. -/
theorem differentIdeal_eq_top_of_isIntegralBasis {ι : Type*} [Finite ι] [DecidableEq ι]
    {b : Basis ι F F'} (hb : P.IsIntegralBasis F' b) (hb' : P.IsIntegralBasis F' b.traceDual) :
    differentIdeal P.integers (integralClosure P.integers F') = ⊤ :=
  differentIdeal_eq_top_of_span_eq_one P.integers F b
    (by
      rw [Subalgebra.restrictScalars_one]
      exact (isIntegralBasis_iff_span_eq F' P b).mp hb)
    (by
      rw [Subalgebra.restrictScalars_one]
      exact (isIntegralBasis_iff_span_eq F' P b.traceDual).mp hb')

end LocalModel

section Extension

variable [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']
variable [Algebra.IsSeparable F F']

variable (k F)

/-- **A place with an integral basis below it is not in the different.**  If an `F`-basis of `F'`
and its trace dual are integral bases at the place below `P'`, then `d(P' ∣ P) = 0`. -/
theorem differentExponent_eq_zero_of_isIntegralBasis (P' : Place k' F') {ι : Type*} [Finite ι]
    [DecidableEq ι] {b : Basis ι F F'} (hb : (P'.restrict k F).IsIntegralBasis F' b)
    (hb' : (P'.restrict k F).IsIntegralBasis F' b.traceDual) :
    differentExponent k F P' = 0 := by
  by_contra h
  have hdvd := (pow_dvd_differentIdeal_iff_le_differentExponent (n := 1) k F P').mpr
    (Nat.one_le_iff_ne_zero.mpr h)
  rw [pow_one, differentIdeal_eq_top_of_isIntegralBasis _ hb hb', Ideal.dvd_iff_le,
    top_le_iff] at hdvd
  exact (centerIntegralClosure k F P').isPrime.ne_top hdvd

/-- **Only finitely many places have a nonzero different exponent** (Stichtenoth,
Remark 3.4.4).  A basis of `F' / F` and its trace dual are integral bases at all but finitely many
places of `F / k`, no place above such a place contributes, and each of the finitely many
remaining places of `F / k` has only finitely many places of `F' / k'` above it. -/
theorem finite_setOf_differentExponent_ne_zero (hF : IsFunctionField k F) :
    {P' : Place k' F' | differentExponent k F P' ≠ 0}.Finite := by
  classical
  set b := finBasis F F'
  have hbad := (finite_setOf_not_isIntegralBasis hF b).union
    (finite_setOf_not_isIntegralBasis hF b.traceDual)
  refine (hbad.biUnion fun P _ ↦ finite_setOf_restrict_eq (k' := k') (F' := F') k F P).subset
    fun P' hP' ↦ Set.mem_biUnion (x := P'.restrict k F) ?_ rfl
  by_contra hgood
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hgood
  exact hP' (differentExponent_eq_zero_of_isIntegralBasis k F P' hgood.1 hgood.2)

end Extension

end Place

namespace Divisor

section Extension

variable [Field k'] [Algebra k k'] [Algebra k' F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [FiniteDimensional F F']
variable [Algebra.IsSeparable F F']

variable (k' F')

/-- The different exponents form a finitely supported family of coefficients. -/
private theorem finite_support_differentCoeff (hF : IsFunctionField k F) :
    (Function.support fun P' : Place k' F' ↦ (Place.differentExponent k F P' : ℤ)).Finite :=
  (Place.finite_setOf_differentExponent_ne_zero (k' := k') (F' := F') k F hF).subset
    fun _ hP' ↦ by simpa using hP'

/-- **The different divisor** `Diff(F' / F) = ∑_{P'} d(P' ∣ P) · P'` of an extension `F' / k'` of
an algebraic function field `F / k` with `F' / F` finite and separable (Stichtenoth,
Definition 3.4.3): the divisor of `F' / k'` whose coefficient at a place `P'` is the different
exponent of `P'` over the place below it. -/
noncomputable def different (hF : IsFunctionField k F) : Divisor k' F' :=
  Finsupp.ofSupportFinite (fun P' : Place k' F' ↦ (Place.differentExponent k F P' : ℤ))
    (finite_support_differentCoeff k' F' hF)

/-- **The defining coefficient formula of the different divisor**: the coefficient of
`Diff(F' / F)` at a place `P'` is the different exponent `d(P' ∣ P)`. -/
@[simp]
theorem coeff_different (hF : IsFunctionField k F) (P' : Place k' F') :
    (different k' F' hF).coeff P' = Place.differentExponent k F P' := (rfl)

/-- **The different divisor is effective**, `Diff(F' / F) ≥ 0` (Stichtenoth, Definition 3.4.3):
its coefficients are different exponents, which are natural numbers. -/
theorem zero_le_different (hF : IsFunctionField k F) : 0 ≤ different k' F' hF :=
  WeilDivisor.le_iff.mpr fun P' ↦ by
    rw [WeilDivisor.coeff_zero, coeff_different]
    exact Int.natCast_nonneg _

/-- The degree of the different divisor is nonnegative. -/
theorem degree_different_nonneg (hF : IsFunctionField k F) :
    0 ≤ degree (different k' F' hF) :=
  degree_nonneg (zero_le_different k' F' hF)

/-- **The support of the different divisor is the ramification locus** (Stichtenoth,
Corollary 3.5.5): a place lies in it exactly when the local model is ramified there, in Mathlib's
`Algebra.IsUnramifiedAt` sense, which asks for a separable residue extension as well as
`e(P' ∣ P) = 1`. -/
theorem mem_support_different_iff (hF : IsFunctionField k F) {P' : Place k' F'} :
    P' ∈ (different k' F' hF).support ↔ ¬ Algebra.IsUnramifiedAt ((P'.restrict k F).integers)
      (Place.centerIntegralClosure k F P').asIdeal := by
  rw [WeilDivisor.mem_support_iff, coeff_different, ne_eq, Nat.cast_eq_zero,
    Place.differentExponent_eq_zero_iff]

/-- **The different divisor vanishes exactly for an everywhere unramified extension**
(Stichtenoth, Corollary 3.5.5). -/
theorem different_eq_zero_iff (hF : IsFunctionField k F) :
    different k' F' hF = 0 ↔ ∀ P' : Place k' F',
      Algebra.IsUnramifiedAt ((P'.restrict k F).integers)
        (Place.centerIntegralClosure k F P').asIdeal := by
  refine ⟨fun h P' ↦ ?_, fun h ↦ WeilDivisor.ext fun P' ↦ ?_⟩
  · have hP' := coeff_different k' F' hF P'
    rw [h, WeilDivisor.coeff_zero] at hP'
    rw [← Place.differentExponent_eq_zero_iff]
    exact_mod_cast hP'.symm
  · rw [coeff_different, WeilDivisor.coeff_zero, Nat.cast_eq_zero,
      Place.differentExponent_eq_zero_iff]
    exact h P'

/-- **A ramified place lies in the different** (Stichtenoth, Corollary 3.5.5): this half needs no
hypothesis on the residue extension. -/
theorem mem_support_different_of_one_lt_ramificationIdx (hF : IsFunctionField k F)
    {P' : Place k' F'} (h : 1 < Place.ramificationIdx F P') :
    P' ∈ (different k' F' hF).support := by
  rw [WeilDivisor.mem_support_iff, coeff_different, ne_eq, Nat.cast_eq_zero]
  exact (Place.differentExponent_pos_of_one_lt_ramificationIdx k F P' h).ne'

end Extension

end Divisor

end TauCeti

end
