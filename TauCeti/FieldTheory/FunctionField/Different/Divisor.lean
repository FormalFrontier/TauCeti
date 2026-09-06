/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Different.Basic
public import TauCeti.FieldTheory.FunctionField.Divisor.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.AlmostEverywhere

/-!
# The different divisor of a finite separable extension

Let `F' / k'` be an extension of the algebraic function field `F / k` with `F' / F` finite and
separable.  The different exponent `d(P' ∣ P)` of
`TauCeti/FieldTheory/FunctionField/Different/Basic.lean` vanishes at all but finitely many places
of `F'`, so the formal sum

`Diff(F'/F) = ∑_{P'} d(P' ∣ P) · P'`

is a divisor of `F' / k'` — the **different divisor** (Stichtenoth, Definition 3.4.3 and
Remark 3.4.4).  It is effective, its support is exactly the set of ramified places, and Dedekind's
different theorem reads on it as `e(P' ∣ P) ≤ Diff(F'/F)(P') + 1`.

## The finiteness

Fix once and for all an `F`-basis `b` of `F'`.  At a place `P` of `F / k` at which every `b i` is
integral and at which the discriminant `disc(b) ∈ F` is a unit, the complementary module of the
local model `𝒪_P ⊆ 𝒪'_P` is `𝒪'_P` itself: Mathlib's
`isIntegral_discr_mul_of_mem_traceDual` makes `disc(b) · x` integral for every `x` of the trace
dual, and dividing by the unit `disc(b)` puts `x` back in `𝒪'_P`.  So the different ideal of the
local model is the unit ideal and `d(P' ∣ P) = 0` for every `P'` over `P`.

Both exceptional conditions hold at only finitely many `P`: the first because a fixed element of
`F'` is integral at almost every place
(`TauCeti.Place.finite_setOf_not_isIntegral`), the second because `disc(b)` is a
nonzero element of `F` and so has finitely many zeros and poles
(`TauCeti.Place.finite_setOf_ord_ne_zero`).  Each of the finitely many exceptional places carries
finitely many places of `F'` (`TauCeti.Place.finite_setOf_restrict_eq`), which bounds the support.

No local integral basis is needed for this, only integrality of the vectors of one fixed global
basis: the discriminant estimate bounds the trace dual of `𝒪'_P` by `disc(b)⁻¹ · 𝒪'_P` for any
integral spanning family, and once `disc(b)` is a unit at `P` that bound already forces equality,
whether or not `b` happens to be an `𝒪_P`-basis of `𝒪'_P`.

## Main definitions

* `TauCeti.Divisor.different`: the different divisor `Diff(F'/F)`.

## Main results

* `TauCeti.Place.finite_setOf_differentExponent_ne_zero` and
  `TauCeti.Place.finite_setOf_exists_differentExponent_ne_zero`: the different exponent vanishes
  at all but finitely many places of `F'`, and only finitely many places of `F` ramify.
* `TauCeti.Divisor.zero_le_different`: the different divisor is effective (Stichtenoth,
  Remark 3.4.4).
* `TauCeti.Divisor.mem_support_different_iff_not_isUnramifiedAt`: its support is the set of
  ramified places (Stichtenoth, Corollary 3.5.5).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 3.4.3, Remark 3.4.4 and Corollary 3.5.5.
-/

public section

open Module

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [Algebra.IsSeparable F F']

namespace Place

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

section Finiteness

variable (k F)

/-- **The different exponent vanishes at all but finitely many places** of `F' / k'`
(Stichtenoth, Proposition 3.4.2 and Definition 3.4.3).  This is what makes the different divisor
a divisor. -/
theorem finite_setOf_differentExponent_ne_zero (hF : IsFunctionField k F) :
    {P' : Place k' F' | differentExponent k F P' ≠ 0}.Finite := by
  classical
  set b : Basis (Fin (finrank F F')) F F' := finBasis F F'
  set bad : Set (Place k F) :=
    {P | P.ord (Algebra.discr F b) ≠ 0} ∪ ⋃ i, {P | ¬ IsIntegral P.integers (b i)} with hbaddef
  have hbad : bad.Finite :=
    (finite_setOf_ord_ne_zero hF _).union (Set.finite_iUnion fun i ↦
      finite_setOf_not_isIntegral hF (b i) (IsIntegral.of_finite F (b i)))
  refine (hbad.biUnion fun P _ ↦ finite_setOf_restrict_eq (k' := k') (F' := F') k F P).subset ?_
  intro Q hQ
  rw [Set.mem_iUnion₂]
  refine ⟨Q.restrict k F, ?_, rfl⟩
  by_contra hmem
  simp only [hbaddef, Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_not,
    not_exists] at hmem
  exact hQ (differentExponent_eq_zero_of_ord_discr_eq_zero k F Q hmem.2 hmem.1)

/-- **Almost every place of `F` is unramified in `F'`**: only finitely many places of `F / k`
carry an extension with nonzero different exponent.  This is the downstairs form of the
finiteness, the one a sum over the ramified places of `F` runs on. -/
theorem finite_setOf_exists_differentExponent_ne_zero (hF : IsFunctionField k F) :
    {P : Place k F | ∃ P' : Place k' F',
      P'.restrict k F = P ∧ differentExponent k F P' ≠ 0}.Finite := by
  have himg := (finite_setOf_differentExponent_ne_zero (k' := k') (F' := F') k F hF).image
    (fun P' : Place k' F' ↦ P'.restrict k F)
  have hsub : {P : Place k F | ∃ P' : Place k' F',
      P'.restrict k F = P ∧ differentExponent k F P' ≠ 0}
      ⊆ (fun P' : Place k' F' ↦ P'.restrict k F) '' {P' | differentExponent k F P' ≠ 0} := by
    rintro P ⟨P', hres, hne⟩
    exact ⟨P', hne, hres⟩
  exact himg.subset hsub

end Finiteness

end Place

namespace Divisor

open AlgebraicGeometry

variable (k' F') (hF : IsFunctionField k F)

/-- **The different divisor** `Diff(F'/F) = ∑_{P'} d(P' ∣ P) · P'` of a finite separable extension
`F' / F` of an algebraic function field (Stichtenoth, Definition 3.4.3). -/
noncomputable def different : Divisor k' F' :=
  Finsupp.ofSupportFinite (fun P' ↦ (Place.differentExponent k F P' : ℤ))
    ((Place.finite_setOf_differentExponent_ne_zero (k' := k') (F' := F') k F hF).subset
      fun _ hP' ↦ by simpa using hP')

/-- The coefficient of `P'` in the different divisor is the different exponent `d(P' ∣ P)`. -/
@[simp]
theorem coeff_different (P' : Place k' F') :
    (different k' F' hF).coeff P' = Place.differentExponent k F P' :=
  (rfl)

/-- A place lies in the support of the different divisor exactly when its different exponent is
nonzero. -/
theorem mem_support_different_iff {P' : Place k' F'} :
    P' ∈ (different k' F' hF).support ↔ Place.differentExponent k F P' ≠ 0 := by
  rw [WeilDivisor.mem_support_iff, coeff_different, ne_eq, Nat.cast_eq_zero]

/-- **The different divisor is effective** (Stichtenoth, Remark 3.4.4). -/
theorem isEffective_different : (different k' F' hF).IsEffective := by
  refine (WeilDivisor.isEffective_iff _).mpr fun P' ↦ ?_
  rw [coeff_different]
  exact Int.natCast_nonneg _

/-- Effectivity of the different divisor, in the order form the degree bound consumes. -/
theorem zero_le_different : 0 ≤ different k' F' hF :=
  WeilDivisor.isEffective_iff_zero_le.mp (isEffective_different k' F' hF)

/-- The different divisor has nonnegative degree, the input the Hurwitz genus formula reads it
through. -/
theorem zero_le_degree_different : 0 ≤ degree (different k' F' hF) :=
  degree_nonneg (zero_le_different k' F' hF)

/-- **The support of the different divisor is the set of ramified places** (Stichtenoth,
Corollary 3.5.5), ramification being read in Mathlib's `Algebra.IsUnramifiedAt` sense at the
centre of `P'` on the local model, which asks for a separable residue extension as well as
`e(P' ∣ P) = 1`. -/
theorem mem_support_different_iff_not_isUnramifiedAt {P' : Place k' F'} :
    P' ∈ (different k' F' hF).support ↔ ¬ Algebra.IsUnramifiedAt ((P'.restrict k F).integers)
      (Place.centerIntegralClosure k F P').asIdeal := by
  rw [mem_support_different_iff, ne_eq, Place.differentExponent_eq_zero_iff]

/-- **A ramified place lies in the support of the different divisor**, with no hypothesis on the
residue extension (Stichtenoth, Corollary 3.5.5). -/
theorem mem_support_different_of_one_lt_ramificationIdx {P' : Place k' F'}
    (h : 1 < Place.ramificationIdx F P') : P' ∈ (different k' F' hF).support :=
  (mem_support_different_iff k' F' hF).mpr
    (Place.differentExponent_pos_of_one_lt_ramificationIdx k F P' h).ne'

/-- **Dedekind's different theorem** (Stichtenoth, Theorem 3.5.1(a)) at the level of divisors:
the coefficient of `P'` in `Diff(F'/F)` is at least `e(P' ∣ P) - 1`, stated without subtraction. -/
theorem ramificationIdx_le_coeff_different_add_one (P' : Place k' F') :
    (Place.ramificationIdx F P' : ℤ) ≤ (different k' F' hF).coeff P' + 1 := by
  rw [coeff_different]
  exact_mod_cast Place.ramificationIdx_le_differentExponent_add_one k F P'

/-- **The different divisor vanishes exactly when no place of `F'` ramifies.** -/
theorem different_eq_zero_iff :
    different k' F' hF = 0 ↔ ∀ P' : Place k' F', Place.differentExponent k F P' = 0 := by
  refine ⟨fun h P' ↦ ?_, fun h ↦ ?_⟩
  · simpa using congrArg (fun D ↦ WeilDivisor.coeff D P') h
  · ext P'
    simpa using h P'

end Divisor

end TauCeti
