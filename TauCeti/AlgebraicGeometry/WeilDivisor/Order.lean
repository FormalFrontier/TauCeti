/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Basic
public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Order.Preorder.Finsupp

/-!
# The order on Weil divisors and the positive/negative part decomposition

This file continues the Jacobian roadmap's Layer A formal Weil divisor API
(`TauCeti.AlgebraicGeometry.WeilDivisor.Basic`) by recording the lattice-ordered-group structure of
formal divisors and the canonical decomposition of a divisor into its effective positive and
negative parts.

The point set `X →₀ ℤ` already carries the coefficientwise partial order, the lattice
operations `⊔`/`⊓`, and (because `ℤ` is an ordered group) the lattice-ordered-group positive and
negative parts `D⁺` and `D⁻` from Mathlib. The contribution here is to connect that order with
the divisor vocabulary already in place: effectivity is nonnegativity, `D ≤ E` is effectivity of
`E - D`, the pointwise maximum and minimum of effective divisors are effective, and every
divisor decomposes as `D = D⁺ - D⁻` with `D⁺`, `D⁻` effective of disjoint support. We read off
the consequences for the unweighted and weighted degree maps and compute the decomposition of
the basic degree-zero divisors `[x] - [y]`.

This reuses Mathlib's lattice-ordered-group `posPart`/`negPart` API
(`Mathlib.Algebra.Order.Group.PosPart`) and the coefficientwise order and lattice on finitely
supported functions (`Mathlib.Order.Preorder.Finsupp`, `Mathlib.Data.Finsupp.Order`); no
external mathematics is vendored.

This advances the Tau Ceti Jacobian roadmap, Layer A, "Divisors on a curve: Weil divisors
`⊕_x ℤ`", "principal divisors", and "Degree".
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X Y : Type*}

/-! ### The coefficientwise order -/

/-- One Weil divisor is `≤` another exactly when it is so coefficientwise. -/
lemma le_iff {D E : WeilDivisor X} : D ≤ E ↔ ∀ x, coeff D x ≤ coeff E x :=
  Finsupp.le_def

/-- The coefficientwise order projects to coefficients: `D ≤ E` gives `coeff D x ≤ coeff E x`. -/
lemma coeff_le_coeff {D E : WeilDivisor X} (h : D ≤ E) (x : X) : coeff D x ≤ coeff E x :=
  le_iff.mp h x

/-- Effectivity is exactly nonnegativity in the coefficientwise order. -/
lemma isEffective_iff_zero_le {D : WeilDivisor X} : IsEffective D ↔ 0 ≤ D := by
  rw [isEffective_iff, le_iff]
  simp

/-- Membership in the effective submonoid is nonnegativity in the coefficientwise order. -/
lemma mem_effectiveSubmonoid_iff_zero_le {D : WeilDivisor X} :
    D ∈ effectiveSubmonoid X ↔ 0 ≤ D := by
  rw [mem_effectiveSubmonoid, isEffective_iff_zero_le]

/-- `D ≤ E` exactly when the difference `E - D` is effective. -/
lemma le_iff_isEffective_sub {D E : WeilDivisor X} : D ≤ E ↔ IsEffective (E - D) := by
  rw [isEffective_iff_zero_le, sub_nonneg]

/-! ### Lattice operations -/

/-- The coefficient of a pointwise maximum is the maximum of the coefficients. -/
@[simp]
lemma coeff_sup (D E : WeilDivisor X) (x : X) :
    coeff (D ⊔ E) x = coeff D x ⊔ coeff E x :=
  Finsupp.sup_apply D E x

/-- The coefficient of a pointwise minimum is the minimum of the coefficients. -/
@[simp]
lemma coeff_inf (D E : WeilDivisor X) (x : X) :
    coeff (D ⊓ E) x = coeff D x ⊓ coeff E x :=
  Finsupp.inf_apply D E x

/-- The pointwise maximum of an effective divisor with any divisor is effective. -/
lemma IsEffective.sup {D E : WeilDivisor X} (hD : IsEffective D) :
    IsEffective (D ⊔ E) :=
  isEffective_iff_zero_le.mpr
    (le_sup_of_le_left (isEffective_iff_zero_le.mp hD))

/-- The pointwise minimum of two effective divisors is effective. -/
lemma IsEffective.inf {D E : WeilDivisor X} (hD : IsEffective D) (hE : IsEffective E) :
    IsEffective (D ⊓ E) :=
  isEffective_iff_zero_le.mpr
    (le_inf (isEffective_iff_zero_le.mp hD) (isEffective_iff_zero_le.mp hE))

/-- A pointwise minimum is effective exactly when both divisors are effective. -/
@[simp]
lemma isEffective_inf_iff {D E : WeilDivisor X} :
    IsEffective (D ⊓ E) ↔ IsEffective D ∧ IsEffective E := by
  rw [isEffective_iff_zero_le, isEffective_iff_zero_le, isEffective_iff_zero_le]
  constructor
  · intro h
    exact ⟨le_trans h inf_le_left, le_trans h inf_le_right⟩
  · rintro ⟨hD, hE⟩
    exact le_inf hD hE

/-- Removing the infimum from each of two Weil divisors leaves disjoint residual divisors. -/
lemma sub_inf_inf_sub_inf_eq_zero (D E : WeilDivisor X) : ((D - D ⊓ E) ⊓ (E - D ⊓ E)) = 0 := by
  rw [← inf_sub, sub_self]

/-! ### Positive and negative parts -/

/-- The coefficient of the positive part is the positive part of the coefficient. -/
@[simp]
lemma coeff_posPart (D : WeilDivisor X) (x : X) : coeff D⁺ x = coeff D x ⊔ 0 := by
  rw [posPart_def, coeff_sup, coeff_zero]

/-- The coefficient of the negative part is the negative part of the coefficient. -/
@[simp]
lemma coeff_negPart (D : WeilDivisor X) (x : X) : coeff D⁻ x = -coeff D x ⊔ 0 := by
  rw [negPart_def, coeff_sup, coeff_neg, coeff_zero]

/-- The positive part of a Weil divisor is effective. -/
@[simp]
lemma isEffective_posPart (D : WeilDivisor X) : IsEffective D⁺ :=
  isEffective_iff_zero_le.mpr (posPart_nonneg D)

/-- The negative part of a Weil divisor is effective. -/
@[simp]
lemma isEffective_negPart (D : WeilDivisor X) : IsEffective D⁻ :=
  isEffective_iff_zero_le.mpr (negPart_nonneg D)

/-- The positive and negative parts of a Weil divisor have disjoint supports: no point carries
both a positive and a negative coefficient. -/
lemma support_posPart_disjoint_negPart (D : WeilDivisor X) :
    Disjoint D⁺.support D⁻.support := by
  rw [Finset.disjoint_left]
  intro x hxp hxn
  rw [Finsupp.mem_support_iff] at hxp hxn
  have hinf : coeff D⁺ x ⊓ coeff D⁻ x = 0 := by
    rw [← coeff_inf, posPart_inf_negPart_eq_zero, coeff_zero]
  rcases le_total (coeff D⁺ x) (coeff D⁻ x) with h | h
  · exact hxp (by rwa [inf_eq_left.mpr h] at hinf)
  · exact hxn (by rwa [inf_eq_right.mpr h] at hinf)

/-- A divisor is effective exactly when its negative part vanishes. -/
lemma negPart_eq_zero_iff_isEffective {D : WeilDivisor X} : D⁻ = 0 ↔ IsEffective D := by
  rw [negPart_eq_zero, isEffective_iff_zero_le]

/-- A divisor is effective exactly when it equals its own positive part. -/
lemma posPart_eq_self_iff_isEffective {D : WeilDivisor X} : D⁺ = D ↔ IsEffective D := by
  rw [posPart_eq_self, isEffective_iff_zero_le]

/-! ### Degree of the decomposition -/

/-- The weighted degree splits over the positive/negative part decomposition. -/
lemma weightedDegree_posPart_sub_weightedDegree_negPart (w : X → ℤ) (D : WeilDivisor X) :
    weightedDegree w D⁺ - weightedDegree w D⁻ = weightedDegree w D := by
  rw [← weightedDegree_sub, _root_.posPart_sub_negPart D]

/-- The unweighted degree splits over the positive/negative part decomposition. -/
lemma degree_posPart_sub_degree_negPart (D : WeilDivisor X) :
    degree D⁺ - degree D⁻ = degree D := by
  simp only [← weightedDegree_one_eq_degree]
  exact weightedDegree_posPart_sub_weightedDegree_negPart _ D

/-! ### The decomposition of a point difference -/

/-- For distinct points the positive part of `[x] - [y]` is the point divisor `[x]`. -/
lemma posPart_pointDifference {x y : X} (h : x ≠ y) : (pointDifference x y)⁺ = ofPoint x := by
  classical
  ext z
  rw [coeff_posPart, coeff_pointDifference]
  rcases eq_or_ne z x with rfl | hzx
  · rw [if_pos rfl, if_neg h, coeff_ofPoint_self, sub_zero]
    exact sup_eq_left.mpr zero_le_one
  · rw [if_neg hzx, coeff_ofPoint_of_ne hzx]
    rcases eq_or_ne z y with rfl | hzy
    · rw [if_pos rfl, zero_sub]
      exact sup_eq_right.mpr (neg_nonpos.mpr zero_le_one)
    · rw [if_neg hzy, sub_zero]
      exact sup_idem 0

/-- For distinct points the negative part of `[x] - [y]` is the point divisor `[y]`. -/
lemma negPart_pointDifference {x y : X} (h : x ≠ y) : (pointDifference x y)⁻ = ofPoint y := by
  have hneg : -pointDifference x y = pointDifference y x := by
    rw [pointDifference, pointDifference, neg_sub]
  rw [← posPart_neg, hneg, posPart_pointDifference h.symm]

end WeilDivisor

end AlgebraicGeometry

end TauCeti
