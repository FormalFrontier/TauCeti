/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.ClassNumber
public import TauCeti.NumberTheory.ClassGroup.ElementaryTwoQuotient

/-!
# Class-number bounds from the elementary-2 quotient

For a number field `K`, the genus-theory layer of the multiquadratic roadmap uses the
maximal elementary-2 quotient of the class group of its ring of integers,
`Cl(𝓞 K) / Cl(𝓞 K)²`. The generic construction and its class-group specialization live in
`TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic` and
`TauCeti.NumberTheory.ClassGroup.ElementaryTwoQuotient`; this file records the number-field
class-number consequences where Mathlib's class-number theorem supplies finiteness
automatically.

The quotient here is the maximal elementary-2 quotient, not the 2-torsion subgroup. For the
finite class group of a number field, the two have the same cardinality, and the quotient
cardinality divides the class number.

## Main results

* `NumberField.card_classGroupElementaryTwoQuotient_dvd_classNumber`: the elementary-2
  quotient cardinality divides the class number.
* `NumberField.two_pow_classGroupTwoRank_dvd_classNumber`: the same divisibility in
  rank form.
-/

public section

open scoped NumberField

namespace NumberField

variable (K : Type*) [Field K]

/-- The cardinality of `Cl(𝓞 K) / Cl(𝓞 K)²` divides the class number. -/
theorem card_classGroupElementaryTwoQuotient_dvd_classNumber [NumberField K] :
    Nat.card (TauCeti.ClassGroup.ElementaryTwoQuotient (𝓞 K)) ∣ NumberField.classNumber K := by
  rw [NumberField.classNumber]
  rw [← Nat.card_eq_fintype_card]
  exact TauCeti.ClassGroup.card_elementaryTwoQuotient_dvd_card (𝓞 K)

/-- The elementary-2 quotient of a number-field class group has cardinality at most the class
number. -/
theorem card_classGroupElementaryTwoQuotient_le_classNumber [NumberField K] :
    Nat.card (TauCeti.ClassGroup.ElementaryTwoQuotient (𝓞 K)) ≤ NumberField.classNumber K := by
  rw [NumberField.classNumber]
  rw [← Nat.card_eq_fintype_card]
  exact TauCeti.ClassGroup.card_elementaryTwoQuotient_le_card (𝓞 K)

/-- The rank form of `card_classGroupElementaryTwoQuotient_dvd_classNumber`:
`2 ^ TauCeti.ClassGroup.twoRank (𝓞 K)` divides the class number. -/
theorem two_pow_classGroupTwoRank_dvd_classNumber [NumberField K] :
    2 ^ TauCeti.ClassGroup.twoRank (𝓞 K) ∣ NumberField.classNumber K := by
  rw [NumberField.classNumber]
  rw [← Nat.card_eq_fintype_card]
  exact TauCeti.ClassGroup.two_pow_twoRank_dvd_card (𝓞 K)

/-- The rank form of `card_classGroupElementaryTwoQuotient_le_classNumber`:
`2 ^ TauCeti.ClassGroup.twoRank (𝓞 K)` is bounded by the class number. -/
theorem two_pow_classGroupTwoRank_le_classNumber [NumberField K] :
    2 ^ TauCeti.ClassGroup.twoRank (𝓞 K) ≤ NumberField.classNumber K := by
  rw [NumberField.classNumber]
  rw [← Nat.card_eq_fintype_card]
  exact TauCeti.ClassGroup.two_pow_twoRank_le_card (𝓞 K)

end NumberField
