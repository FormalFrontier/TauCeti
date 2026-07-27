/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.Algebra.Group.ElementaryTwoQuotient.FreeModule

/-!
# The maximal elementary-2 quotient of a cyclic group

For a cyclic group `G`, the maximal elementary-2 quotient `G / G²` of
`TauCeti.Algebra.Group.ElementaryTwoQuotient.Basic` has cardinality `gcd |G| 2`, where `|G|` is
read via `Nat.card` (so `|G| = 0` for an infinite cyclic group). This unifies the parities: a
finite cyclic group of even order and an infinite cyclic group both have two square classes
(`gcd |G| 2 = 2`), and a finite cyclic group of odd order has one. The even reading and its
2-rank are corollaries.

The finite case is Mathlib's index computation `IsCyclic.index_powMonoidHom_range` (the subgroup
of `d`-th powers has index `gcd |G| d`) read through `G² = range (powMonoidHom 2)`; the infinite
case is `G ≃* Multiplicative ℤ`, whose elementary-2 quotient is `2 ^ finrank ℤ ℤ = 2`.

These are the cyclic building blocks promised by the product lemmas of
`TauCeti.Algebra.Group.ElementaryTwoQuotient.Prod`: a finite abelian group is a product of cyclic
groups, and combining that decomposition with this file reads off its 2-rank as the number of
even-order cyclic factors. The multiquadratic roadmap consumes the even case through the torsion
subgroup of a number field's unit group, which is finite cyclic of even order. The odd-order case
also holds for any commutative group (no cyclicity), as
`TauCeti.card_elementaryTwoQuotient_of_odd_card` in `Basic`.

## Main results

* `TauCeti.card_elementaryTwoQuotient_of_isCyclic`: `|G/G²| = gcd |G| 2` for cyclic `G`.
* `TauCeti.card_elementaryTwoQuotient_of_isCyclic_of_even`: the even reading, `2`.
* `TauCeti.twoRank_of_isCyclic_of_even`: an even-order cyclic group has 2-rank `1`.
-/

public section

namespace TauCeti

variable (G : Type*) [CommGroup G] [IsCyclic G]

/-- **The elementary-2 quotient of a cyclic group has `gcd |G| 2` elements.** For the finite case
the subgroup of squares has index `gcd |G| 2` (Mathlib's `IsCyclic.index_powMonoidHom_range`, read
through `G² = range (powMonoidHom 2)`); the infinite case is `G ≃* Multiplicative ℤ`, whose
elementary-2 quotient is `2 ^ finrank ℤ ℤ = 2 = gcd 0 2`. -/
theorem card_elementaryTwoQuotient_of_isCyclic :
    Nat.card (ElementaryTwoQuotient G) = (Nat.card G).gcd 2 := by
  rcases finite_or_infinite G with hfin | hinf
  · rw [card_elementaryTwoQuotient_eq_index_square, square_eq_powMonoidHom_two_range,
      IsCyclic.index_powMonoidHom_range]
  · rw [Nat.card_congr (elementaryTwoQuotientCongr (intCyclicMulEquiv (G := G)).symm).toEquiv,
      card_elementaryTwoQuotient_multiplicative, Module.finrank_self, pow_one,
      Nat.card_eq_zero_of_infinite, Nat.gcd_zero_left]

/-- A cyclic group of even order has exactly two square classes. -/
theorem card_elementaryTwoQuotient_of_isCyclic_of_even (h : Even (Nat.card G)) :
    Nat.card (ElementaryTwoQuotient G) = 2 := by
  rw [card_elementaryTwoQuotient_of_isCyclic, Nat.gcd_comm]
  exact Nat.gcd_eq_left h.two_dvd

/-- A cyclic group of even order has 2-rank one. -/
theorem twoRank_of_isCyclic_of_even (h : Even (Nat.card G)) : twoRank G = 1 :=
  twoRank_eq_of_card_elementaryTwoQuotient_eq_two_pow G
    ((card_elementaryTwoQuotient_of_isCyclic_of_even G h).trans (pow_one 2).symm)

end TauCeti
