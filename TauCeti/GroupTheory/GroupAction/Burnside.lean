/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Burnside's lemma on a product of two `G`-sets

A point of a product `G`-set `X × Y` is fixed by `g` exactly when both of its components are, so
Mathlib's Burnside lemma `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`, applied to
`X × Y`, reads

`∑ g : G, |X^g| * |Y^g| = |(X × Y) / G| * |G|`.

This is the shape in which Burnside's lemma computes the pairing of two permutation characters.

## Main statements

* `TauCeti.fixedBy_prod`: the fixed points of `g` on `X × Y` are the product of its fixed points
  on `X` and on `Y`.
* `TauCeti.card_fixedBy_prod`: the corresponding count.
* `TauCeti.sum_card_fixedBy_mul_card_fixedBy_eq_card_orbits_mul_card_group`: Burnside's lemma
  on `X × Y`.

## Implementation notes

Everything is phrased with `Nat.card`; Mathlib's Burnside lemma is stated with `Fintype.card` and
carries `Fintype` instances for each fixed-point set, which are supplied here from `Finite X` and
`Finite Y` rather than assumed.
-/

public section

open MulAction

namespace TauCeti

variable {G : Type*} (X Y : Type*)

section Monoid

variable [Monoid G] [MulAction G X] [MulAction G Y]

/-- A point of a product `G`-set is fixed exactly when both of its components are. -/
@[simp]
theorem fixedBy_prod (g : G) : fixedBy (X × Y) g = fixedBy X g ×ˢ fixedBy Y g := by
  ext p
  simp [mem_fixedBy, Prod.ext_iff, Set.mem_prod]

/-- The fixed points of `g` on a product `G`-set are counted by the product of the two
fixed-point counts. -/
theorem card_fixedBy_prod (g : G) :
    Nat.card (fixedBy (X × Y) g) = Nat.card (fixedBy X g) * Nat.card (fixedBy Y g) := by
  rw [fixedBy_prod, Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]

end Monoid

variable [Group G] [MulAction G X] [MulAction G Y]

/-- **Burnside's lemma on a product.** For a finite group `G` acting on two finite sets `X` and
`Y`, the sum over `g : G` of the product of the two fixed-point counts is the number of orbits of
`G` on `X × Y`, times the order of `G`. -/
theorem sum_card_fixedBy_mul_card_fixedBy_eq_card_orbits_mul_card_group
    [Fintype G] [Finite X] [Finite Y] :
    ∑ g : G, Nat.card (fixedBy X g) * Nat.card (fixedBy Y g) =
      Nat.card (orbitRel.Quotient G (X × Y)) * Nat.card G := by
  classical
  have : Fintype (X × Y) := Fintype.ofFinite _
  have : Fintype (orbitRel.Quotient G (X × Y)) := Fintype.ofFinite _
  have : ∀ g : G, Fintype (fixedBy (X × Y) g) := fun _ => Fintype.ofFinite _
  have hburnside := sum_card_fixedBy_eq_card_orbits_mul_card_group G (X × Y)
  simp only [← Nat.card_eq_fintype_card] at hburnside
  simpa only [card_fixedBy_prod] using hburnside

end TauCeti
