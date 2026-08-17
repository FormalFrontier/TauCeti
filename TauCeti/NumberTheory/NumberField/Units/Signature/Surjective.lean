/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.SignApproximation
public import TauCeti.NumberTheory.NumberField.Units.Signature.Basic
import TauCeti.GroupTheory.QuotientGroup.KerEquiv

/-!
# The signature map of a number field is surjective

`NumberField.fieldUnitSignature` records the sign of an element of `Kˣ` under each real
embedding of a number field `K`, as a point of the sign group
`{w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ`. This file proves that every sign
pattern is realized: the signature map is surjective, its kernel being the totally positive
elements, so `Kˣ ⧸ totallyPositiveUnits` *is* the sign group and the totally positive elements have
index exactly `2 ^ r₁` in `Kˣ`, with `r₁` the number of real places.

The input is weak approximation at the real places,
`NumberField.exists_ne_zero_forall_isReal_pos`. The analogous *unit* signature
`NumberField.unitSignature` need not be surjective, so the index of the totally positive
units inside `(𝓞 K)ˣ` need not equal `2 ^ r₁`: it is a genuine arithmetic invariant, and the gap
between it and `2 ^ r₁` is exactly what the narrow class group measures.

## Main results

* `NumberField.fieldUnitSignature_surjective`: every sign pattern at the real places is the
  signature of an element of `Kˣ`.
* `NumberField.quotientTotallyPositiveUnitsEquiv`: `Kˣ ⧸ totallyPositiveUnits` is the sign
  group.
* `NumberField.index_totallyPositiveUnits`: the totally positive elements have index
  `2 ^ nrRealPlaces K` in `Kˣ`.

## References

The statement that `Kˣ` realizes every sign pattern is the archimedean half of weak approximation;
see J. Neukirch, *Algebraic Number Theory*, Chapter I, and the discussion of the narrow class group
in H. Cohn, *A Classical Invitation to Algebraic Numbers and Class Fields*.
-/

public section

open NumberField NumberField.InfinitePlace

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The signature map of a number field is surjective.** Every assignment of a sign to each real
place of `K` is realized by an element of `Kˣ`.

This is weak approximation at the real places; it says nothing about the signatures realized by the
units of `𝓞 K`, which form a genuinely smaller subgroup in general. -/
theorem fieldUnitSignature_surjective :
    Function.Surjective (fieldUnitSignature (K := K)) := by
  intro t
  -- Lift each prescribed sign class to an actual nonzero real.
  choose ε hε using fun w : {w : InfinitePlace K // w.IsReal} =>
    QuotientGroup.mk_surjective (s := Units.posSubgroup ℝ) (t w)
  obtain ⟨x, hx0, hx⟩ :=
    exists_ne_zero_forall_isReal_pos (K := K) (fun w => ((ε w : ℝˣ) : ℝ))
      fun w => (ε w).ne_zero
  refine ⟨Units.mk0 x hx0, funext fun w => ?_⟩
  rw [fieldUnitSignature_apply, ← hε w]
  refine QuotientGroup.eq.mpr ?_
  rw [Units.mem_posSubgroup]
  -- The real embedding of `x` at `w` has the sign of `ε w`, hence so does its inverse.
  have h := hx w
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, Units.val_mk0]
  rcases mul_pos_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_pos (inv_pos.mpr h2) h1
  · exact mul_pos_of_neg_of_neg (inv_lt_zero.mpr h2) h1

/-- **The sign group is the quotient of `Kˣ` by the totally positive elements.** -/
-- The two instance arguments are explicit because the codomain carries `Pi.mulOneClass`, while
-- `QuotientGroup.quotientKerEquivOfSurjective` states its multiplicative structure through `Group`.
-- They agree definitionally, but inference otherwise makes the unifier rediscover this at each use.
noncomputable def quotientTotallyPositiveUnitsEquiv :
    Kˣ ⧸ totallyPositiveUnits (K := K) ≃*
      ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) :=
  MulEquiv.trans
    (QuotientGroup.quotientMulEquivOfEq (G := Kˣ) (fieldUnitSignature_ker (K := K)).symm)
    (@QuotientGroup.quotientKerEquivOfSurjective Kˣ _
      ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) inferInstance
      fieldUnitSignature fieldUnitSignature_surjective)

/-- The quotient equivalence sends the class of `u : Kˣ` to its signature. -/
@[simp] theorem quotientTotallyPositiveUnitsEquiv_mk (u : Kˣ) :
    quotientTotallyPositiveUnitsEquiv (K := K) (QuotientGroup.mk u) = fieldUnitSignature u := by
  simp [quotientTotallyPositiveUnitsEquiv,
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk]

/-- There are `2 ^ r₁` sign patterns at the real places, `r₁` being their number: the codomain of
`NumberField.fieldUnitSignature` is a product of `r₁` two-element sign groups. -/
theorem card_realSignPatterns :
    Nat.card ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) =
      2 ^ nrRealPlaces K := by
  classical
  rw [Nat.card_fun, ← Subgroup.index_eq_card, Units.index_posSubgroup, Nat.card_eq_fintype_card]

/-- **The totally positive elements of `Kˣ` have index `2 ^ r₁`,** with `r₁` the number of real
places of `K`. This is the exact value of the index whose finiteness is
`NumberField.finiteIndex_totallyPositiveUnits`. -/
theorem index_totallyPositiveUnits :
    (totallyPositiveUnits (K := K)).index = 2 ^ nrRealPlaces K := by
  rw [Subgroup.index_eq_card,
    Nat.card_congr (quotientTotallyPositiveUnitsEquiv (K := K)).toEquiv,
    card_realSignPatterns]

/-- **Every element of `Kˣ` is totally positive exactly when `K` has no real place.** One direction
is vacuity of total positivity over a totally complex field; the other needs an element of `Kˣ`
negative at a given real place, which is what surjectivity of the signature provides. -/
@[simp] theorem totallyPositiveUnits_eq_top_iff :
    totallyPositiveUnits (K := K) = ⊤ ↔ nrRealPlaces K = 0 := by
  rw [← Subgroup.index_eq_one, index_totallyPositiveUnits]
  simp

end NumberField
