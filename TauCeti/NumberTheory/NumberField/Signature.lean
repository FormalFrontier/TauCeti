/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.TotallyPositive

/-!
# The signature map on the units of a number field

The **signature** of a unit `u : Kˣ` of a number field `K` records the sign of `u` under each real
embedding `K →+* ℝ`. Packaged as a group homomorphism to the product, over the real infinite places,
of the sign group `ℝˣ ⧸ (posSubgroup ℝ)` (the positive units of `ℝ` form an index-`2` subgroup, so
each factor is the two-element sign group), its **kernel is exactly the totally positive units**
`TauCeti.NumberField.totallyPositiveUnits`.

This is the archimedean half of the narrow class group `Cl⁺(K)` (Layer 3 of the multiquadratic
roadmap): the image of the signature map on units, sitting inside the full sign group, measures the
difference between the narrow and ordinary class groups, and the `2`-rank of `Cl⁺(K)` is what the
`t - 1` genus-theory formula computes for a real quadratic field.

## Main definitions and results

* `TauCeti.NumberField.unitSignature`: the signature homomorphism
  `Kˣ →* ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ)`.
* `TauCeti.NumberField.ker_unitSignature`: its kernel is `totallyPositiveUnits`.
* `TauCeti.NumberField.unitSignature_eq_one_iff`: a unit has trivial signature iff it is totally
  positive.
-/

public section

open NumberField InfinitePlace

namespace TauCeti.NumberField

variable {K : Type*} [Field K]

/-- The **signature homomorphism** on the units of a number field: `u : Kˣ` is sent, at each real
infinite place `w`, to the class of its image `Units.map (embedding_of_isReal w) u` in the sign
group `ℝˣ ⧸ (posSubgroup ℝ)`. -/
noncomputable def unitSignature :
    Kˣ →* ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) :=
  MonoidHom.pi fun w =>
    (QuotientGroup.mk' (Units.posSubgroup ℝ)).comp
      (Units.map (embedding_of_isReal w.2).toMonoidHom)

theorem unitSignature_apply (u : Kˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    unitSignature u w = QuotientGroup.mk' (Units.posSubgroup ℝ)
      (Units.map (embedding_of_isReal w.2).toMonoidHom u) := by
  simp only [unitSignature, MonoidHom.pi_apply, MonoidHom.comp_apply]

/-- The kernel of the signature homomorphism is exactly the subgroup of totally positive units. -/
theorem ker_unitSignature : MonoidHom.ker (unitSignature (K := K)) = totallyPositiveUnits := by
  ext u
  simp only [MonoidHom.mem_ker, funext_iff, Pi.one_apply, unitSignature_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Units.mem_posSubgroup, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, mem_totallyPositiveUnits, isTotallyPositive_iff,
    Subtype.forall]

/-- A unit has trivial signature exactly when it is totally positive. -/
theorem unitSignature_eq_one_iff {u : Kˣ} :
    unitSignature u = 1 ↔ IsTotallyPositive (u : K) := by
  rw [← MonoidHom.mem_ker, ker_unitSignature, mem_totallyPositiveUnits]

end TauCeti.NumberField
