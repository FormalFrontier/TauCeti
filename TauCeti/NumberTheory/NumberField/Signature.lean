/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.TotallyPositive

/-!
# The signature map on the units of the ring of integers

The **signature** of an integer unit `u : (𝓞 K)ˣ` of a number field `K` records the sign of `u`
under each real embedding `K →+* ℝ`. Packaged as a group homomorphism to the product, over the real
infinite places, of the sign group `ℝˣ ⧸ (posSubgroup ℝ)` (the positive units of `ℝ` form an
index-`2` subgroup, so each factor is the two-element sign group), its **kernel is exactly the
totally positive integer units**.

This is the archimedean half of the narrow class group `Cl⁺(K)` (Layer 3 of the multiquadratic
roadmap): the image of the signature map on the integer units, sitting inside the full sign group,
measures the difference between the narrow and ordinary class groups `Cl⁺(K) → Cl(K)`, and the
`2`-rank of `Cl⁺(K)` is what the `t - 1` genus-theory formula computes for a real quadratic field.
The signature is taken on the arithmetic unit group `(𝓞 K)ˣ` (Dirichlet units), not the whole
multiplicative group `Kˣ`, because it is those units that control the comparison `Cl⁺(K) → Cl(K)`.

## Main definitions and results

* `TauCeti.NumberField.totallyPositiveIntegerUnits`: the subgroup of `(𝓞 K)ˣ` of totally positive
  integer units, as the preimage of `totallyPositiveUnits` under `(𝓞 K)ˣ → Kˣ`.
* `TauCeti.NumberField.unitSignature`: the signature homomorphism
  `(𝓞 K)ˣ →* ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ)`.
* `TauCeti.NumberField.ker_unitSignature`: its kernel is `totallyPositiveIntegerUnits`.
* `TauCeti.NumberField.unitSignature_eq_one_iff`: an integer unit has trivial signature iff its
  image in `K` is totally positive.
-/

public section

open NumberField InfinitePlace

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The subgroup of **totally positive integer units** of `(𝓞 K)ˣ`: the preimage of
`totallyPositiveUnits` under the inclusion `(𝓞 K)ˣ → Kˣ`, i.e. the integer units whose image in `K`
is totally positive. -/
noncomputable def totallyPositiveIntegerUnits : Subgroup (𝓞 K)ˣ :=
  totallyPositiveUnits.comap (Units.map (algebraMap (𝓞 K) K).toMonoidHom)

omit [NumberField K] in
theorem mem_totallyPositiveIntegerUnits {u : (𝓞 K)ˣ} :
    u ∈ totallyPositiveIntegerUnits ↔ IsTotallyPositive (algebraMap (𝓞 K) K (u : 𝓞 K)) := by
  simp only [totallyPositiveIntegerUnits, Subgroup.mem_comap, mem_totallyPositiveUnits,
    Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]

/-- The **signature homomorphism** on the integer units of a number field: `u : (𝓞 K)ˣ` is sent, at
each real infinite place `w`, to the class of the sign of its image under the real embedding `w`, in
the sign group `ℝˣ ⧸ (posSubgroup ℝ)`. -/
noncomputable def unitSignature :
    (𝓞 K)ˣ →* ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) :=
  MonoidHom.pi fun w =>
    (QuotientGroup.mk' (Units.posSubgroup ℝ)).comp
      (Units.map ((embedding_of_isReal w.2).comp (algebraMap (𝓞 K) K)).toMonoidHom)

omit [NumberField K] in
theorem unitSignature_apply (u : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    unitSignature u w = QuotientGroup.mk' (Units.posSubgroup ℝ)
      (Units.map ((embedding_of_isReal w.2).comp (algebraMap (𝓞 K) K)).toMonoidHom u) := by
  simp only [unitSignature, MonoidHom.pi_apply, MonoidHom.comp_apply]

omit [NumberField K] in
/-- The kernel of the signature homomorphism is exactly the subgroup of totally positive integer
units. -/
theorem ker_unitSignature :
    MonoidHom.ker (unitSignature (K := K)) = totallyPositiveIntegerUnits := by
  ext u
  simp only [MonoidHom.mem_ker, funext_iff, Pi.one_apply, unitSignature_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Units.mem_posSubgroup, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.comp_apply,
    mem_totallyPositiveIntegerUnits, isTotallyPositive_iff, Subtype.forall]

omit [NumberField K] in
/-- An integer unit has trivial signature exactly when its image in `K` is totally positive. -/
theorem unitSignature_eq_one_iff {u : (𝓞 K)ˣ} :
    unitSignature u = 1 ↔ IsTotallyPositive (algebraMap (𝓞 K) K (u : 𝓞 K)) := by
  rw [← MonoidHom.mem_ker, ker_unitSignature, mem_totallyPositiveIntegerUnits]

end TauCeti.NumberField
