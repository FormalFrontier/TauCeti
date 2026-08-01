/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.NumberField.TotallyPositive

/-!
# The signature map on the units of a number field

The **signature** of a unit records its sign under each real embedding `K →+* ℝ`, as a class in the
sign group `ℝˣ ⧸ (posSubgroup ℝ)` (the positive units of `ℝ` form an index-`2` subgroup, so each
factor is the two-element sign group).

We build it first on the full multiplicative group `Kˣ` — `fieldUnitSignature`, whose kernel is the
totally positive units `totallyPositiveUnits` — and then restrict along `(𝓞 K)ˣ → Kˣ` to the
arithmetic unit group to obtain `unitSignature`, whose kernel is the totally positive integer units.

The integer-unit signature is the archimedean input to the narrow class group `Cl⁺(K)` (Layer 3 of
the multiquadratic roadmap): the *cokernel* of the signature — the full sign group modulo the
signatures realized by units — is what contributes the kernel of the surjection `Cl⁺(K) → Cl(K)`
between the narrow and ordinary class groups, and the `2`-rank of `Cl⁺(K)` is what the `t - 1`
genus-theory formula computes for a real quadratic field.

## Main definitions and results

* `TauCeti.NumberField.fieldUnitSignature`: the signature homomorphism on `Kˣ`, with
  `ker_fieldUnitSignature` computing its kernel as `totallyPositiveUnits`.
* `TauCeti.NumberField.unitSignature`: the signature homomorphism on `(𝓞 K)ˣ`, the restriction of
  `fieldUnitSignature`, with `ker_unitSignature` its kernel `totallyPositiveIntegerUnits` (defined
  in `TotallyPositive.lean`).
-/

public section

open NumberField InfinitePlace

namespace TauCeti.NumberField

variable {K : Type*} [Field K]

/-- The **signature homomorphism** on `Kˣ`: `u` is sent, at each real infinite place `w`, to the
class of its image `Units.map (embedding_of_isReal w) u` in the sign group
`ℝˣ ⧸ (posSubgroup ℝ)`. -/
noncomputable def fieldUnitSignature :
    Kˣ →* ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) :=
  MonoidHom.pi fun w =>
    (QuotientGroup.mk' (Units.posSubgroup ℝ)).comp
      (Units.map (embedding_of_isReal w.2).toMonoidHom)

/-- Componentwise evaluation of the field-unit signature. -/
@[simp] theorem fieldUnitSignature_apply (u : Kˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    fieldUnitSignature u w =
      (Units.map (embedding_of_isReal w.2).toMonoidHom u : ℝˣ ⧸ Units.posSubgroup ℝ) := by
  simp only [fieldUnitSignature, MonoidHom.pi_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply]

/-- The kernel of the field-unit signature is exactly the subgroup of totally positive units. -/
theorem ker_fieldUnitSignature :
    MonoidHom.ker (fieldUnitSignature (K := K)) = totallyPositiveUnits := by
  ext u
  simp only [MonoidHom.mem_ker, funext_iff, Pi.one_apply, fieldUnitSignature_apply,
    QuotientGroup.eq_one_iff, Units.mem_posSubgroup, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, mem_totallyPositiveUnits, isTotallyPositive_iff,
    Subtype.forall]

/-- A unit has trivial field signature exactly when it is totally positive. -/
@[simp] theorem fieldUnitSignature_eq_one_iff {u : Kˣ} :
    fieldUnitSignature u = 1 ↔ IsTotallyPositive (u : K) := by
  rw [← MonoidHom.mem_ker, ker_fieldUnitSignature, mem_totallyPositiveUnits]

variable [NumberField K]

/-- The **signature homomorphism** on the integer units `(𝓞 K)ˣ`, the restriction of
`fieldUnitSignature` along the inclusion `(𝓞 K)ˣ → Kˣ`. -/
noncomputable def unitSignature :
    (𝓞 K)ˣ →* ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) :=
  fieldUnitSignature.comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom)

omit [NumberField K] in
/-- Componentwise evaluation of the integer-unit signature: the class, in the sign group, of the
image of `u` under the real embedding `w` composed with `(𝓞 K) → K`. -/
@[simp] theorem unitSignature_apply (u : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    unitSignature u w = (Units.map (embedding_of_isReal w.2).toMonoidHom
      (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) : ℝˣ ⧸ Units.posSubgroup ℝ) := by
  simp only [unitSignature, MonoidHom.comp_apply, fieldUnitSignature_apply]

omit [NumberField K] in
/-- The kernel of the integer-unit signature is exactly the totally positive integer units. -/
theorem ker_unitSignature :
    MonoidHom.ker (unitSignature (K := K)) = totallyPositiveIntegerUnits := by
  rw [unitSignature, ← MonoidHom.comap_ker, ker_fieldUnitSignature, totallyPositiveIntegerUnits_eq]

omit [NumberField K] in
/-- An integer unit has trivial signature exactly when its image in `K` is totally positive. -/
@[simp] theorem unitSignature_eq_one_iff {u : (𝓞 K)ˣ} :
    unitSignature u = 1 ↔ IsTotallyPositive (algebraMap (𝓞 K) K (u : 𝓞 K)) := by
  rw [← MonoidHom.mem_ker, ker_unitSignature, mem_totallyPositiveIntegerUnits]

end TauCeti.NumberField
