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

On `Kˣ` the signature is onto: weak approximation at the infinite places realizes every sign
pattern, which is `fieldUnitSignature_surjective`. So the integer-unit signature is the archimedean
input to the narrow class group `Cl⁺(K)` (Layer 3 of the multiquadratic roadmap): its **cokernel**
— the full sign group modulo `unitSignatures`, the signatures realized by units — is what
contributes the kernel of the surjection `Cl⁺(K) → Cl(K)` between the narrow and ordinary class
groups, and the `2`-rank of `Cl⁺(K)` is what the `t - 1` genus-theory formula computes for a real
quadratic field.

## Main definitions and results

* `TauCeti.NumberField.fieldUnitSignature`: the signature homomorphism on `Kˣ`, with
  `fieldUnitSignature_ker` computing its kernel as `totallyPositiveUnits`.
* `TauCeti.NumberField.unitSignature`: the signature homomorphism on `(𝓞 K)ˣ`, the restriction of
  `fieldUnitSignature`, with `unitSignature_ker` its kernel `totallyPositiveIntegerUnits` (defined
  in `TotallyPositive.lean`).
* `TauCeti.NumberField.fieldUnitSignature_map_algebraMap`: the two signatures agree on an integer
  unit, the form in which the comparison of their ranges is used.
* `TauCeti.NumberField.fieldUnitSignature_surjective`: **every sign pattern is realized in `Kˣ`**,
  by weak approximation.
* `TauCeti.NumberField.unitSignatures`: the sign patterns realized by the units of `𝓞 K`, with
  `card_unitSignatures_mul_index` recording that the ambient sign group has order `2 ^ r₁`. It is
  named because its index measures the narrow-versus-ordinary class-group defect.
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
theorem fieldUnitSignature_ker :
    MonoidHom.ker (fieldUnitSignature (K := K)) = totallyPositiveUnits := by
  ext u
  simp only [MonoidHom.mem_ker, funext_iff, Pi.one_apply, fieldUnitSignature_apply,
    QuotientGroup.eq_one_iff, Units.mem_posSubgroup, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, mem_totallyPositiveUnits, isTotallyPositive_iff,
    Subtype.forall]

/-- A unit has trivial field signature exactly when it is totally positive. -/
@[simp] theorem fieldUnitSignature_eq_one_iff {u : Kˣ} :
    fieldUnitSignature u = 1 ↔ IsTotallyPositive (u : K) := by
  rw [← MonoidHom.mem_ker, fieldUnitSignature_ker, mem_totallyPositiveUnits]

/-- The **signature homomorphism** on the integer units `(𝓞 K)ˣ`, the restriction of
`fieldUnitSignature` along the inclusion `(𝓞 K)ˣ → Kˣ`. -/
noncomputable def unitSignature :
    (𝓞 K)ˣ →* ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) :=
  fieldUnitSignature.comp (Units.map (algebraMap (𝓞 K) K).toMonoidHom)

/-- Componentwise evaluation of the integer-unit signature: the class, in the sign group, of the
image of `u` under the real embedding `w` composed with `(𝓞 K) → K`. -/
@[simp] theorem unitSignature_apply (u : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    unitSignature u w = (Units.map (embedding_of_isReal w.2).toMonoidHom
      (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) : ℝˣ ⧸ Units.posSubgroup ℝ) := by
  simp only [unitSignature, MonoidHom.comp_apply, fieldUnitSignature_apply]

/-- The integer-unit signature is the field-unit signature of the image in `Kˣ`. This is
`unitSignature`'s defining factorization, in the applied form a consumer comparing the two ranges
uses. -/
@[simp] theorem fieldUnitSignature_map_algebraMap (u : (𝓞 K)ˣ) :
    fieldUnitSignature (Units.map (algebraMap (𝓞 K) K : (𝓞 K) →* K) u) = unitSignature u := by
  simp only [unitSignature, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe]

/-- An integer unit has trivial signature exactly when its image in `K` is totally positive. -/
@[simp] theorem unitSignature_eq_one_iff {u : (𝓞 K)ˣ} :
    unitSignature u = 1 ↔ IsTotallyPositive (algebraMap (𝓞 K) K (u : 𝓞 K)) := by
  simp only [unitSignature, MonoidHom.comp_apply, fieldUnitSignature_eq_one_iff, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]

/-- The kernel of the integer-unit signature is exactly the totally positive integer units. -/
theorem unitSignature_ker :
    MonoidHom.ker (unitSignature (K := K)) = totallyPositiveIntegerUnits := by
  ext u
  rw [MonoidHom.mem_ker, unitSignature_eq_one_iff, mem_totallyPositiveIntegerUnits]

variable [NumberField K] in
open scoped Classical in
/-- **Every sign pattern is realized in `Kˣ`.** By weak approximation the diagonal image of `K` is
dense in the product of its infinite places, so `K` contains an element lying within distance `1`
of a prescribed `±1` at every infinite place. At a real place that pins its sign to the prescribed
one, and everywhere it keeps the element away from `0`, so it is a unit. -/
theorem fieldUnitSignature_surjective : Function.Surjective (fieldUnitSignature (K := K)) := by
  intro s
  -- Choose a representing unit of `ℝ` for each prescribed sign, and the corresponding `±1` in `K`.
  obtain ⟨r, hr⟩ : ∃ r : {w : InfinitePlace K // w.IsReal} → ℝˣ,
      ∀ w, (QuotientGroup.mk (r w) : ℝˣ ⧸ Units.posSubgroup ℝ) = s w :=
    ⟨fun w => (QuotientGroup.mk_surjective (s w)).choose,
      fun w => (QuotientGroup.mk_surjective (s w)).choose_spec⟩
  set ε : InfinitePlace K → K := fun v =>
    if h : v.IsReal then (if 0 < ((r ⟨v, h⟩ : ℝˣ) : ℝ) then 1 else -1) else 1 with hε
  have hone : ∀ v : InfinitePlace K, v (ε v) = 1 := by
    intro v
    have h1 : v (1 : K) = 1 := by rw [InfinitePlace.coe_apply, AbsoluteValue.map_one]
    have h2 : v (-1 : K) = 1 := by
      rw [InfinitePlace.coe_apply, map_neg_eq_map, AbsoluteValue.map_one]
    simp only [hε]
    split
    · split <;> assumption
    · assumption
  -- Weak approximation: some `x : K` lies in the open unit ball around `ε v` at every place `v`.
  obtain ⟨x, hx⟩ := (InfinitePlace.denseRange_algebraMap_pi K).exists_mem_open
    (isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball)
    ⟨fun v => WithAbs.toAbs v.1 (ε v), fun v _ => Metric.mem_ball_self one_pos⟩
  have hkey : ∀ v : InfinitePlace K, v (x - ε v) < 1 := fun v => by
    have h := hx v (Set.mem_univ v)
    rwa [Metric.mem_ball, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs] at h
  have hx0 : x ≠ 0 := by
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace K))
    intro h
    have hv := hkey v
    rw [h, zero_sub, InfinitePlace.coe_apply, map_neg_eq_map, ← InfinitePlace.coe_apply,
      hone v] at hv
    exact absurd hv (lt_irrefl 1)
  refine ⟨Units.mk0 x hx0, funext fun w => ?_⟩
  rw [fieldUnitSignature_apply, ← hr w]
  refine QuotientGroup.eq.mpr ?_
  rw [Units.mem_posSubgroup, Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map]
  have hεw : ε (w : InfinitePlace K) = if 0 < ((r w : ℝˣ) : ℝ) then 1 else -1 := by
    simp only [hε, w.2, Subtype.coe_eta, ↓reduceDIte]
  -- At the real place `w` the embedding of `x` is within `1` of `±1`, hence has that sign.
  have hball : |embedding_of_isReal w.2 x -
      embedding_of_isReal w.2 (ε (w : InfinitePlace K))| < 1 := by
    have h := hkey (w : InfinitePlace K)
    rwa [← map_sub, ← Real.norm_eq_abs, norm_embedding_of_isReal]
  by_cases hpos : 0 < ((r w : ℝˣ) : ℝ)
  · simp only [hεw, hpos, ↓reduceIte, map_one] at hball
    have hxpos : 0 < embedding_of_isReal w.2 x := by linarith [(abs_lt.mp hball).1]
    exact mul_pos (inv_pos.mpr hxpos) hpos
  · have hneg : ((r w : ℝˣ) : ℝ) < 0 := lt_of_le_of_ne (not_lt.mp hpos) (Units.ne_zero _)
    simp only [hεw, hpos, ↓reduceIte, map_neg, map_one] at hball
    have hxneg : embedding_of_isReal w.2 x < 0 := by linarith [(abs_lt.mp hball).2]
    exact mul_pos_of_neg_of_neg (inv_lt_zero.mpr hxneg) hneg

variable (K)

/-- The **sign patterns realized by the units of `𝓞 K`**: the range of the integer-unit
signature. -/
noncomputable def unitSignatures :
    Subgroup ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) :=
  (unitSignature (K := K)).range

variable {K}

@[simp] theorem mem_unitSignatures
    {s : {w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ} :
    s ∈ unitSignatures K ↔ ∃ u : (𝓞 K)ˣ, unitSignature u = s := Iff.rfl

variable [NumberField K] in
open scoped Classical in
/-- The sign patterns form a group of order `2 ^ r₁`, with `r₁` the number of real places: they are
a product, indexed by the real places, of copies of the two-element sign group `ℝˣ ⧸ posSubgroup ℝ`.
So the number of sign patterns realized by the units times the index of those inside all sign
patterns is `2 ^ r₁`. -/
theorem card_unitSignatures_mul_index :
    Nat.card (unitSignatures K) * (unitSignatures K).index = 2 ^ nrRealPlaces K := by
  rw [Subgroup.card_mul_index, Nat.card_fun, ← Subgroup.index_eq_card, Units.index_posSubgroup,
    Nat.card_eq_fintype_card]

end TauCeti.NumberField
