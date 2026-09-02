/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic
public import TauCeti.RingTheory.Valuation.WithZeroMulInt

/-!
# The normalized valuation of a nonarchimedean local field

A nonarchimedean local field `K` carries a canonical valuative relation, but Mathlib's
`ValuativeRel.valuation K` takes values in the abstract group `ValueGroupWithZero K`. This file
pins the two concrete normalizations of that valuation and relates them.

## Main definitions

* `TauCeti.IsNonarchimedeanLocalField.mulValuation K : Valuation K ℤᵐ⁰`, the canonical valuation
  read in `ℤᵐ⁰ = WithZero (Multiplicative ℤ)` through
  `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`. It follows Mathlib's multiplicative
  convention, the one of `Padic.mulValuation`: a uniformizer has value `WithZero.exp (-1) < 1`
  and `𝒪[K]` is the set of elements of value at most `1`.
* `TauCeti.IsNonarchimedeanLocalField.normalizedValuation K : Kˣ →* Multiplicative ℤ`, the
  additive normalization `v_K` of the same valuation, for which a uniformizer has value
  `Multiplicative.ofAdd 1`.

## Main results

* `TauCeti.IsNonarchimedeanLocalField.eq_mulValuation`: `mulValuation K` is *the* surjective
  `ℤᵐ⁰`-valued valuation in the canonical class, so it does not depend on the arbitrary choice
  made by `valueGroupWithZeroIsoInt`.
* `TauCeti.IsNonarchimedeanLocalField.mulValuation_integers`: `𝒪[K]` is the ring of integers of
  `mulValuation K`. This unlocks the whole `Valuation.Integers` API — divisibility versus the
  order on values, units versus value `1`, and so on — for the normalized valuation.
* `TauCeti.IsNonarchimedeanLocalField.mulValuation_irreducible` and
  `TauCeti.IsNonarchimedeanLocalField.normalizedValuation_irreducible`: the value at a
  uniformizer, in the two normalizations.
* `TauCeti.IsNonarchimedeanLocalField.normalizedValuation_surjective`: the value group of `v_K`
  is all of `ℤ`.
* `TauCeti.IsNonarchimedeanLocalField.normalizedValuation_eq_one_iff` and
  `TauCeti.IsNonarchimedeanLocalField.normalizedValuation_eq_one_iff_isUnit`: `v_K` is trivial
  exactly on the units of `𝒪[K]`.

## Implementation notes

Mathlib's convention makes the two normalizations differ by a sign: `v_K` is *minus* the
logarithm of `mulValuation K`. `toAdd_normalizedValuation` is the single lemma that translates
between them, and every statement mixing the two goes through it.
-/

public section

open ValuativeRel WithZero

namespace TauCeti

namespace IsNonarchimedeanLocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### The multiplicative normalization -/

/-- The canonical valuation of a nonarchimedean local field, read in `ℤᵐ⁰`.

This is Mathlib's multiplicative convention, matching `Padic.mulValuation`: a uniformizer has
value `WithZero.exp (-1)`, which is `< 1`, and `𝒪[K]` is the set of elements of value at most
`1`. The additively normalized `normalizedValuation`, for which a uniformizer has value
`Multiplicative.ofAdd 1`, is minus its logarithm. -/
noncomputable def mulValuation : Valuation K ℤᵐ⁰ :=
  (valuation K).map
    (MonoidWithZeroHom.ofClass (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K))
    (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).strictMono.monotone

private theorem mulValuation_apply (x : K) : mulValuation K x =
    _root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x) := (rfl)

/-- `mulValuation K` represents the canonical valuative relation of `K`. -/
instance : (mulValuation K).Compatible where
  vle_iff_le x y := by
    rw [Valuation.vle_iff_le (valuation K), mulValuation_apply, mulValuation_apply,
      OrderIsoClass.map_le_map_iff]

/-- The value group of `mulValuation K` is all of `ℤᵐ⁰`. -/
theorem mulValuation_surjective : Function.Surjective (mulValuation K) := by
  intro γ
  obtain ⟨δ, rfl⟩ :=
    (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).surjective γ
  obtain ⟨x, rfl⟩ := ValuativeRel.valuation_surjective δ
  exact ⟨x, (mulValuation_apply K x)⟩

/-- `mulValuation K` is the unique surjective `ℤᵐ⁰`-valued valuation in the canonical valuation
class of `K`. In particular it does not depend on the choice `valueGroupWithZeroIsoInt` makes. -/
theorem eq_mulValuation (v : Valuation K ℤᵐ⁰) [v.Compatible] (hv : Function.Surjective v) :
    v = mulValuation K :=
  (ValuativeRel.isEquiv v (mulValuation K)).eq_of_surjective hv
    (mulValuation_surjective K)

/-- The ring of integers of `mulValuation K` is `𝒪[K]`. -/
@[simp]
theorem integer_mulValuation : (mulValuation K).integer = 𝒪[K] := by
  ext x
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff,
    ← Valuation.vle_one_iff (mulValuation K), Valuation.vle_one_iff (valuation K)]

/-- `𝒪[K]` is the ring of integers of `mulValuation K`, as a `Valuation.Integers` statement.
This is the gateway to Mathlib's `Valuation.Integers` API: divisibility in `𝒪[K]` against the
order on values, units against value `1`, and irreducibles against value `< 1`. -/
theorem mulValuation_integers : (mulValuation K).Integers 𝒪[K] where
  hom_inj := Subtype.val_injective
  map_le_one x := by
    rw [← Valuation.mem_integer_iff, integer_mulValuation]; exact x.2
  exists_of_le_one {r} hr := by
    rw [← Valuation.mem_integer_iff, integer_mulValuation] at hr
    exact ⟨⟨r, hr⟩, rfl⟩

/-- A uniformizer of `K`, that is an irreducible element of the discrete valuation ring `𝒪[K]`,
has multiplicative value `WithZero.exp (-1)`: the value group of `mulValuation K` is generated
by the value at a uniformizer. -/
theorem mulValuation_irreducible {π : 𝒪[K]} (hπ : Irreducible π) :
    mulValuation K (π : K) = exp (-1) := by
  have hints := mulValuation_integers K
  -- Mathlib states the `Valuation.Integers` API through `algebraMap 𝒪[K] K`, which is the
  -- coercion; `hcoe` is the (definitional) identification, used to rewrite the statements below.
  have hcoe : ∀ y : 𝒪[K], algebraMap (𝒪[K]) K y = (y : K) := fun _ ↦ rfl
  have hπ1 : mulValuation K (π : K) < 1 := by
    simpa [hcoe] using hints.valuation_irreducible_lt_one hπ
  have hπ0 : mulValuation K (π : K) ≠ 0 := by
    simpa [hcoe] using (hints.valuation_irreducible_pos hπ).ne'
  obtain ⟨m, hm⟩ : ∃ m : ℤ, mulValuation K (π : K) = exp m := ⟨log _, (exp_log hπ0).symm⟩
  rw [hm, exp_lt_one_iff] at hπ1
  rw [hm, exp_inj]
  by_contra hne
  -- The remaining possibility is `m < -1`; then an element of value `exp (-1)` would be a
  -- proper divisor of `π` inside `𝒪[K]`, contradicting irreducibility.
  obtain ⟨b, hb⟩ := mulValuation_surjective K (exp (-1))
  have hbmem : b ∈ 𝒪[K] := by
    rw [← integer_mulValuation, Valuation.mem_integer_iff, hb]
    simp
  obtain ⟨β, hb'⟩ : ∃ β : 𝒪[K], mulValuation K (β : K) = exp (-1) := ⟨⟨b, hbmem⟩, hb⟩
  have hdvd : β ∣ π := by
    rw [hints.dvd_iff_le, hcoe, hcoe, hb', hm, exp_le_exp]
    omega
  obtain ⟨c, hc⟩ := hdvd
  rcases hπ.isUnit_or_isUnit hc with hu | hu
  · rw [show mulValuation K (β : K) = 1 by simpa [hcoe] using hints.one_of_isUnit hu] at hb'
    exact absurd hb'.symm (by simp)
  · have hc1 : mulValuation K (c : K) = 1 := by simpa [hcoe] using hints.one_of_isUnit hu
    rw [hc, Subring.coe_mul, map_mul, hb', hc1, mul_one, exp_inj] at hm
    exact hne hm.symm

/-- The value at a uniformizer generates the value group: the valuation of any nonzero element
of `K` is an integer power of the valuation of a uniformizer. -/
theorem exists_valuation_eq_zpow_of_irreducible {π : 𝒪[K]} (hπ : Irreducible π) (x : Kˣ) :
    ∃ n : ℤ, valuation K (x : K) = valuation K (π : K) ^ n := by
  have hx : mulValuation K (x : K) ≠ 0 := by simp
  refine ⟨-log (mulValuation K (x : K)), ?_⟩
  rw [← map_zpow₀, (ValuativeRel.isEquiv (valuation K) (mulValuation K)).eq_iff, map_zpow₀,
    mulValuation_irreducible K hπ, ← exp_zsmul]
  simp [exp_log hx]

/-! ### The additive normalization -/

/-- The normalized valuation `v_K` of a nonarchimedean local field, as a homomorphism
`Kˣ →* Multiplicative ℤ`. It is normalized so that a uniformizer has value
`Multiplicative.ofAdd 1`; equivalently it is *minus* the logarithm of `mulValuation K`. -/
noncomputable def normalizedValuation : Kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (-log (mulValuation K (x : K)))
  map_one' := by simp
  map_mul' x y := by
    have hx : mulValuation K (x : K) ≠ 0 := by simp
    have hy : mulValuation K (y : K) ≠ 0 := by simp
    simp [log_mul hx hy, ofAdd_add, mul_comm]

/-- The `-log` translation lemma: the additive normalization is minus the logarithm of the
multiplicative one. Every statement mixing the two conventions goes through this lemma. -/
@[simp]
theorem toAdd_normalizedValuation (x : Kˣ) :
    (normalizedValuation K x).toAdd = -log (mulValuation K (x : K)) := (rfl)

/-- The multiplicative normalization recovered from the additive one. -/
theorem mulValuation_eq_exp_neg_toAdd (x : Kˣ) :
    mulValuation K (x : K) = exp (-(normalizedValuation K x).toAdd) := by
  rw [toAdd_normalizedValuation, neg_neg, exp_log (by simp)]

/-- The value group of the normalized valuation is all of `ℤ`. -/
theorem normalizedValuation_surjective : Function.Surjective (normalizedValuation K) := by
  intro n
  obtain ⟨x, hx⟩ := mulValuation_surjective K (exp (-n.toAdd))
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hx
    exact exp_ne_zero hx.symm
  refine ⟨Units.mk0 x hx0, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_normalizedValuation]
  simp [hx]

/-- The normalized valuation of `x` is trivial — that is, `v_K(x) = 0` after decoding with
`Multiplicative.toAdd` — exactly when `x` has valuation `1`. The form phrased on `𝒪[K]` is
`normalizedValuation_eq_one_iff_isUnit`. -/
theorem normalizedValuation_eq_one_iff (x : Kˣ) :
    normalizedValuation K x = 1 ↔ valuation K (x : K) = 1 := by
  rw [← (ValuativeRel.isEquiv (mulValuation K) (valuation K)).eq_one_iff_eq_one,
    ← Multiplicative.toAdd.injective.eq_iff, toAdd_normalizedValuation, toAdd_one, neg_eq_zero,
    ← exp_inj, exp_log (by simp), exp_zero]

/-- The normalized valuation is trivial exactly on the units of `𝒪[K]`. -/
theorem normalizedValuation_eq_one_iff_isUnit {u : 𝒪[K]} (hu : (u : K) ≠ 0) :
    normalizedValuation K (Units.mk0 (u : K) hu) = 1 ↔ IsUnit u := by
  rw [normalizedValuation_eq_one_iff, Units.val_mk0,
    (ValuativeRel.isEquiv (valuation K) (mulValuation K)).eq_one_iff_eq_one]
  exact ((mulValuation_integers K).isUnit_iff_valuation_eq_one).symm

/-- The uniformizer equation: a uniformizer has normalized valuation `Multiplicative.ofAdd 1`. -/
theorem normalizedValuation_irreducible {π : 𝒪[K]} (hπ : Irreducible π) (hπ0 : (π : K) ≠ 0) :
    normalizedValuation K (Units.mk0 (π : K) hπ0) = Multiplicative.ofAdd 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_normalizedValuation]
  simp [mulValuation_irreducible K hπ]

end IsNonarchimedeanLocalField

end TauCeti
