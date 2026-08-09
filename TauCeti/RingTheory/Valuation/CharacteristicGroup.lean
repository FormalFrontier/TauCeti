/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Cofinal values and the full-characteristic-group condition

Two conditions on the values of a valuation `v : Valuation A Γ₀` from the `Spv (A, I)`
theory of Wedhorn, *Adic Spaces* (arXiv:1910.05934v1), §4.3 and §7.1. Both are formulated
on the **value group** of `v` — Mathlib's `ValueGroup₀ (.ofClass v)`, via the restricted
valuation `v.restrict` — not on the ambient codomain, so they are invariant under valuation
equivalence (`IsEquiv.cofinalValue_iff`, `IsEquiv.hasFullCharacteristicGroup_iff`) and can
be consumed on points of the valuation spectrum:

* a value `v a` is *cofinal* if its powers fall below every positive element of the value
  group — the condition on ideals of definition in Wedhorn Lemma 7.1;
* `v` *has full characteristic group* if every positive element of the value group is
  bounded between `(v a)⁻¹` and `v a` for some `a` — the elementwise
  reading of "`Γ_v = cΓ_v`", for the characteristic subgroup `cΓ_v` of Wedhorn 4.13.

These are the two disjuncts of the membership criterion for `Spv (A, I)`: Wedhorn
Lemma 7.4 proves `cΓ_v(I) = Γ_v` equivalent to "`v a` is cofinal for every `a ∈ I`, or
`Γ_v = cΓ_v`". The *microbial* condition of Wedhorn Definition 5.46 (existence of a
dependent height-one valuation) is a genuinely different notion and is deliberately not
formalised here.

## Main definitions

* `TauCeti.Valuation.CofinalValue v a` : Powers of `v a` fall below every positive element
  of the value group of `v`.
* `TauCeti.Valuation.HasFullCharacteristicGroup v` : Every positive element of the value
  group of `v` is bounded by attained values.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, 4.13, Lemma 7.1, Lemma 7.4

The statements are adapted from the AINTLIB development (Apache 2.0), files
`projects/AdicSpaces/Adic spaces/SpvAI.lean` (the cofinal-value cluster) and
`projects/AdicSpaces/Adic spaces/CharacteristicSubgroup.lean` (the characteristic-group
cluster), reformulated on the value group.
-/

public section

namespace TauCeti.Valuation

open MonoidWithZeroHom

variable {A : Type*} [Ring A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀']

/-! ### Cofinal values -/

/-- A value `v a` is **cofinal** if for every positive `γ` in the value group of `v` some
power `(v a) ^ n` lies strictly below `γ` (Wedhorn Lemma 7.1: the condition satisfied by
the elements of an ideal of definition). -/
def CofinalValue (v : Valuation A Γ₀) (a : A) : Prop :=
  ∀ γ : ValueGroup₀ (.ofClass v), 0 < γ → ∃ n : ℕ, v.restrict a ^ n < γ

/-- The defining property of a cofinal value, on the value group of `v`. -/
@[simp]
theorem cofinalValue_iff {v : Valuation A Γ₀} {a : A} :
    CofinalValue v a ↔ ∀ γ : ValueGroup₀ (.ofClass v), 0 < γ → ∃ n : ℕ, v.restrict a ^ n < γ :=
  Iff.rfl

/-- A cofinal value is at most `1`: otherwise its powers stay above `1`. -/
theorem CofinalValue.le_one {v : Valuation A Γ₀} {a : A} (h : CofinalValue v a) :
    v a ≤ 1 := by
  by_contra h_gt
  push Not at h_gt
  have h_res : 1 < v.restrict a := by
    have := (v.restrict_lt_iff (x := 1) (y := a)).mpr (by simpa using h_gt)
    simpa using this
  obtain ⟨n, hn⟩ := h 1 zero_lt_one
  exact absurd hn (not_lt_of_ge (one_le_pow_of_one_le' h_res.le n))

/-- Cofinality is downward closed in the value: a smaller value is cofinal whenever a
larger one is (Wedhorn Lemma 7.1). -/
theorem CofinalValue.of_le {v : Valuation A Γ₀} {a b : A} (h : CofinalValue v a)
    (hba : v b ≤ v a) : CofinalValue v b := fun γ hγ ↦
  let ⟨n, hn⟩ := h γ hγ
  ⟨n, lt_of_le_of_lt (pow_le_pow_left' (v.restrict_le_iff.mpr hba) n) hn⟩

/-- Cofinality transports along an equivalence of valuations, through the ordered
isomorphism of their value groups. -/
theorem CofinalValue.of_isEquiv {v : Valuation A Γ₀} {w : Valuation A Γ₀'}
    (h : v.IsEquiv w) {a : A} (hv : CofinalValue v a) : CofinalValue w a := by
  intro γ hγ
  obtain ⟨n, hn⟩ := hv (h.orderMonoidIso.symm γ)
    (zero_lt_iff.mpr fun heq ↦ hγ.ne' (by simpa using congrArg h.orderMonoidIso heq))
  refine ⟨n, ?_⟩
  have := (map_lt_map_iff h.orderMonoidIso).mpr hn
  rw [map_pow, Valuation.IsEquiv.orderMonoidIso_spec] at this
  simpa using this

/-- Cofinality is invariant under valuation equivalence. -/
theorem _root_.Valuation.IsEquiv.cofinalValue_iff {v : Valuation A Γ₀}
    {w : Valuation A Γ₀'} (h : v.IsEquiv w) {a : A} :
    CofinalValue v a ↔ CofinalValue w a :=
  ⟨fun hv ↦ hv.of_isEquiv h, fun hw ↦ hw.of_isEquiv h.symm⟩

/-! ### The full-characteristic-group condition -/

/-- A valuation **has full characteristic group** if every positive element of its value
group is bounded between `(v a)⁻¹` and `v a` for some `a` — the elementwise form of
"`Γ_v = cΓ_v`", for the characteristic subgroup `cΓ_v` of Wedhorn 4.13. Such a witness
automatically satisfies `1 ≤ v.restrict a`, since the two bounds force `x⁻¹ ≤ x`. This is
the second disjunct of Wedhorn Lemma 7.4(ii); it is weaker than the *microbial* condition
of Wedhorn Definition 5.46 (on a field it holds for every valuation). -/
def HasFullCharacteristicGroup (v : Valuation A Γ₀) : Prop :=
  ∀ γ : ValueGroup₀ (.ofClass v), 0 < γ →
    ∃ a : A, (v.restrict a)⁻¹ ≤ γ ∧ γ ≤ v.restrict a

/-- The defining property of the full-characteristic-group condition. -/
@[simp]
theorem hasFullCharacteristicGroup_iff {v : Valuation A Γ₀} :
    HasFullCharacteristicGroup v ↔
      ∀ γ : ValueGroup₀ (.ofClass v), 0 < γ →
        ∃ a : A, (v.restrict a)⁻¹ ≤ γ ∧ γ ≤ v.restrict a :=
  Iff.rfl

/-- A bounding witness is automatically at least `1`: the two bounds force
`x⁻¹ ≤ x` at a positive element. -/
private theorem one_le_of_inv_le_of_le {v : Valuation A Γ₀}
    {x γ : ValueGroup₀ (.ofClass v)} (hγ : 0 < γ)
    (h1 : x⁻¹ ≤ γ) (h2 : γ ≤ x) : 1 ≤ x := by
  by_contra hx
  push Not at hx
  have hx0 : 0 < x := hγ.trans_le h2
  have h3 : (1 : ValueGroup₀ (.ofClass v)) < x⁻¹ := (one_lt_inv₀ hx0).mpr hx
  exact absurd ((h1.trans h2).trans hx.le) (not_le.mpr h3)

/-- Strengthened elimination: a bounding witness for a positive `γ` can be taken with
`1 ≤ v.restrict a` alongside the two bounds. -/
theorem HasFullCharacteristicGroup.exists_one_le {v : Valuation A Γ₀}
    (h : HasFullCharacteristicGroup v) {γ : ValueGroup₀ (.ofClass v)} (hγ : 0 < γ) :
    ∃ a : A, 1 ≤ v.restrict a ∧ (v.restrict a)⁻¹ ≤ γ ∧ γ ≤ v.restrict a := by
  obtain ⟨a, h1, h2⟩ := h γ hγ
  exact ⟨a, one_le_of_inv_le_of_le hγ h1 h2, h1, h2⟩

/-- The full-characteristic-group condition transports along an equivalence of
valuations, through the ordered isomorphism of their value groups. -/
theorem HasFullCharacteristicGroup.of_isEquiv {v : Valuation A Γ₀} {w : Valuation A Γ₀'}
    (h : v.IsEquiv w) (hv : HasFullCharacteristicGroup v) : HasFullCharacteristicGroup w := by
  intro γ hγ
  obtain ⟨a, ha_lo, ha_hi⟩ := hv (h.orderMonoidIso.symm γ)
    (zero_lt_iff.mpr fun heq ↦ hγ.ne' (by simpa using congrArg h.orderMonoidIso heq))
  refine ⟨a, ?_, ?_⟩
  · have := (map_le_map_iff h.orderMonoidIso).mpr ha_lo
    rw [map_inv₀, Valuation.IsEquiv.orderMonoidIso_spec] at this
    simpa using this
  · have := (map_le_map_iff h.orderMonoidIso).mpr ha_hi
    rw [Valuation.IsEquiv.orderMonoidIso_spec] at this
    simpa using this

/-- The full-characteristic-group condition is invariant under valuation equivalence. -/
theorem _root_.Valuation.IsEquiv.hasFullCharacteristicGroup_iff {v : Valuation A Γ₀}
    {w : Valuation A Γ₀'} (h : v.IsEquiv w) :
    HasFullCharacteristicGroup v ↔ HasFullCharacteristicGroup w :=
  ⟨fun hv ↦ hv.of_isEquiv h, fun hw ↦ hw.of_isEquiv h.symm⟩

/-- Under the full-characteristic-group condition, every positive element of the value
group dominates the inverse of some nonzero value: the existence statement used in the
`Γ_v = cΓ_v` case of Wedhorn Lemma 7.10. -/
theorem HasFullCharacteristicGroup.exists_inv_le {v : Valuation A Γ₀}
    (h : HasFullCharacteristicGroup v)
    {γ : ValueGroup₀ (.ofClass v)} (hγ : 0 < γ) :
    ∃ t : A, v.restrict t ≠ 0 ∧ (v.restrict t)⁻¹ ≤ γ := by
  obtain ⟨a, ha_inv_le, ha_le⟩ := h γ hγ
  exact ⟨a, (hγ.trans_le ha_le).ne', ha_inv_le⟩

end TauCeti.Valuation
