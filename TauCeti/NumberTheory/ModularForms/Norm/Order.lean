/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.NormTrace
public import TauCeti.NumberTheory.ModularForms.Order.OfVanishing
import TauCeti.NumberTheory.ModularForms.Norm.Trace

/-!
# Orders along the norm map

The general-level valence formula reads the level-one formula off the norm
`ModularForm.norm`, so it needs the orders of a form to distribute over the norm's coset
product. This file records that distribution at interior points, for a form on any subgroup
of finite relative index: each coset factor is nonzero when the form is, and the vanishing
order of the norm is the sum of the orders of the factors.

## Main declarations

* `TauCeti.SlashInvariantForm.quotientFunc_ne_zero`: a coset factor of the norm of a nonzero
  form is nonzero.
* `TauCeti.ModularForm.orderOfVanishingAt_norm`: the vanishing order of the norm at a point
  is the sum, over the coset space, of the vanishing orders of the coset factors.
* `TauCeti.ModularForm.orderOfVanishingAt_quotientFunc_le_orderOfVanishingAt_norm`: each coset
  factor vanishes to at most the order the norm does, with
  `TauCeti.ModularForm.orderOfVanishingAt_le_orderOfVanishingAt_norm` as the identity-coset
  corollary — so the zeros of the norm dominate those of the form.
-/

open UpperHalfPlane

namespace TauCeti

noncomputable section

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

namespace SlashInvariantForm

/-- A coset factor of the norm of a nonzero form is nonzero: the factor is a slash translate
of the form, and the slash action of a group element kills only `0`. -/
public lemma quotientFunc_ne_zero [SlashInvariantFormClass F 𝒢 k] {f : F}
    (hf : (⇑f : ℍ → ℂ) ≠ 0) (q : ℋ ⧸ 𝒢.subgroupOf ℋ) :
    _root_.SlashInvariantForm.quotientFunc f q ≠ 0 := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [_root_.SlashInvariantForm.quotientFunc_mk]
    exact fun hzero ↦ hf ((SlashAction.slash_eq_zero_iff k g.val⁻¹ (⇑f : ℍ → ℂ)).1 hzero)

end SlashInvariantForm

namespace ModularForm

variable [𝒢.IsFiniteRelIndex ℋ] [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k]

/-- The vanishing order of the norm at an interior point is the sum of the vanishing orders
of its coset factors. -/
public lemma orderOfVanishingAt_norm (f : F) (hf : (⇑f : ℍ → ℂ) ≠ 0) (p : ℍ) :
    orderOfVanishingAt (⇑(_root_.ModularForm.norm ℋ f)) p =
      ∑ᶠ q : ℋ ⧸ 𝒢.subgroupOf ℋ,
        orderOfVanishingAt (_root_.SlashInvariantForm.quotientFunc f q) p := by
  let _ : Fintype (ℋ ⧸ 𝒢.subgroupOf ℋ) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, _root_.ModularForm.coe_norm]
  exact orderOfVanishingAt_prod
    (fun q _ ↦ SlashInvariantForm.mdifferentiable_quotientFunc f q)
    (fun q _ ↦ SlashInvariantForm.quotientFunc_ne_zero hf q) p

/-- Each coset factor of the norm of a form vanishes at a point to at most the order the norm
itself does. -/
public lemma orderOfVanishingAt_quotientFunc_le_orderOfVanishingAt_norm (f : F)
    (q : ℋ ⧸ 𝒢.subgroupOf ℋ) (p : ℍ) :
    orderOfVanishingAt (_root_.SlashInvariantForm.quotientFunc f q) p ≤
      orderOfVanishingAt (⇑(_root_.ModularForm.norm ℋ f)) p := by
  rcases eq_or_ne (⇑f : ℍ → ℂ) 0 with hf | hf
  · -- Every coset factor of the zero form is zero, and so is its norm.
    have hq : _root_.SlashInvariantForm.quotientFunc f q = 0 :=
      Quotient.inductionOn q fun g ↦ (SlashAction.slash_eq_zero_iff k g.val⁻¹ _).2 hf
    simp [hq, (_root_.ModularForm.norm_eq_zero_iff ℋ f).mpr hf]
  · rw [orderOfVanishingAt_norm f hf p]
    exact single_le_finsum q (Set.toFinite _) fun r ↦
      orderOfVanishingAt_nonneg (SlashInvariantForm.mdifferentiable_quotientFunc f r) p

/-- The norm vanishes at a point to at least the order the form itself does: the zeros of the
norm dominate the zeros of the form. -/
public lemma orderOfVanishingAt_le_orderOfVanishingAt_norm (f : F) (p : ℍ) :
    orderOfVanishingAt (⇑f) p ≤ orderOfVanishingAt (⇑(_root_.ModularForm.norm ℋ f)) p := by
  -- The form is the factor at the identity coset. That coset space is not a group —
  -- `𝒢.subgroupOf ℋ` need not be normal — so the identity coset is spelled `⟦1⟧`, not `1`.
  simpa using orderOfVanishingAt_quotientFunc_le_orderOfVanishingAt_norm f
    (⟦1⟧ : ℋ ⧸ 𝒢.subgroupOf ℋ) p

end ModularForm

end

end TauCeti
