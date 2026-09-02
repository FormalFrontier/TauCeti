/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Products over a disjoint union of index types

`Fintype.prod_sum_type` splits a product over `α ⊕ β` into the two partial products, but it needs
both index types to be finite.  This file records the `finprod` analogue, which only needs the two
restricted families to have finite multiplicative support.

## Main results

* `TauCeti.hasFiniteMulSupport_sum_type`: a family on `α ⊕ β` has finite multiplicative support as
  soon as its two restrictions do.
* `TauCeti.finprod_sum_type`: `∏ᶠ v : α ⊕ β, f v = (∏ᶠ a, f (.inl a)) * ∏ᶠ b, f (.inr b)`.
-/

public section

namespace TauCeti

open Function Set

variable {α β M : Type*} {f : α ⊕ β → M}

section One

variable [One M]

@[to_additive]
theorem mulSupport_sum_type (f : α ⊕ β → M) :
    mulSupport f =
      Sum.inl '' mulSupport (f ∘ Sum.inl) ∪ Sum.inr '' mulSupport (f ∘ Sum.inr) := by
  ext x
  cases x <;> simp [Sum.inl_injective.mem_set_image, Sum.inr_injective.mem_set_image]

/-- Finite multiplicative support on both summands implies finite multiplicative support on their
disjoint union. -/
@[to_additive]
theorem hasFiniteMulSupport_sum_type (hl : HasFiniteMulSupport (f ∘ Sum.inl))
    (hr : HasFiniteMulSupport (f ∘ Sum.inr)) : HasFiniteMulSupport f := by
  rw [HasFiniteMulSupport, mulSupport_sum_type]
  exact (Set.Finite.image _ hl).union (Set.Finite.image _ hr)

end One

variable [CommMonoid M]

/-- A product over a disjoint union of index types splits as the product of the two partial
products, provided both partial families have finite multiplicative support. -/
@[to_additive]
theorem finprod_sum_type (f : α ⊕ β → M) (hl : HasFiniteMulSupport (f ∘ Sum.inl))
    (hr : HasFiniteMulSupport (f ∘ Sum.inr)) :
    ∏ᶠ v : α ⊕ β, f v = (∏ᶠ a : α, f (Sum.inl a)) * ∏ᶠ b : β, f (Sum.inr b) := by
  have hfl : (range (Sum.inl : α → α ⊕ β) ∩ mulSupport f).Finite :=
    (Set.Finite.image Sum.inl hl).subset (by rintro _ ⟨⟨a, rfl⟩, hx⟩; exact ⟨a, hx, rfl⟩)
  have hfr : (range (Sum.inr : β → α ⊕ β) ∩ mulSupport f).Finite :=
    (Set.Finite.image Sum.inr hr).subset (by rintro _ ⟨⟨b, rfl⟩, hx⟩; exact ⟨b, hx, rfl⟩)
  rw [← finprod_mem_univ, ← range_inl_union_range_inr,
    finprod_mem_union' isCompl_range_inl_range_inr.disjoint hfl hfr,
    finprod_mem_range Sum.inl_injective, finprod_mem_range Sum.inr_injective]

end TauCeti
