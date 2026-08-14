/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

/-!
# Vanishing and boundedness at a cusp are closed under finite sums

Mathlib's `OnePoint.IsZeroAt` and `OnePoint.IsBoundedAt` are closed under binary sums
(`OnePoint.IsZeroAt.add`, `OnePoint.IsBoundedAt.add`), but the zero function and a
`Finset.sum` are not recorded. This file adds them.

The gap matters for the Hecke operators, which are finite sums of slashes: a proof that such
an operator preserves vanishing at the cusps is an induction over the summands, and without
`OnePoint.IsZeroAt.sum` each call site has to rerun that induction by hand.

## Main declarations

* `UpperHalfPlane.isZeroAtImInfty_zero`: the zero analogue of Mathlib's
  `zero_form_isBoundedAtImInfty`, which is absent upstream.
* `OnePoint.IsZeroAt.zero`, `OnePoint.IsBoundedAt.zero`: the zero function vanishes, and is
  bounded, at every point of `OnePoint ℝ`.
* `OnePoint.IsZeroAt.sum`, `OnePoint.IsBoundedAt.sum`: a finite sum of functions vanishing
  (resp. bounded) at `c` vanishes (resp. is bounded) at `c`.

## Provenance

No code is transcribed here, but the gap these lemmas fill was identified from the AINTLIB
`LeanModularForms` project (Chris Birkbeck, Apache-2.0):
`LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean` lines 62-71, at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`. Its `heckeT_p_ut_zero_at_cusps` open-codes this
induction with `Finset.sum_induction`, and obtains the base case by constructing a zero
`CuspForm` purely to invoke `zero_at_cusps'` — because `IsZeroAt c 0 k` is not stated anywhere.
The statements below are about Mathlib's `OnePoint.IsZeroAt`/`IsBoundedAt` and are given at
arbitrary `c`, `k` and index type.
-/

public section

open UpperHalfPlane

open scoped ModularForm

namespace UpperHalfPlane

/-- **The zero function is zero at `im → ∞`.** This is the missing analogue of Mathlib's
`zero_form_isBoundedAtImInfty`, which covers only the bounded predicate. -/
@[simp]
lemma isZeroAtImInfty_zero {α : Type*} [Zero α] [TopologicalSpace α] :
    IsZeroAtImInfty (0 : ℍ → α) := by
  -- `IsZeroAtImInfty` is a non-`@[expose]` wrapper for `ZeroAtFilter atImInfty`; plain
  -- `simpa using` cannot cross that boundary, as `CuspForm.instZero` also finds.
  simpa using! Filter.zero_zeroAtFilter _

end UpperHalfPlane

namespace OnePoint

variable {c : OnePoint ℝ} {k : ℤ} {ι : Type*} {s : Finset ι} {F : ι → ℍ → ℂ}

/-- The zero function vanishes at every point of `OnePoint ℝ`. -/
@[simp]
lemma IsZeroAt.zero : IsZeroAt c (0 : ℍ → ℂ) k := fun _ _ ↦ by
  rw [SlashAction.zero_slash]
  exact isZeroAtImInfty_zero

/-- The zero function is bounded at every point of `OnePoint ℝ`. -/
@[simp]
lemma IsBoundedAt.zero : IsBoundedAt c (0 : ℍ → ℂ) k := fun _ _ ↦ by
  simpa only [SlashAction.zero_slash] using zero_form_isBoundedAtImInfty

/-- A finite sum of functions vanishing at `c` vanishes at `c`. -/
lemma IsZeroAt.sum (h : ∀ i ∈ s, IsZeroAt c (F i) k) : IsZeroAt c (∑ i ∈ s, F i) k :=
  Finset.sum_induction F (fun g ↦ IsZeroAt c g k) (fun _ _ ↦ IsZeroAt.add) IsZeroAt.zero h

/-- A finite sum of functions bounded at `c` is bounded at `c`. -/
lemma IsBoundedAt.sum (h : ∀ i ∈ s, IsBoundedAt c (F i) k) : IsBoundedAt c (∑ i ∈ s, F i) k :=
  Finset.sum_induction F (fun g ↦ IsBoundedAt c g k) (fun _ _ ↦ IsBoundedAt.add)
    IsBoundedAt.zero h

end OnePoint

end
