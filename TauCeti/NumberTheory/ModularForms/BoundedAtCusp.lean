/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

/-!
# Vanishing and boundedness at a cusp are closed under finite sums and scalars

Mathlib's `OnePoint.IsZeroAt` and `OnePoint.IsBoundedAt` are closed under binary sums
(`OnePoint.IsZeroAt.add`, `OnePoint.IsBoundedAt.add`), but the zero function and a
`Finset.sum` are not recorded. Nor is scaling by a constant: `Filter.ZeroAtFilter.smul` and
`Filter.BoundedAtFilter.smul` supply that one level down, but carrying them up to the cusp
predicate has to cross the `σ`-twist of `ModularForm.smul_slash`. This file adds all three.

The gap matters for the Hecke operators, which are finite sums of slashes: a proof that such
an operator preserves vanishing at the cusps is an induction over the summands, and without
`OnePoint.IsZeroAt.sum` each call site has to rerun that induction by hand. The scalar half is
what the nebentypus twist needs, where each summand carries a character value as its weight.

## Main declarations

* `UpperHalfPlane.isZeroAtImInfty_zero`: the zero analogue of Mathlib's
  `zero_form_isBoundedAtImInfty`, which is absent upstream.
* `OnePoint.IsZeroAt.zero`, `OnePoint.IsBoundedAt.zero`: the zero function vanishes, and is
  bounded, at every point of `OnePoint ℝ`.
* `OnePoint.IsZeroAt.sum`, `OnePoint.IsBoundedAt.sum`: a finite sum of functions vanishing
  (resp. bounded) at `c` vanishes (resp. is bounded) at `c`.
* `OnePoint.IsZeroAt.const_smul`, `OnePoint.IsBoundedAt.const_smul`: both properties survive
  scaling by a constant.

## Provenance

No code is transcribed here. The gap the zero and sum lemmas fill was identified from the
AINTLIB `LeanModularForms` project (Chris Birkbeck, Apache-2.0):
`LeanModularForms/HeckeRIngs/GL2/AdjointTheory.lean` lines 62-70, at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`. Its `heckeT_p_ut_zero_at_cusps` open-codes this
induction with `Finset.sum_induction`, and obtains the base case by constructing a zero
`CuspForm` purely to invoke `zero_at_cusps'` — because `IsZeroAt c 0 k` is not stated anywhere.
The `const_smul` pair has a different origin: it is the scalar step the nebentypus-twisted
slash sum needs, and is not open-coded in that source. All the statements below are about
Mathlib's `OnePoint.IsZeroAt`/`IsBoundedAt`, at arbitrary `c` and `k` (and, for the sums, an
arbitrary index type).
-/

public section

open UpperHalfPlane

namespace UpperHalfPlane

/-- **The zero function is zero at `im → ∞`.** This is the missing analogue of Mathlib's
`zero_form_isBoundedAtImInfty`, which covers only the bounded predicate. -/
-- `IsZeroAtImInfty` is a semireducible wrapper for `ZeroAtFilter atImInfty`, so `simp`, `exact?`
-- and `simpa ... using` all match only reducibly and fail; cf. Mathlib's `CuspForm.instZero`.
@[simp]
lemma isZeroAtImInfty_zero {α : Type*} [Zero α] [TopologicalSpace α] :
    IsZeroAtImInfty (0 : ℍ → α) := Filter.zero_zeroAtFilter _

end UpperHalfPlane

namespace OnePoint

variable {c : OnePoint ℝ} {k : ℤ} {ι : Type*} {s : Finset ι} {F : ι → ℍ → ℂ}

/-- The zero function vanishes at every point of `OnePoint ℝ`. -/
@[simp]
lemma IsZeroAt.zero : IsZeroAt c 0 k := fun _ _ ↦ by simp

/-- The zero function is bounded at every point of `OnePoint ℝ`. -/
@[simp]
lemma IsBoundedAt.zero : IsBoundedAt c 0 k := fun _ _ ↦ by
  simpa using zero_form_isBoundedAtImInfty

/-- A finite sum of functions vanishing at `c` vanishes at `c`. -/
lemma IsZeroAt.sum (h : ∀ i ∈ s, IsZeroAt c (F i) k) : IsZeroAt c (∑ i ∈ s, F i) k :=
  Finset.sum_induction F (IsZeroAt c · k) (fun _ _ ↦ .add) IsZeroAt.zero h

/-- A finite sum of functions bounded at `c` is bounded at `c`. -/
lemma IsBoundedAt.sum (h : ∀ i ∈ s, IsBoundedAt c (F i) k) : IsBoundedAt c (∑ i ∈ s, F i) k :=
  Finset.sum_induction F (IsBoundedAt c · k) (fun _ _ ↦ .add) IsBoundedAt.zero h

/-- Vanishing at `c` survives scaling by a constant. -/
lemma IsZeroAt.const_smul {f : ℍ → ℂ} (a : ℂ) (hf : IsZeroAt c f k) :
    IsZeroAt c (a • f) k := fun g hg ↦ by
  -- `ModularForm.smul_slash` twists the scalar to `σ g a` when `g` has negative determinant;
  -- that twist is immaterial, since vanishing along `atImInfty` is preserved by *any* scalar.
  rw [ModularForm.smul_slash]
  exact (hf g hg).smul _

/-- Boundedness at `c` survives scaling by a constant. -/
lemma IsBoundedAt.const_smul {f : ℍ → ℂ} (a : ℂ) (hf : IsBoundedAt c f k) :
    IsBoundedAt c (a • f) k := fun g hg ↦ by
  -- `ModularForm.smul_slash` twists the scalar to `σ g a` when `g` has negative determinant;
  -- that twist is immaterial, since boundedness along `atImInfty` is preserved by *any* scalar.
  rw [ModularForm.smul_slash]
  exact (hf g hg).smul _

end OnePoint

end
