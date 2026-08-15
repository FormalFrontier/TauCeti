/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# Vanishing at zero and oddness of an elliptic sequence

`IsEllipticSequence W` constrains `W` on every triple of integers. Two facts about `W` alone
follow, given that suitable terms are nonzerodivisors: `W` vanishes at `0`, and `W` is an odd
function.

Both are used elsewhere as *hypotheses*. `Descent.lean` carries `zero : W 0 = 0` and
`odd : W.Odd` on `IsEllipticNet.of_rel` and on the two equivalences, and it must: those results
reconstruct the relation from the two doubling recurrences, so they cannot assume the relation
they are proving. The lemmas here go the other way — the relation is the hypothesis — so they
apply exactly where a caller already has `IsEllipticSequence W` in hand.

## Main results

* `IsEllipticSequence.zero`: `W 0 = 0`, given that some even term is a nonzerodivisor.
* `IsEllipticSequence.neg`: `W (-m) = -W m`, given that `W 1` and `W 2` are nonzerodivisors.

Nothing else is exported. `W.Odd` unfolds to `neg`'s statement, so a second declaration for
Mathlib's spelling would be a definitional restatement; a caller wanting `W.Odd` supplies `neg`
directly. No file consumes either lemma yet — `SignEquivariance.lean` and `Descent.lean` take
`W.Odd` and `W 0 = 0` as *hypotheses* and do not import this module. The symmetrisation the
oddness proof turns on is likewise a local `have`: a step of that argument, not a fact a caller
wants.

Neither lemma is `@[simp]`, and neither can be: `W` is a variable, so `W (-m)` has a variable head
symbol and Lean rejects the attribute outright — simp would have to try the rewrite at every step.
Mathlib tags `normEDS_neg`, `preNormEDS_neg` and `complEDS_neg` because those are stated for the
*concrete* sequences, whose head symbol is a constant.

## Implementation notes

Each proof specialises the relator at indices chosen to make all but one term cancel, then
divides by the surviving nonzerodivisor.

For `zero` the choice is `(m, m, 2 * m)`: the two outer terms of `rel` coincide and cancel, and
the first collapses to `W 0 * W (2 * m) ^ 3`.

For `neg` the relator is symmetrised first. Adding `rel W p q r 0` to `rel W q p r 0` cancels the
two outer terms against each other and leaves `(W (p - q) + W (q - p)) * W (p + q) * W r ^ 2`.
Choosing `(1 - k, k + 1, 1)` puts `2` in the middle slot and `-(2 * k)` in the first, and
`(-k, k + 1, 1)` puts `1` and `-(2 * k + 1)` there; those are the even and odd cases, and they are
why both `W 1` and `W 2` are needed.

The index arithmetic is left to `ring_nf` rather than to explicit rewrites. It has to happen
*inside* `W`'s argument: `W` is opaque, so `linear_combination` cannot on its own see that
`W (1 - k - (k + 1))` and `W (-(2 * k))` are the same term.

## Provenance

Adapted from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
declarations `IsEllSequence.zero`, `IsEllSequence.sub_add_neg_sub_mul_eq_zero` — inlined here as
a local step of `neg` rather than exported — and `IsEllSequence.neg`. That file's header reads
`Authors: David Kurniadi Angdinata`; following this repository's convention for adapted material
the upstream authorship is credited here rather than in the copyright header. J. Xu is
acknowledged for the surrounding LutzNagell development — he authors `Universal.lean` and
co-authors `DivisionPolynomialOmega.lean` at the same revision — as context for this port, not as
an author of the declarations above.

The source also carries a `zero'` proved from `IsReduced R` rather than from a nonzerodivisor.
It is not ported: `zero` below is what the development uses, and `IsReduced` is a hypothesis no
consumer in this repository has.
-/

public section

open scoped nonZeroDivisors

namespace IsEllipticSequence

variable {R : Type*} [CommRing R] {W : ℤ → R}

/-- **An elliptic sequence vanishes at `0`**, given that some even term is a nonzerodivisor. -/
protected theorem zero (h : IsEllipticSequence W) (m : ℤ) (mem : W (2 * m) ∈ R⁰) : W 0 = 0 := by
  have key : W 0 * W (2 * m) ^ 3 = 0 := by
    have := h m m (2 * m)
    rw [IsEllipticNet.rel] at this
    ring_nf at this ⊢
    linear_combination this
  exact (pow_mem mem 3).2 _ key

/-- **An elliptic sequence is an odd function**, given that `W 1` and `W 2` are nonzerodivisors.

`W.Odd` is this statement, so a caller wanting Mathlib's spelling applies this directly. -/
protected theorem neg (h : IsEllipticSequence W) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰) (m : ℤ) :
    W (-m) = -W m := by
  -- Adding the relator to itself with the first two indices exchanged cancels its outer terms
  -- against each other and leaves the symmetrised first slot.
  have key : ∀ p q r : ℤ, (W (p - q) + W (q - p)) * W (p + q) * W r ^ 2 = 0 := fun p q r ↦ by
    have hpq := h p q r
    have hqp := h q p r
    rw [IsEllipticNet.rel] at hpq hqp
    ring_nf at hpq hqp ⊢
    linear_combination hpq + hqp
  rw [eq_neg_iff_add_eq_zero]
  -- `ring_nf` is what puts the indices in normal form: `W` is opaque, so `linear_combination`
  -- cannot see that `W (1 - k - (k + 1))` and `W (-(2 * k))` are the same term.
  obtain ⟨k, rfl | rfl⟩ := m.even_or_odd'
  · have := key (1 - k) (k + 1) 1
    ring_nf at this ⊢
    exact (mul_mem two (pow_mem one 2)).2 _ (by linear_combination this)
  · have := key (-k) (k + 1) 1
    ring_nf at this ⊢
    exact (mul_mem one (pow_mem one 2)).2 _ (by linear_combination this)

end IsEllipticSequence
