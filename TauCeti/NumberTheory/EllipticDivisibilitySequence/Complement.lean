/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.EllipticDivisibilitySequence.NormEDS

/-!
# The complement of a normalised EDS at a general multiple

Mathlib defines `complEDS b c d k` to witness `normEDS b c d k ∣ normEDS b c d (n * k)`, but
proves the witnessing identity `normEDS b c d k * complEDS b c d k n = normEDS b c d (n * k)`
only at `k = 2`, as `normEDS_mul_complEDS₂`. This file proves it at every `k`, on the hypothesis
that `normEDS b c d k` is a nonzerodivisor.

That identity is the second conjunct of the TODO Mathlib records at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:70`, "prove that `normEDS` satisfies
`IsEllipticDvdSequence`". `NormEDS.lean` discharges the first conjunct and names this one as a
slice of its own.

## Main results

* `normEDS_mul_complEDS_of_mem_nonZeroDivisors`:
  `normEDS b c d k * complEDS b c d k n = normEDS b c d (n * k)`, for every `n`, over any
  commutative ring, whenever `normEDS b c d k` is a nonzerodivisor.

## Implementation notes

The nonzerodivisor hypothesis is what the induction consumes. The odd step derives the identity
multiplied through by `normEDS b c d k`, and cancelling that factor is the only use of `hk`; the
even step and both base cases are unconditional. It is removable by specialising from the
universal parameters, where the sequence is a nonzerodivisor at every index — the route
`NormEDS.lean` takes for `isEllipticNet_normEDS`. That is now available: `universalNormEDS_ne_zero`
(`NormEDS.lean`) gives the nonvanishing, and `mem_nonZeroDivisors_of_ne_zero` turns it into the
hypothesis this induction consumes, `ℤ[B, C, D]` being a domain.

The elliptic relation is instantiated once, at `ER((j + 2) * k, 1, (j + 1) * k, 0)`. Its middle
term is then `W((2 * j + 3) * k) * W k`, the odd step's right-hand side times the factor to be
cancelled, and its two outer terms are the products the recursion produces.

`IsEllipticNet.rel` holds its indices unnormalised — `W (p + q + s)` at `s = 0`, `W (q - r)`
where the goal has `W (r - q)` — so the instance and the goal disagree on the *arguments* of
`normEDS`, which are atoms to `ring`. `linear_combination`'s default `ring1` closer does not
descend into an atom's arguments, so the norm is switched to `ring_nf`, which does. That covers
every index mismatch except the reflected one: `W (1 - x) = -W (x - 1)` is `normEDS_neg`, a fact
about the sequence rather than about `ℤ`, and is the single rewrite done by hand.

## Provenance

Adapted from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at `dev/modular-curves @ 9fec8eba7652` — the revision
`TauCetiRoadmap/EllipticCurves/README.md` pins for the NagellLutz project. Source declaration
`normEDS_mul_complEDS_of_mem` (`:1324`), which is `private` there and public here, being this
slice's deliverable rather than a step; the name gains Mathlib's full `_of_mem_nonZeroDivisors`
suffix. That file's header reads `Authors: David Kurniadi Angdinata`; following this repository's
convention for adapted material the upstream authorship is credited here rather than in the
copyright header.

Three departures from the source, all forced by Mathlib having since absorbed the construction.

The source builds a *general* complement `EllSequence.compl'`, parametric in two sequences `W₁`
and `compl₂`, and obtains this identity by specialising a general lemma about it at
`W₁ := normEDS b c d` and `compl₂ := compl₂EDS b c d`. Mathlib's `complEDS'` is that construction
with exactly those two arguments already substituted, and Mathlib defines it directly rather than
through a general `compl`, so porting the general version would duplicate `complEDS'` without
making it derivable. The induction is run on `complEDS` itself instead.

The source's hypothesis `b ∈ R⁰` is dropped. It is needed there because the `n = 0` base case
goes through `IsEllSequence.zero`, which asks for `W 2 = b` to be a nonzerodivisor; Mathlib's
`normEDS_zero` gives `W 0 = 0` outright.

The source splits at the `ℕ` level and unfolds `compl'`, because it has no `ℤ`-level recurrence.
Mathlib states `complEDS_even` and `complEDS_odd` over `ℤ`, so the `Int.sign`/`Int.natAbs`
bookkeeping disappears and the even step is four rewrites.
-/

public section

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] {b c d : R}

/-- **The complement of a normalised EDS witnesses divisibility at every multiple.**

`complEDS b c d k n` is Mathlib's division-free candidate for `W (n * k) / W k`; this is the
identity that makes it one, given that `normEDS b c d k` is a nonzerodivisor. -/
theorem normEDS_mul_complEDS_of_mem_nonZeroDivisors {k : ℤ} (hk : normEDS b c d k ∈ R⁰) (n : ℤ) :
    normEDS b c d k * complEDS b c d k n = normEDS b c d (n * k) := by
  induction n using Int.negInduction with
  | nat n =>
    refine n.strong_induction_on fun n ih ↦ ?_
    obtain _ | _ | n := n
    · simp
    · simp
    -- Mathlib states the two recurrences at the `ℤ` level, so split there rather than unfolding
    -- `complEDS'` at the `ℕ` level as the source does.
    obtain ⟨j, rfl | rfl⟩ := n.even_or_odd'
    · -- the index is `2 * j + 2 = 2 * (j + 1)`
      have hj : ((2 * j + 2 : ℕ) : ℤ) = 2 * (j + 1) := by push_cast; ring
      have hih := ih (j + 1) (by omega)
      -- the inductive hypothesis arrives at `↑(j + 1)`, which is not the goal's `↑j + 1`
      push_cast at hih
      rw [hj, complEDS_even, ← mul_assoc, hih, normEDS_mul_complEDS₂]
      ring_nf
    · -- the index is `2 * j + 3 = 2 * (j + 1) + 1`
      have hj : ((2 * j + 1 + 2 : ℕ) : ℤ) = 2 * (j + 1) + 1 := by push_cast; ring
      have hih₁ := ih (j + 1) (by omega)
      have hih₂ := ih (j + 2) (by omega)
      push_cast at hih₁ hih₂
      have hell := isEllipticSequence_normEDS b c d (((j : ℤ) + 2) * k) 1 (((j : ℤ) + 1) * k)
      simp only [IsEllipticNet.rel, add_zero, normEDS_one, mul_one] at hell
      -- only the reflected index needs rewriting by hand; `ring_nf` normalises the rest
      rw [show (1 : ℤ) - ((j : ℤ) + 1) * k = -(((j : ℤ) + 1) * k - 1) by ring, normEDS_neg,
        ← hih₁, ← hih₂] at hell
      rw [← mul_cancel_left_mem_nonZeroDivisors hk, hj, complEDS_odd]
      linear_combination (norm := ring_nf) hell
  | neg hn n =>
    rw [neg_mul, normEDS_neg, complEDS_neg, mul_neg, hn n]
