/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Ring.NonZeroDivisors
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Elementary
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Recurrence

/-!
# An elliptic sequence is determined by its first four terms

Two elliptic sequences that agree at `1, 2, 3, 4` are equal, provided the first two terms are
nonzerodivisors. The two doubling recurrences determine every later term from a bounded window of
earlier ones — five for the even step, four for the odd — `Elementary.lean` supplies the value at
`0` and the behaviour at negative indices, and `normEDSRec` is the induction that puts those
together.

## Main results

* `IsEllipticSequence.ext`: `W = U` from agreement at `1, 2, 3, 4`.

## Implementation notes

The recurrences give the doubled-index term only up to a nonzerodivisor factor — `W 2 * W 1 ^ 2`
at even indices and `W 1 ^ 3` at odd ones, which is exactly the shape `Recurrence.lean`'s
docstring flags as needing "a hypothesis this file does not carry". Each inductive step therefore
cancels that factor before comparing, which is where `one` and `two` are used.

`normEDSRec` is indexed by `ℕ` while the recurrences are stated over `ℤ`, so each step pushes the
cast through before rewriting; `Int.negInduction` then reduces negative indices to nonnegative
ones through oddness.

The index arithmetic then needs `ring_nf`. `rel_even` at `m + 3` writes its indices as `m + 3 - 1`
and so on, while the induction hypotheses are stated at `m + 2`; `W` is opaque, so nothing equates
those two terms until both are in normal form. Once they are, rewriting the hypotheses through the
`W` side of the recurrence leaves it with the same right-hand side as the `U` side, and the two
subtract.

## Provenance

Adapted from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
declaration `IsEllSequence.ext`. That file's header reads
`Authors: David Kurniadi Angdinata`; following this repository's convention for adapted material
the upstream authorship is credited here rather than in the copyright header. J. Xu is
acknowledged for the surrounding LutzNagell development — he authors `Universal.lean` and
co-authors `DivisionPolynomialOmega.lean` at the same revision — as context for this port, not as
an author of the declaration above.

The source derives the value at `0` and the oddness inline from its own `zero` and `neg`; here
those are `Elementary.lean`'s `IsEllipticSequence.zero` and `IsEllipticSequence.neg`, so this file
is the induction alone.
-/

public section

open scoped nonZeroDivisors

namespace IsEllipticSequence

variable {R : Type*} [CommRing R] {W U : ℤ → R}

/-- **An elliptic sequence is determined by its first four terms.** Two elliptic sequences
agreeing at `1, 2, 3, 4` are equal, given that `W 1` and `W 2` are nonzerodivisors. -/
protected theorem ext (hW : IsEllipticSequence W) (hU : IsEllipticSequence U)
    (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
    (h1 : W 1 = U 1) (h2 : W 2 = U 2) (h3 : W 3 = U 3) (h4 : W 4 = U 4) : W = U := by
  have twoU : U 2 ∈ R⁰ := h2 ▸ two
  have oneU : U 1 ∈ R⁰ := h1 ▸ one
  funext n
  induction n using Int.negInduction with
  | nat n =>
    refine normEDSRec ?_ h1 h2 h3 h4 (fun m e1 e2 e3 e4 e5 ↦ ?_) (fun m e1 e2 e3 e4 ↦ ?_) n
    · rw [Nat.cast_zero, hW.zero 1 (by simpa using two), hU.zero 1 (by simpa using twoU)]
    · have hw := hW.rel_even (m + 3)
      have hu := hU.rel_even (m + 3)
      push_cast at e1 e2 e3 e4 e5 ⊢
      rw [← mul_cancel_right_mem_nonZeroDivisors (mul_mem two (pow_mem one 2))]
      ring_nf at hw hu e1 e2 e3 e4 e5 ⊢
      rw [e1, e2, e3, e4, e5, h1, h2] at hw
      rw [h1, h2]
      linear_combination hw - hu
    · have hw := hW.rel_odd (m + 2)
      have hu := hU.rel_odd (m + 2)
      push_cast at e1 e2 e3 e4 ⊢
      rw [← mul_cancel_right_mem_nonZeroDivisors (pow_mem one 3)]
      ring_nf at hw hu e1 e2 e3 e4 ⊢
      rw [e1, e2, e3, e4, h1] at hw
      rw [h1]
      linear_combination hw - hu
  | neg hn n => rw [hW.neg one two, hU.neg oneU twoU, hn]

end IsEllipticSequence
