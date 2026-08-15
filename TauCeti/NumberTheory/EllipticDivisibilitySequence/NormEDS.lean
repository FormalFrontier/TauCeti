/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Descent
public import TauCeti.NumberTheory.EllipticDivisibilitySequence.Universal

/-!
# A normalised EDS is an elliptic sequence

`normEDS b c d` is defined by the doubling recursion, so it satisfies that recursion by
construction. This file draws the consequence: it satisfies the full three-index elliptic
relation, for arbitrary `b`, `c`, `d` in any commutative ring.

This is the first half of the TODO Mathlib records at
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:70`, "prove that `normEDS` satisfies
`IsEllipticDvdSequence`". That predicate is `IsEllipticSequence ∧ IsDvdSequence`; the second
conjunct needs a general `normEDS_mul_complEDS`, of which Mathlib has only the `k = 2` case, and
is left to its own slice.

## Main results

* `isEllipticSequence_normEDS`: `IsEllipticSequence (normEDS b c d)`, with no hypothesis on the
  parameters.

## Implementation notes

The direct argument needs `normEDS b c d 2 = b` to be a nonzerodivisor, which is a genuine
constraint on `b`. It is avoided by proving the statement over `ℤ[B, C, D]` first, where the
second term is the indeterminate `X B` and is a nonzerodivisor because a polynomial ring over a
domain is a domain, and then transporting along `aeval`. Every `normEDS b c d` is such a
specialisation of `universalNormEDS`, which is what `normEDS_eq_aeval` says, so the hypothesis
survives only in the private helper, applied once at the indeterminates.

`Universal.lean` records `universalNormEDS_ne_zero` and `universalNormEDS_mem_nonZeroDivisors`
as belonging with "whichever slice ports" the fact proved here. They are still not ported: they
rest on `normEDS 2 3 2 = id`, which additionally needs an extensionality principle for elliptic
sequences that this repository does not yet have. This file is the prerequisite they were
waiting on, not the slice that lands them.

## Provenance

Adapted from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
declarations `IsEllSequence.normEDS_of_mem_nonZeroDivisors` and `IsEllSequence.normEDS`. That
file's header reads `Authors: David Kurniadi Angdinata`; following this repository's convention for
adapted material the upstream authorship is credited here rather than in the copyright header. J.
Xu is acknowledged for the surrounding LutzNagell development — he authors `Universal.lean` and
co-authors `DivisionPolynomialOmega.lean` at the same revision — as context for this port, not as
an author of the declarations above.

The source proves the hypothesis-carrying version from its own descent development; here that
step is `isEllipticSequence_iff`, so the helper is six lines rather than a file. The universal
transport is the source's argument, with `normEDS_eq_aeval` in place of its inline rewriting.
-/

public section

open scoped nonZeroDivisors
open MvPolynomial NormEDSParam

variable {R : Type*} [CommRing R] {b c d : R}

/-- **A normalised EDS is an elliptic sequence, given that `b` is a nonzerodivisor.** Superseded
by `isEllipticSequence_normEDS`, which carries no hypothesis; this is the form that transports. -/
private theorem isEllipticSequence_normEDS_of_mem (hb : b ∈ R⁰) :
    IsEllipticSequence (normEDS b c d) := by
  refine (isEllipticSequence_iff (fun k ↦ normEDS_neg b c d k) (normEDS_zero b c d)
    (by simp [normEDS_one]) (by simpa [normEDS_two] using hb)).mpr ⟨fun m _ ↦ ?_, fun m _ ↦ ?_⟩
  · simpa [normEDS_one] using normEDS_odd b c d m
  -- `linear_combination` needs `normEDS _ _ _ 2` and `… 1` as `b` and `1` before it can match.
  · simp only [normEDS_one, normEDS_two, one_pow, mul_one]
    linear_combination normEDS_even b c d m

/-- **A normalised EDS is an elliptic sequence.** No hypothesis on `b`, `c`, `d`. -/
theorem isEllipticSequence_normEDS (b c d : R) : IsEllipticSequence (normEDS b c d) := by
  -- Supply the defining equation rather than leaving it to `isDefEq`: `universalNormEDS`'s body
  -- is not exposed, so unification cannot cheaply see it as `normEDS (X B) (X C) (X D)`.
  have huniv : IsEllipticSequence (universalNormEDS : ℤ → MvPolynomial NormEDSParam ℤ) := by
    have hfun : (universalNormEDS : ℤ → MvPolynomial NormEDSParam ℤ)
        = normEDS (X B) (X C) (X D) := funext universalNormEDS_apply
    rw [hfun]
    exact isEllipticSequence_normEDS_of_mem (mem_nonZeroDivisors_of_ne_zero (X_ne_zero B))
  intro p q r
  -- `map_rel` is stated for `f ∘ W`, `normEDS_eq_aeval` for the eta-expanded lambda.
  rw [normEDS_eq_aeval (b := b) (c := c) (d := d), ← Function.comp_def,
    ← IsEllipticNet.map_rel, huniv, map_zero]
