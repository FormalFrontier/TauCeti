/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# The doubling relations of an elliptic sequence

`IsEllipticSequence W` says that `IsEllipticNet.rel W p q r 0` vanishes for all `p, q, r`.
Mathlib's `IsEllipticNet.rel_odd` and `rel_even` evaluate that relator at the two instances
relating a doubled index to its neighbours, but they give the relator's *value* rather than the
relation that follows from its vanishing.

This file draws that consequence: from `IsEllipticSequence W`, the doubled-index term stands in a
fixed relation to its neighbours, at both parities. This is the intended interface for the
division-polynomial development, which will meet the doubling step holding `IsEllipticSequence`
rather than a relator value; no file consumes it yet.

## Main results

* `IsEllipticSequence.rel_odd`: from `IsEllipticSequence W`,
  `W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3`.
* `IsEllipticSequence.rel_even`: from `IsEllipticSequence W`,
  `W (2 * m) * W 2 * W 1 ^ 2 = W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2)`.

## Implementation notes

Each proof specialises the hypothesis at the relevant instance, rewrites with Mathlib's evaluation
of the relator there, and rearranges. Nothing intermediate is named: an earlier draft exported the
two vanishing-form equivalences as well, but their only consumers were the two lemmas below, so
they were a second public spelling of `rel_odd` / `rel_even` rather than API.

The equations **relate** the doubled-index term to its neighbours; they do not determine it.
Nothing here inverts `W 1` or `W 2 * W 1 ^ 2`, and over an arbitrary `CommRing` neither need be a
unit, so solving for `W (2 * m + 1)` or `W (2 * m)` requires a hypothesis this file does not carry.

## Provenance

Adapted from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`),
declarations `OddRec`, `EvenRec`, `rel₃_iff_oddRec` and `rel₃_iff_evenRec`. That file's header
reads `Authors: David Kurniadi Angdinata`; following this repository's convention for adapted
material the upstream authorship is credited here rather than in the copyright header. J. Xu is
acknowledged for the surrounding LutzNagell development — he authors `Universal.lean` and
co-authors `DivisionPolynomialOmega.lean` at the same revision — as context for this port, not as
an author of the declarations above.

The adaptation is substantial, because Mathlib has since absorbed most of what the source had to
build for itself. The source states its equivalences against `Rel₃`, a three-index relation of its
own, and carries `OddRec` / `EvenRec` as `Prop` definitions naming the right-hand sides. Mathlib
supplies `Rel₃` as `rel W p q r 0` — the shape `IsEllipticSequence` quantifies over — and supplies
`rel_odd` / `rel_even` as the evaluations at these two instances. What remains is the consequence
drawn here, and none of the source's four declarations survives as such.

The source's `rel₄_iff_evenRec`, a third equivalence against the four-index relator at
`(2 * m + 1, 2 * m - 1, 3, 1)`, is not ported. It is the one declaration in this group carrying
`set_option allowUnsafeReducibility true` together with an `attribute [local reducible]
Nat.rawCast`, which this repository has previously declined to take on, and it belongs with the
descent layer that consumes it.
-/

public section

namespace IsEllipticSequence

variable {R : Type*} [CommRing R] {W : ℤ → R}

/-- **The odd doubling relation of an elliptic sequence.** -/
theorem rel_odd (h : IsEllipticSequence W) (m : ℤ) :
    W (2 * m + 1) * W 1 ^ 3 = W (m + 2) * W m ^ 3 - W (m - 1) * W (m + 1) ^ 3 := by
  have hm := h (m + 1) m 1
  rw [IsEllipticNet.rel_odd] at hm
  linear_combination hm

/-- **The even doubling relation of an elliptic sequence.** -/
theorem rel_even (h : IsEllipticSequence W) (m : ℤ) :
    W (2 * m) * W 2 * W 1 ^ 2 =
      W m * (W (m - 1) ^ 2 * W (m + 2) - W (m - 2) * W (m + 1) ^ 2) := by
  have hm := h (m + 1) (m - 1) 1
  rw [IsEllipticNet.rel_even] at hm
  linear_combination hm

end IsEllipticSequence
