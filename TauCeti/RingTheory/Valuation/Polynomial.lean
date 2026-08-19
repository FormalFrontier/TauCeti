/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Polynomial expressions in the integers of a valuation

A valuation which is trivial on a base ring takes value at most `1` on every polynomial expression
in an element of value at most `1`. Concretely, the ring of integers `v.integer` is a subring
containing the image of the base ring, so it contains every `aeval t p` with `t` in it; the proof
below is the ultrametric bound on the coefficient sum, which is what `Valuation` supplies directly.

## Main results

* `Valuation.aeval_le_one`: `v (Polynomial.aeval t p) ≤ 1` whenever `v t ≤ 1` and `v` is trivial
  on the coefficient ring.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 0–1 infrastructure: the place-at-infinity
argument for isogenies in
`AlgebraicGeometry/EllipticCurve/Isogeny/InfinityPlace.lean` needs exactly this to see that a
pulled-back affine function of a Weierstrass curve — a polynomial in the pulled-back coordinates —
stays in the valuation ring at infinity. The statement is about a valuation and a polynomial and
nothing else, so it is stated here rather than there.
-/

public section

namespace Valuation

variable {R L Γ₀ : Type*} [CommSemiring R] [CommRing L] [Algebra R L]
  [LinearOrderedCommMonoidWithZero Γ₀]

/-- **A valuation trivial on the coefficients is at most `1` on polynomial expressions in an
element of the integers.** -/
theorem aeval_le_one (v : Valuation L Γ₀) [v.IsTrivialOn R] {t : L} (ht : v t ≤ 1)
    (p : Polynomial R) : v (Polynomial.aeval t p) ≤ 1 := by
  rw [Polynomial.aeval_eq_sum_range]
  refine v.map_sum_le fun i _ ↦ ?_
  rw [Algebra.smul_def, v.map_mul, v.map_pow]
  exact mul_le_one' (IsTrivialOn.valuation_algebraMap_le_one v _) (pow_le_one' ht i)

end Valuation

end
