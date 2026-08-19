/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Power subfields of a rational function field

For a field `K` and an exponent `n`, this file computes the degree of `K(X)` over the subfield
`K(X ^ n)`.

## Main result

* `TauCeti.RatFunc.finrank_adjoin_X_pow`: `[K(X) : K(X ^ n)] = n`.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 1**. The relative and finite-field Frobenius
degree computations use this as the inner degree in the tower `K(W) / K(x) / K(x^n)`.

## Provenance

The statement was extracted while porting the finite-field Frobenius tower from the AINTLIB
`HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by that roadmap at
`dev/hasse-weil @ 513e83879e2f`). The source proves only the finite-field exponent; the arbitrary
field and exponent statement here is new, and follows directly from Mathlib's rational-function
degree formula.
-/

public section

open Polynomial

namespace TauCeti.RatFunc

/-- **`[K(X) : K(X ^ n)] = n`** for any field `K` and any `n`. At `n = 0` both sides read `0`:
`K⟮1⟯` is `K`, over which `K(X)` is infinite-dimensional, and `Module.finrank` reports `0`. -/
@[simp]
theorem finrank_adjoin_X_pow (K : Type*) [Field K] (n : ℕ) :
    Module.finrank (IntermediateField.adjoin K {(_root_.RatFunc.X : _root_.RatFunc K) ^ n})
      (_root_.RatFunc K) = n := by
  -- `X ^ n` as the image of a polynomial, so that `finrank_eq_max_natDegree` reads its
  -- numerator and denominator off `X ^ n` and `1`
  rw [← _root_.RatFunc.algebraMap_X, ← map_pow, _root_.RatFunc.finrank_eq_max_natDegree,
    _root_.RatFunc.num_algebraMap, _root_.RatFunc.denom_algebraMap, natDegree_X_pow,
    natDegree_one, Nat.max_zero]

end TauCeti.RatFunc

end
