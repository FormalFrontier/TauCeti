/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `dotProductBilin` and `dotProductEquiv` occur in the statement and the body below.
public import Mathlib.LinearAlgebra.Matrix.Dual
-- `LinearMap.IsPerfPair` occurs in the statement below.
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

public section

/-!
# The dot product on `ι → R` is a perfect pairing

Mathlib's `dotProductEquiv` identifies `ι → R`, for `ι` finite, with its own dual under the dot
product. This file records the same fact in the form asked for by `LinearMap.IsPerfPair`, so that
the dot product may be used directly as the pairing of a `RootPairing` or a `RootDatum` on `ι → R`.

## Main results

* `TauCeti.dotProductBilin_isPerfPair`: the dot product `dotProductBilin R R` on `ι → R` is a
  perfect pairing of that module with itself.
-/

namespace TauCeti

open _root_.Matrix

/-- The dot product on `ι → R` is a perfect pairing of that module with itself: it is Mathlib's
`dotProductEquiv` read as a bilinear map. -/
instance dotProductBilin_isPerfPair (R ι : Type*) [CommRing R] [Fintype ι] :
    (dotProductBilin R R : (ι → R) →ₗ[R] (ι → R) →ₗ[R] R).IsPerfPair := by
  classical
  have h : (dotProductBilin R R : (ι → R) →ₗ[R] (ι → R) →ₗ[R] R) =
      (dotProductEquiv R ι).toLinearMap := by
    ext x y
    simp
  rw [h]
  infer_instance

end TauCeti
