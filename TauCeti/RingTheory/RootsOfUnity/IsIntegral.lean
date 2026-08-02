/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Roots of unity are integral over `ℤ`

Mathlib's `IsPrimitiveRoot.isIntegral` proves that a primitive `n`-th root of unity in a
commutative ring is integral over `ℤ`, exhibiting it as a root of the monic integer polynomial
`X ^ n - 1`. That witness makes no use of primitivity, so the statement holds for every `n`-th root
of unity; this file records that version.

## Main results

* `TauCeti.isIntegral_of_pow_eq_one`: an `n`-th root of unity in a commutative ring, `n ≠ 0`, is
  integral over `ℤ`.
-/

public section

namespace TauCeti

open Polynomial

/-- A root of unity in a commutative ring is integral over `ℤ`: it is a root of the monic
integer polynomial `X ^ n - 1`. This drops the primitivity hypothesis of
`IsPrimitiveRoot.isIntegral`, which the same proof never uses. -/
theorem isIntegral_of_pow_eq_one {A : Type*} [CommRing A] {μ : A} {n : ℕ} (hn : n ≠ 0)
    (hμ : μ ^ n = 1) : IsIntegral ℤ μ :=
  ⟨X ^ n - 1, by simpa using monic_X_pow_sub_C (1 : ℤ) hn, by simp [hμ]⟩

end TauCeti
