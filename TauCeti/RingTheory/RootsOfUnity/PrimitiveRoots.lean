/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# How a ring endomorphism acts on the roots of unity

In a domain the `n`-th roots of unity are exactly the powers of a primitive one, so a ring
endomorphism is pinned down on all of them by its value on a single primitive `n`-th root: if it
raises that root to the `j`-th power, it raises every `n`-th root of unity to the `j`-th power.

## Main results

* `TauCeti.IsPrimitiveRoot.map_eq_pow`: a ring endomorphism sending a primitive `n`-th root of
  unity `ζ` to `ζ ^ j` sends every `n`-th root of unity `μ` to `μ ^ j`.
-/

public section

namespace TauCeti

universe u

variable {R : Type u} [CommRing R] [IsDomain R]

/-- A ring homomorphism that raises one primitive `n`-th root of unity to the `j`-th power raises
every `n`-th root of unity to the `j`-th power, since the `n`-th roots of unity are exactly the
powers of a primitive one. -/
theorem IsPrimitiveRoot.map_eq_pow {n j : ℕ} [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n)
    (σ : R →+* R) (hσ : σ ζ = ζ ^ j) {μ : R} (hμ : μ ^ n = 1) : σ μ = μ ^ j := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [map_pow, hσ, ← pow_mul, ← pow_mul, Nat.mul_comm]

end TauCeti
