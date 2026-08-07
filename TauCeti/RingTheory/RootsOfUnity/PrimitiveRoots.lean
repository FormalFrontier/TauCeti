/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Primitive roots of unity: where they come from, and how an endomorphism moves them

The unit group of a finite field is cyclic, so a generator of it has a power of every order
dividing the group order: a primitive `d`-th root of unity exists for every such `d`.

In a domain the `n`-th roots of unity are exactly the powers of a primitive one, so a ring
endomorphism is pinned down on all of them by its value on a single primitive `n`-th root: if it
raises that root to the `j`-th power, it raises every `n`-th root of unity to the `j`-th power.

## Main results

* `TauCeti.exists_isPrimitiveRoot_of_dvd_card_units`: a finite field contains a primitive `d`-th
  root of unity for every `d` dividing the order of its unit group.
* `TauCeti.IsPrimitiveRoot.map_eq_pow`: a ring endomorphism sending a primitive `n`-th root of
  unity `ζ` to `ζ ^ j` sends every `n`-th root of unity `μ` to `μ ^ j`.
-/

public section

namespace TauCeti

universe u

/-- A finite field contains a primitive `d`-th root of unity for every `d` dividing the order of
its unit group, because that unit group is cyclic. -/
theorem exists_isPrimitiveRoot_of_dvd_card_units (F : Type*) [Field F] [Finite F] {d : ℕ}
    (hd : d ∣ Nat.card Fˣ) : ∃ ζ : F, IsPrimitiveRoot ζ d := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
  have hcard : Nat.card Fˣ ≠ 0 := Nat.card_pos.ne'
  refine ⟨((u ^ (Nat.card Fˣ / d) : Fˣ) : F), IsPrimitiveRoot.coe_units_iff.2 ?_⟩
  have hord : orderOf (u ^ (orderOf u / d)) = d :=
    orderOf_pow_orderOf_div (by rw [hu]; exact hcard) (by rw [hu]; exact hd)
  rw [hu] at hord
  have hprim := IsPrimitiveRoot.orderOf (u ^ (Nat.card Fˣ / d))
  rwa [hord] at hprim

variable {R : Type u} [CommRing R] [IsDomain R]

/-- A ring homomorphism that raises one primitive `n`-th root of unity to the `j`-th power raises
every `n`-th root of unity to the `j`-th power, since the `n`-th roots of unity are exactly the
powers of a primitive one. -/
theorem IsPrimitiveRoot.map_eq_pow {n j : ℕ} [NeZero n] {ζ : R} (hζ : IsPrimitiveRoot ζ n)
    (σ : R →+* R) (hσ : σ ζ = ζ ^ j) {μ : R} (hμ : μ ^ n = 1) : σ μ = μ ^ j := by
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [map_pow, hσ, ← pow_mul, ← pow_mul, Nat.mul_comm]

end TauCeti
