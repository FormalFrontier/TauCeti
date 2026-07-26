/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Span

/-!
# Membership of integers in an ideal lying over `(a)`

For an ideal `Q` of a `ℤ`-algebra lying over the integer ideal `(a)`
(`Ideal.LiesOver`), an integer `m` maps into `Q` exactly when `a ∣ m`. This unfolds
`Ideal.mem_of_liesOver` through `Ideal.mem_span_singleton` once, so that arithmetic arguments
can move between divisibility in `ℤ` and membership in `Q` without repeating the two-step
translation.

It is the shared translation step of the multiquadratic Layer 1 arguments: the splitting law
and the Frobenius computations each convert congruences modulo a prime `Q` over `p` into
divisibility by `p`.

## Main result

* `TauCeti.algebraMap_int_mem_iff_dvd_of_liesOver`: `algebraMap ℤ S m ∈ Q ↔ a ∣ m`.
-/

public section

open Ideal

namespace TauCeti

/-- An ideal of a `ℤ`-algebra lying over the integer ideal `(a)` meets `ℤ` exactly in the
multiples of `a`: `algebraMap ℤ S m ∈ Q ↔ a ∣ m`. -/
theorem algebraMap_int_mem_iff_dvd_of_liesOver {S : Type*} [CommRing S] {a : ℤ}
    (Q : Ideal S) [Q.LiesOver (span {a})] (m : ℤ) :
    algebraMap ℤ S m ∈ Q ↔ a ∣ m :=
  (Ideal.mem_of_liesOver Q (span {a}) m).symm.trans Ideal.mem_span_singleton

end TauCeti
