/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# When the different ideal is the unit ideal

Let `A` be an integrally closed domain with fraction field `K` and let `B` be a Dedekind domain
with fraction field `L`, integral over `A`, with `L / K` finite and separable.  Mathlib's
`differentIdeal A B` is the inverse of the trace dual `Bᵛ = {x ∈ L | Tr_{L/K} (x · B) ⊆ A}` of `B`,
so it is the unit ideal exactly when `B` is its own trace dual.  This file records that criterion
and the concrete test that decides it: a `K`-basis of `L` that spans `B` over `A` and whose
trace-dual basis spans `B` as well.

Mathlib's `not_dvd_differentIdeal_iff` decides divisibility of the different ideal by one prime at
a time; the statements here are the global ones, and dispose of all primes at once.

## Main results

* `TauCeti.differentIdeal_eq_top_iff_traceDual_eq_one`: the different ideal is the unit ideal
  exactly when `B` is its own trace dual.
* `TauCeti.differentIdeal_eq_top_of_span_eq_one`: the basis form of that criterion.
-/

public section

open Module Submodule

open scoped nonZeroDivisors

namespace TauCeti

variable (A K : Type*) {B L : Type*}
variable [CommRing A] [Field K] [CommRing B] [Field L]
variable [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsDomain A] [IsFractionRing A K] [IsFractionRing B L]
variable [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L]

/-- **The different ideal is the unit ideal exactly when `B` is its own trace dual.**  The
different ideal is the inverse of the trace dual as a fractional ideal, and inversion is
injective on the nonzero ones. -/
theorem differentIdeal_eq_top_iff_traceDual_eq_one :
    differentIdeal A B = ⊤ ↔ Submodule.traceDual A K (1 : Submodule B L) = 1 := by
  have hdual : FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) = 1 ↔
      Submodule.traceDual A K (1 : Submodule B L) = 1 := by
    rw [← FractionalIdeal.coeToSubmodule_inj (J := (1 : FractionalIdeal B⁰ L)),
      FractionalIdeal.coe_dual_one, FractionalIdeal.coe_one]
  rw [← hdual, ← Ideal.one_eq_top, ← FractionalIdeal.coeIdeal_eq_one (K := L),
    coeIdeal_differentIdeal (A := A) (K := K) (L := L) (B := B), inv_eq_one]

/-- **A self-dual integral basis makes the different ideal the unit ideal**: if a `K`-basis of `L`
spans `B` over `A`, and so does its trace-dual basis, then `B` is its own trace dual, because the
trace dual of a span is the span of the trace-dual basis. -/
theorem differentIdeal_eq_top_of_span_eq_one {ι : Type*} [Finite ι] [DecidableEq ι]
    (b : Basis ι K L)
    (hb : Submodule.span A (Set.range b) = (1 : Submodule B L).restrictScalars A)
    (hb' : Submodule.span A (Set.range b.traceDual) = (1 : Submodule B L).restrictScalars A) :
    differentIdeal A B = ⊤ := by
  rw [differentIdeal_eq_top_iff_traceDual_eq_one A K (L := L)]
  refine Submodule.restrictScalars_injective A _ _ ?_
  rw [Submodule.traceDual_span_of_basis A _ b hb.symm, hb']

end TauCeti

end
