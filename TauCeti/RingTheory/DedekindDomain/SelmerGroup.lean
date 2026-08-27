/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.SelmerGroup

import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# Complements on the `v`-adic valuation of a unit

Mathlib's `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero` is the `v`-adic valuation
restricted to `Kˣ`, valued in `Multiplicative ℤ` rather than `ℤₘ₀`, and Mathlib relates it to
`valuation` only through the coercion `valuationOfNeZero_eq`. This file adds the triviality
criterion in the uncoerced form, and the corresponding criterion one level up, on the quotient
`Kˣ ⧸ (Kˣ)ⁿ` where the Selmer group `K⟮S, n⟯` lives: there triviality of `valuationOfNeZeroMod`
is divisibility by `n` of the valuation. That second criterion is what turns membership in
`IsDedekindDomain.selmerGroup` from a statement about a quotient into an arithmetic condition on
a representative.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_one_iff`: a unit has trivial `v`-adic
  `valuationOfNeZero` exactly when its `v`-adic `valuation` is `1`.
* `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff`: the class of a unit
  has trivial `v`-adic `valuationOfNeZeroMod n` exactly when `n` divides its `v`-adic valuation.
* `IsDedekindDomain.HeightOneSpectrum.dvd_toAdd_valuationOfNeZero`: if the `v`-adic valuation of
  a unit is the `n`-th power of that of another unit, then `n` divides its `v`-adic order.
* `IsDedekindDomain.HeightOneSpectrum.finite_setOfPred_valuation_ne_one`: a nonzero element has
  trivial valuation at all but finitely many primes.

Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, at the `EllipticCurves` roadmap's pin
`66889eada51a`, Apache 2.0, by Michael Stoll) reaches for a
`HeightOneSpectrum.valuationOfNeZero_eq_iff` in this role; no such lemma exists at our Mathlib
pin, so it is supplied here, with `valuationOfNeZero_eq_one_iff` as its `m = 1` case.
`valuationOfNeZeroMod_mk_eq_one_iff`, `dvd_toAdd_valuationOfNeZero` and
`finite_setOfPred_valuation_ne_one` are adapted from that source's
`EllipticCurves/Mathlib/Basic.lean`. Following this repository's convention for adapted material,
the upstream authorship is credited here rather than in the copyright header.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The `Multiplicative ℤ`-valued valuation of a unit is determined by the `ℤᵐ⁰`-valued one.
Mathlib carries only the coerced form `valuationOfNeZero_eq`, which this complements. -/
theorem valuationOfNeZero_eq_iff (v : HeightOneSpectrum R) (u : Kˣ) (m : Multiplicative ℤ) :
    v.valuationOfNeZero u = m ↔ v.valuation K (u : K) = (m : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq]

/-- A unit has trivial `v`-adic `valuationOfNeZero` iff its `v`-adic valuation is `1`, the case
`m = 1` of `valuationOfNeZero_eq_iff`. -/
@[simp]
theorem valuationOfNeZero_eq_one_iff (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuationOfNeZero x = 1 ↔ v.valuation K (x : K) = 1 := by
  simpa using valuationOfNeZero_eq_iff v x 1

/-- The class of a unit `u` in `Kˣ ⧸ (Kˣ)ⁿ` has trivial `v`-adic valuation mod `n` exactly when
`n` divides the `v`-adic valuation of `u`. Membership in `IsDedekindDomain.selmerGroup` is the
conjunction of these conditions over the primes away from `S`, so this is what expresses that
membership as an arithmetic condition on a representative. -/
@[simp]
theorem valuationOfNeZeroMod_mk_eq_one_iff (v : HeightOneSpectrum R) (n : ℕ) (u : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk u) = 1 ↔
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  -- `erw`, not `rw`, for the reason Mathlib records at `valuationOfNeZeroMod` itself: that
  -- definition passes between `Multiplicative (ℤ ⧸ _)` and `Multiplicative ℤ ⧸ _` by defeq, so
  -- the two `MonoidHom`s are not syntactically composable. Mathlib's own
  -- `valuation_of_unit_mod_eq` unfolds it the same way.
  erw [valuationOfNeZeroMod, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, EmbeddingLike.map_eq_one_iff]
  refine (QuotientGroup.eq_one_iff _).trans ?_
  rw [Multiplicative.mem_toSubgroup, AddSubgroup.mem_zmultiples_iff]
  exact ⟨fun ⟨k, hk⟩ ↦ ⟨k, by rw [← hk]; ring⟩, fun ⟨k, hk⟩ ↦ ⟨k, by rw [hk]; ring⟩⟩

/-- If the valuation of a unit `u` is the `n`-th power of the valuation of a unit `z`, then the
`v`-adic order of `u` is divisible by `n`. -/
theorem dvd_toAdd_valuationOfNeZero (v : HeightOneSpectrum R) {n : ℕ} {u z : Kˣ}
    (h : v.valuation K (u : K) = v.valuation K (z : K) ^ n) :
    (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  have hu : v.valuationOfNeZero u = v.valuationOfNeZero z ^ n := by
    rw [valuationOfNeZero_eq_iff]
    push_cast
    rw [valuationOfNeZero_eq, h]
  exact ⟨Multiplicative.toAdd (v.valuationOfNeZero z), by rw [hu]; simp [toAdd_pow]⟩

/-- A nonzero element of the fraction field of a Dedekind domain has trivial valuation at all
but finitely many primes. -/
theorem finite_setOfPred_valuation_ne_one {x : K} (hx : x ≠ 0) :
    {v : HeightOneSpectrum R | v.valuation K x ≠ 1}.Finite := by
  refine ((Support.finite R x).union (Support.finite R x⁻¹)).subset fun v hv ↦ ?_
  rcases lt_or_gt_of_ne hv with h | h
  · refine .inr ?_
    rw [Support, Set.mem_ofPred_eq, map_inv₀,
      one_lt_inv₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx))]
    exact h
  · exact .inl h

end IsDedekindDomain.HeightOneSpectrum

end
