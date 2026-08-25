/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.SelmerGroup

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

Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, at the `EllipticCurves` roadmap's pin
`66889eada51a`, Apache 2.0, by Michael Stoll) reaches for a
`HeightOneSpectrum.valuationOfNeZero_eq_iff` in this role; no such lemma exists at our Mathlib
pin, so `valuationOfNeZero_eq_one_iff` supplies it. `valuationOfNeZeroMod_mk_eq_one_iff` is
adapted from that source's `EllipticCurves/Mathlib/Basic.lean`. Following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A unit has trivial `v`-adic `valuationOfNeZero` iff its `v`-adic valuation is `1`. Mathlib
carries this only in the coerced form `valuationOfNeZero_eq`, which this complements. -/
@[simp]
theorem valuationOfNeZero_eq_one_iff (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuationOfNeZero x = 1 ↔ v.valuation K (x : K) = 1 := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq, WithZero.coe_one]

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

end IsDedekindDomain.HeightOneSpectrum

end
