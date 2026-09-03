/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
public import TauCeti.RingTheory.DedekindDomain.Ideal

/-!
# The `Multiplicative ℤ`-valued adic valuation of a unit

Mathlib attaches to a height one prime `v` of a Dedekind domain `R` a homomorphism
`v.valuationOfNeZero : Kˣ →* Multiplicative ℤ`, the `v`-adic valuation of a unit of the fraction
field read without the adjoined zero, and relates it to `v.valuation K` in one direction only:
`valuationOfNeZero_eq` coerces it into `ℤᵐ⁰`. This file supplies the two complements that make it
usable as a rewriting rule, together with two lemmas transporting it along a compatible pair of
embeddings of Dedekind domains and their fraction fields.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_iff`: the `Multiplicative ℤ`-valued
  valuation of a unit is determined by the `ℤᵐ⁰`-valued one.
* `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_one_iff`: its `m = 1` case, that a unit
  has trivial `v`-adic `valuationOfNeZero` exactly when its `v`-adic valuation is `1`.
* `IsDedekindDomain.HeightOneSpectrum.exists_valuationOfNeZero_map_eq`: along a pair of compatible
  embeddings `ψ : B →+* C` of Dedekind domains and `φ : L →+* N` of their fraction fields, the
  `w`-adic valuation of `φ u` is the valuation of `u` at the contracted prime raised to a fixed
  power — the ramification index of `w` over that contraction.
* `IsDedekindDomain.HeightOneSpectrum.dvd_toAdd_valuationOfNeZero_map`: consequently divisibility
  of the valuation by `n` transports along such an embedding. Only the *existence* of the exponent
  matters for that, which is why the exponent is left existentially quantified above.

## Implementation notes

These live in their own module rather than beside their first consumer. `valuationOfNeZero` is
declared in `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean`, so any host must import that;
but the *generic* completion and `S`-integer APIs that need the two complements must not, in
consequence, also inherit this repository's Selmer-group development. Keeping them here lets
`TauCeti/RingTheory/DedekindDomain/AdicCompletionExtension.lean` use them without depending on
`TauCeti/RingTheory/DedekindDomain/SelmerGroup.lean`, which is downstream of it.

## Provenance

Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache 2.0, by Michael Stoll) at commit
`66889eada51a` reaches for a `HeightOneSpectrum.valuationOfNeZero_eq_iff`; no such lemma exists at
our Mathlib pin, so it is supplied here. `exists_valuationOfNeZero_map_eq` and
`dvd_toAdd_valuationOfNeZero_map` are adapted from the same source
(`EllipticCurves/Mathlib/Basic.lean`).
-/

public section

open scoped WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The `Multiplicative ℤ`-valued valuation of a unit is determined by the `ℤᵐ⁰`-valued one.
Mathlib carries only the coerced form `valuationOfNeZero_eq`, which this complements. -/
@[simp]
theorem valuationOfNeZero_eq_iff (v : HeightOneSpectrum R) (u : Kˣ) (m : Multiplicative ℤ) :
    v.valuationOfNeZero u = m ↔ v.valuation K u = (m : ℤᵐ⁰) := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq]

/-- A unit has trivial `v`-adic `valuationOfNeZero` iff its `v`-adic valuation is `1`, the case
`m = 1` of `valuationOfNeZero_eq_iff`. -/
-- Deliberately not `@[simp]`: `valuationOfNeZero_eq_iff` carries the annotation, and with both
-- marked `simpNF` rejects this one — "simp can prove this" — since the general form subsumes it.
theorem valuationOfNeZero_eq_one_iff (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuationOfNeZero x = 1 ↔ v.valuation K x = 1 := by
  simp only [valuationOfNeZero_eq_iff, WithZero.coe_one]

section Transport

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]
  {L N : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
  [Field N] [Algebra C N] [IsFractionRing C N]

/-- Along an embedding `ψ : B →+* C` of Dedekind domains and a compatible embedding `φ : L →+* N`
of their fraction fields, the `w`-adic valuation of `φ u` is the valuation of `u` at the
contracted prime `comapOfNeBot ψ w hne`, raised to a fixed power independent of `u` — namely the
ramification index of `w` over that contraction. -/
theorem exists_valuationOfNeZero_map_eq (φ : L →+* N) (ψ : B →+* C)
    (hcomp : (algebraMap C N).comp ψ = φ.comp (algebraMap B L)) (w : HeightOneSpectrum C)
    (hne : w.asIdeal.comap ψ ≠ ⊥) :
    ∃ e : ℕ, ∀ u : Lˣ, w.valuationOfNeZero (Units.map (φ : L →* N) u) =
      (comapOfNeBot ψ w hne).valuationOfNeZero u ^ e := by
  -- the tower of algebras that `valuation_liesOver` compares the two valuations along
  let _ : Algebra B C := ψ.toAlgebra
  let _ : Algebra L N := φ.toAlgebra
  let _ : Algebra B N := (φ.comp (algebraMap B L)).toAlgebra
  have hψ : Function.Injective ψ := .of_comp (f := algebraMap C N) <| by
    rw [← RingHom.coe_comp, hcomp]
    exact φ.injective.comp (IsFractionRing.injective B L)
  have : IsScalarTower B L N := .of_algebraMap_eq' rfl
  have : IsScalarTower B C N := .of_algebraMap_eq' hcomp.symm
  have : Module.IsTorsionFree B C := Module.isTorsionFree_iff_algebraMap_injective.mpr hψ
  have : w.asIdeal.LiesOver (comapOfNeBot ψ w hne).asIdeal := ⟨comapOfNeBot_asIdeal ψ w hne⟩
  refine ⟨(comapOfNeBot ψ w hne).asIdeal.ramificationIdx' w.asIdeal, fun u ↦ ?_⟩
  rw [valuationOfNeZero_eq_iff, WithZero.coe_pow, valuationOfNeZero_eq]
  exact (valuation_liesOver N (comapOfNeBot ψ w hne) w (u : L)).symm

/-- Divisibility of adic valuations transports along compatible embeddings: if the valuation of
`u` at the contracted prime is divisible by `n`, so is the `w`-adic valuation of `φ u`.

This is the form in which the semilocal comparison of `2`-descent uses
`exists_valuationOfNeZero_map_eq`: ramification multiplies the valuation by a fixed factor, and
multiplication preserves divisibility, so parity — the case `n = 2` — survives in both
directions. -/
theorem dvd_toAdd_valuationOfNeZero_map (φ : L →+* N) (ψ : B →+* C)
    (hcomp : (algebraMap C N).comp ψ = φ.comp (algebraMap B L)) (w : HeightOneSpectrum C)
    (hne : w.asIdeal.comap ψ ≠ ⊥) {n : ℤ} (u : Lˣ)
    (h : n ∣ Multiplicative.toAdd ((comapOfNeBot ψ w hne).valuationOfNeZero u)) :
    n ∣ Multiplicative.toAdd (w.valuationOfNeZero (Units.map (φ : L →* N) u)) := by
  obtain ⟨e, he⟩ := exists_valuationOfNeZero_map_eq φ ψ hcomp w hne
  simpa only [he u, toAdd_pow, nsmul_eq_mul] using h.mul_left _

end Transport

end IsDedekindDomain.HeightOneSpectrum

end
