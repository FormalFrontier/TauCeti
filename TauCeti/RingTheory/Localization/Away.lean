/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The fraction `t/s` in an away localisation

A localisation `S` of `A` away from `s` inverts `s`, so it contains `t/s` for every `t : A`.
Mathlib names the inverse itself — `IsLocalization.Away.invSelf s` is `1/s` — but not the general
fraction; this file names it and gives the identities that manipulating it needs: scaling `1/s`
by `t`, and clearing the denominator on either side.

Nothing here is topological or Huber-specific — it is `IsLocalization` algebra over an arbitrary
commutative semiring, for an arbitrary localisation away from `s` — so it is stated outside the
Huber namespace, alongside `TauCeti/RingTheory/Localization/DenIdeal.lean`.

## Main definitions

* `TauCeti.Localization.divBy`: the element `t/s` of a localisation away from `s`.

## Main results

* `TauCeti.Localization.divBy_one`: `1/s` is Mathlib's `IsLocalization.Away.invSelf`.
* `TauCeti.Localization.invSelf_mul_algebraMap`: scaling `1/s` by `t` gives `t/s`.
* `TauCeti.Localization.algebraMap_mul_divBy` and
  `TauCeti.Localization.divBy_mul_algebraMap`: `s · (t/s) = t` in both orders.
* `TauCeti.Localization.divBy_zero`, `TauCeti.Localization.divBy_add` and
  `TauCeti.Localization.divBy_mul`: `t/s` is additive and `A`-linear in the
  numerator.
* `TauCeti.Localization.divBy_mul_cancel_left` and
  `TauCeti.Localization.divBy_mul_cancel_right`: `(s · t)/s = t` and `(t · s)/s = t`.
* `TauCeti.Localization.divBy_self`: `s/s = 1`.
* `TauCeti.Localization.divBy_one_right`: `t/1 = t`, the trivial denominator.
* `TauCeti.Localization.divBy_mul_divBy_of_eq_mul`: for `s = u * r`, the fraction `(a · b)/s`
  splits as `(a · r)/s · (b · u)/s`, each half carrying one factor of the denominator.
* `TauCeti.Localization.awayLift_divBy`: the comparison map to a localisation at a multiple
  `w = u * r` rescales fractions by the cofactor, sending `a/u` to `(a · r)/w`.

## Provenance

`divBy` and its identities are ported from AINTLIB's
`projects/AdicSpaces/Adic spaces/LocalizationTopology.lean`, branch `dev/adic-spaces`, commit
`d9f2fbbb`, where they are stated for the concrete `Localization.Away s` over a commutative ring
inside the Huber development. They are generalised here to an arbitrary `IsLocalization.Away`
over a commutative semiring, linked to Mathlib's `IsLocalization.Away.invSelf`, and moved out of
the Huber namespace because nothing about them is topological. The topological part of that port
is `TauCeti/RingTheory/Huber/LocalizationTopology/Basic.lean`, which records the same provenance.

`divBy_mul_divBy_of_eq_mul` and `awayLift_divBy` are **later additions with no AINTLIB analogue** —
checked against `dev/adic-spaces` at commit `37bbdaeb9`, which has neither the splitting identity
for a factored denominator nor any statement about `IsLocalization.Away.lift` on distinguished
fractions. Both are proved here directly from Mathlib's `mk'` API.

## References

* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `d9f2fbbb`, `projects/AdicSpaces/Adic spaces/LocalizationTopology.lean`
-/

public section

namespace TauCeti.Localization

variable {A : Type*} [CommSemiring A] {S : Type*} [CommSemiring S] [Algebra A S]
  (t s : A) [IsLocalization.Away s S]

/-- The element `t/s` in a localisation `S` of `A` away from `s` — numerator first, the element
being inverted second. The name follows Mathlib's `LocalizedModule.divBy`, division by the
distinguished element. -/
noncomputable def divBy : S :=
  IsLocalization.mk' S t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)

/-- `t/s` is the fraction `mk' t s`. The body of `divBy` is not exported, so this is how a
consumer reaches Mathlib's `IsLocalization` API for it. -/
theorem divBy_def :
    divBy t s = IsLocalization.mk' S t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s) :=
  (rfl)

/-- `1/s` is Mathlib's `IsLocalization.Away.invSelf`, so its simp set applies to `divBy 1 s`. -/
@[simp]
theorem divBy_one : divBy 1 s = (IsLocalization.Away.invSelf s : S) := (rfl)

/-- **Scaling `1/s` by `t` gives `t/s`.** Stated with `IsLocalization.Away.invSelf` rather than
`divBy 1 s` on the left, because `divBy_one` makes `invSelf` the simp-normal form of `1/s`; the
two together normalise a product of a unit fraction and a scalar to a single `divBy`. -/
@[simp]
theorem invSelf_mul_algebraMap :
    (IsLocalization.Away.invSelf s : S) * algebraMap A S t = divBy t s := by
  rw [← divBy_one, divBy_def, divBy_def,
    IsLocalization.mk'_eq_mul_mk'_one t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)]
  exact mul_comm _ _

/-- **Clearing the denominator**: `s · (t/s) = t`. -/
@[simp]
theorem algebraMap_mul_divBy :
    algebraMap A S s * divBy t s = algebraMap A S t := by
  rw [divBy_def]
  exact IsLocalization.mk'_spec' S t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)

/-- **Clearing the denominator inside the numerator**: `(s · t)/s = t`. -/
@[simp]
theorem divBy_mul_cancel_left : divBy (s * t) s = algebraMap A S t := by
  rw [divBy_def]
  exact IsLocalization.mk'_mul_cancel_left t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)

/-- The same on the other side: `(t · s)/s = t`. -/
@[simp]
theorem divBy_mul_cancel_right : divBy (t * s) s = algebraMap A S t := by
  rw [divBy_def]
  exact IsLocalization.mk'_mul_cancel_right t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)

/-- **Clearing the denominator on the right**: `(t/s) · s = t`. The mirror of
`algebraMap_mul_divBy`; `S` is only a `CommSemiring`, `mul_comm` is not `simp`, and Mathlib's
`IsLocalization.Away.mul_invSelf` fixes the other order, so without this the reversed goal is
left open. -/
@[simp]
theorem divBy_mul_algebraMap :
    divBy t s * algebraMap A S s = algebraMap A S t := by
  rw [divBy_def]
  exact IsLocalization.mk'_spec S t (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s)

/-- The mirror of `invSelf_mul_algebraMap`, for the same reason. -/
@[simp]
theorem algebraMap_mul_invSelf :
    algebraMap A S t * (IsLocalization.Away.invSelf s : S) = divBy t s := by
  rw [mul_comm]; exact invSelf_mul_algebraMap t s

/-! ### The numerator

`divBy` is additive and `A`-linear in its numerator. The body is not exported, so without these
a consumer computing with `t/s` — products of the generators of a localisation subring are
exactly such fractions — has to `rw [divBy_def]` down to `IsLocalization.mk'`. Each is read off
`invSelf_mul_algebraMap`, which turns the fraction into a product with a fixed left factor. -/

/-- `0/s = 0`. -/
@[simp]
theorem divBy_zero : (divBy 0 s : S) = 0 := by
  simp only [← invSelf_mul_algebraMap, map_zero, mul_zero]

/-- `t/s` is additive in the numerator. -/
@[simp]
theorem divBy_add (u : A) : divBy (t + u) s = (divBy t s : S) + divBy u s := by
  simp only [← invSelf_mul_algebraMap, map_add, mul_add]

/-- `t/s` is `A`-linear in the numerator. -/
theorem divBy_mul (a : A) :
    divBy (a * t) s = algebraMap A S a * divBy t s := by
  simp only [← invSelf_mul_algebraMap, map_mul]
  ring

/-- `s/s = 1`. Without this the simp set turns `invSelf s * algebraMap A S s` into `divBy s s`
and stops, where before `invSelf_mul_algebraMap` it could reach `1` through Mathlib's
`IsLocalization.Away.mul_invSelf`. -/
@[simp]
theorem divBy_self : (divBy s s : S) = 1 := by
  rw [divBy_def]
  exact IsLocalization.mk'_self S (Submonoid.mem_powers s)

/-! ### A factored denominator

When `s` factors as `u * r`, a fraction over `s` can be split so that each half carries one factor,
and a fraction over `u` alone can be rewritten over `s`. These are the identities that let a
presentation be replaced by one with a larger denominator. -/

/-- **Splitting a fraction over a factored denominator.** If `s = u * r` then `(a · b)/s` factors as
`(a · r)/s · (b · u)/s`: each half keeps one factor of the denominator, so `a/u` and `b/r` are
recovered as fractions over `s` itself.

Both sides agree after multiplying by `s`, which is a unit. This is what turns a product of
denominators into a product of two fractions over the *common* denominator, so that each can be
recognised separately. -/
theorem divBy_mul_divBy_of_eq_mul {u r : A} (h : s = u * r) (a b : A) :
    divBy (a * b) s = (divBy (a * r) s : S) * divBy (b * u) s := by
  rw [divBy_def, divBy_def, divBy_def, ← IsLocalization.mk'_mul,
    show (a * r) * (b * u) = (a * b) * s by rw [h]; ring]
  exact (IsLocalization.mk'_cancel (S := S) (a * b)
    ⟨s, Submonoid.mem_powers s⟩ ⟨s, Submonoid.mem_powers s⟩).symm

/-! ### Passing to a localisation at a multiple

A localisation away from `u` maps to a localisation away from any multiple `w = u * r`, by
`IsLocalization.Away.lift` at the unit `IsLocalization.Away.isUnit_of_dvd` supplies. The one thing
a consumer needs to know about that map is what it does to fractions, and the answer is that it
rescales numerator and denominator by the cofactor. -/

/-- **The comparison map rescales fractions by the cofactor**: if `w = u * r` then the map
`Aᵤ → A_w` induced by `IsLocalization.Away.lift` sends `a/u` to `(a · r)/w`.

Both sides become `a` after multiplying by `u`, which is a unit in `A_w`, so they agree. This is
what lets a fraction over the coarser denominator be recognised as a *distinguished* fraction of
the finer presentation. -/
theorem awayLift_divBy {V W : Type*} [CommSemiring V] [CommSemiring W] [Algebra A V] [Algebra A W]
    (u r w : A) (hw : w = u * r) [IsLocalization.Away u V] [IsLocalization.Away w W]
    (hu : IsUnit (algebraMap A W u)) (a : A) :
    IsLocalization.Away.lift u hu (divBy a u : V) = (divBy (a * r) w : W) := by
  rw [divBy_def, IsLocalization.Away.lift, IsLocalization.lift_mk'_spec, ← divBy_mul,
    show u * (a * r) = a * w by rw [hw]; ring, divBy_mul_cancel_right]

/-! ### The trivial denominator

A ring is its own localisation away from `1`, and there the fraction `t/1` is `t`. This is the
degenerate presentation `(T, 1)`, which the adic structure presheaf uses to present the whole
adic spectrum. -/

/-- **A ring is its own localisation away from `1`**: `1` is already a unit and the identity is
bijective. -/
instance isLocalizationAwayOne (R : Type*) [CommSemiring R] : IsLocalization.Away (1 : R) R :=
  IsLocalization.away_of_isUnit_of_bijective _ isUnit_one (Equiv.refl _).bijective

/-- **Dividing by `1` is the structure map**: `t/1 = t`. The denominator-one companion of
`divBy_one`, which is about the numerator. -/
@[simp]
theorem divBy_one_right {V : Type*} [CommSemiring V] [Algebra A V] [IsLocalization.Away (1 : A) V]
    (a : A) : (divBy a 1 : V) = algebraMap A V a := by
  simpa using divBy_mul_cancel_left (S := V) a 1

end TauCeti.Localization
