/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Complements on the ideal class group

Four facts about Mathlib's `ClassGroup R` and its principal-ideal map that Mathlib's own file does
not carry: the kernel of `toPrincipalIdeal`, the generator form of triviality of a class, that a
principal fractional ideal has trivial class, and the class `[v]` of a height one prime.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.classGroupMk`: the class `[v]` of a height one prime of a
  Dedekind domain.

## Main results

* `FractionalIdeal.toPrincipalIdeal_eq_one_iff`: the kernel of the principal-ideal homomorphism is
  the image of `Rˣ`, that is, `(u)` is trivial exactly when `u` comes from a unit of `R`. This is
  the left end of the ideal class exact sequence. The underlying computation is Mathlib's
  `Submodule.span_singleton_eq_one_iff`, reached by coercing the fractional ideal to a submodule.
* `ClassGroup.mk_eq_one_iff_exists`: a class is trivial exactly when some `x : Kˣ` generates it.
  This is Mathlib's `ClassGroup.mk_eq_one_iff` with `Submodule.IsPrincipal` traded for the range
  of `toPrincipalIdeal`, which is the form a consumer that wants to *name* the generator can use.
* `ClassGroup.mk_toPrincipalIdeal`: a principal fractional ideal has trivial class. This is the
  `simp` form of `ClassGroup.mk_eq_one_iff` for the one witness that arises in practice, and it
  holds over any domain.
* `IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk0`: the defining formula for `[v]`, as
  `ClassGroup.mk0` of `v.asIdeal`. This needs no fraction field.
* `IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk`: `[v]` is the class of `v.asIdeal` seen
  as an invertible fractional ideal of any fraction field `K`.

All are stated at the weakest hypotheses their proofs need: the two class-triviality results over
`[IsDomain R]`, since nothing in either is Dedekind-specific, and `toPrincipalIdeal_eq_one_iff`
over a plain `[CommRing R]`, since routing it through Mathlib's submodule lemma needs no domain
hypothesis at all. None
of them needs the factorization of a fractional ideal into primes, so this file does not import
it; the results that do live in
`TauCeti.RingTheory.ClassGroup.HeightOneSpectrum`, which every consumer of *those* pays for and
consumers of these do not.

Split out of material adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/FractionalIdeal.lean`
at the roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll). Following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

/-- The kernel of the principal-ideal map is the image of `Rˣ`: `toPrincipalIdeal R K u` is trivial
exactly when `u` comes from a unit of `R`. This is the left end of the ideal class exact
sequence. -/
lemma FractionalIdeal.toPrincipalIdeal_eq_one_iff {R : Type*} [CommRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (u : Kˣ) :
    toPrincipalIdeal R K u = 1 ↔ ∃ a : Rˣ, Units.map (algebraMap R K : R →* K) a = u := by
  rw [← Units.val_inj, coe_toPrincipalIdeal, Units.val_one, ← coeToSubmodule_inj,
    coe_spanSingleton, coe_one, Submodule.span_singleton_eq_one_iff]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, Units.ext ha.symm⟩, fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha]; rfl⟩⟩

/-- A unit fractional ideal has trivial class exactly when it is principal, with the generator
delivered as a unit of `K`. This is Mathlib's `ClassGroup.mk_eq_one_iff` with
`Submodule.IsPrincipal` traded for the range of `toPrincipalIdeal`, which is the form a consumer
that wants to *name* the generator can use. -/
lemma ClassGroup.mk_eq_one_iff_exists {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] {I : (FractionalIdeal R⁰ K)ˣ} :
    ClassGroup.mk K I = 1 ↔ ∃ x : Kˣ, toPrincipalIdeal R K x = I := by
  rw [ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff, ← MonoidHom.mem_range,
    mem_principal_ideals_iff]
  exact exists_congr fun _ ↦ eq_comm

/-- A principal fractional ideal has trivial ideal class. -/
@[simp]
lemma ClassGroup.mk_toPrincipalIdeal {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (x : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K x) = 1 :=
  ClassGroup.mk_eq_one_iff_exists.mpr ⟨x, rfl⟩

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The class of a height one prime `v` in the ideal class group of `R`. -/
noncomputable def IsDedekindDomain.HeightOneSpectrum.classGroupMk (v : HeightOneSpectrum R) :
    ClassGroup R :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

-- Deliberately not `@[simp]`: the statements that matter here are phrased in the folded form,
-- and in `HeightOneSpectrum.classGroupMk '' T` the occurrence is unapplied, so `simp` could not
-- unfold it there anyway — tagging this would only leave goals in mixed normal forms.
/-- The class of `v` is the class of the nonzero ideal `v.asIdeal`. -/
lemma IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk0 (v : HeightOneSpectrum R) :
    v.classGroupMk = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  -- Not `rfl`: a `public section` leaves the body of `classGroupMk` unexposed, so the equation
  -- has to come from the definition's own equation lemma.
  simp only [IsDedekindDomain.HeightOneSpectrum.classGroupMk]

/-- The class of `v` is the class of `v.asIdeal` viewed as an invertible fractional ideal of a
fraction field `K`. -/
lemma IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) :
    v.classGroupMk = ClassGroup.mk K (Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K)
      (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)) := by
  rw [classGroupMk_eq_mk0, ← ClassGroup.mk_mk0 K]
  exact congrArg _ (Units.ext (FractionalIdeal.coe_mk0 K _))

end
