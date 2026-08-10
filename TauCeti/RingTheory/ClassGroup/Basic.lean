/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Complements on the ideal class group

Two facts about Mathlib's `ClassGroup R` that its own file does not carry: that a principal
fractional ideal has trivial class, and the class `[v]` of a height one prime.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.classGroupMk`: the class `[v]` of a height one prime of a
  Dedekind domain.

## Main results

* `ClassGroup.mk_toPrincipalIdeal`: a principal fractional ideal has trivial class. This is the
  `simp` form of `ClassGroup.mk_eq_one_iff` for the one witness that arises in practice, and it
  holds over any domain.
* `IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk0`: the defining formula for `[v]`, as
  `ClassGroup.mk0` of `v.asIdeal`. This needs no fraction field.
* `IsDedekindDomain.HeightOneSpectrum.classGroupMk_eq_mk`: `[v]` is the class of `v.asIdeal` seen
  as an invertible fractional ideal of any fraction field `K`.

Both are stated at the weakest hypotheses their proofs need — `ClassGroup.mk_toPrincipalIdeal`
over `[IsDomain R]`, since nothing in it is Dedekind-specific. Neither needs the factorization
of a fractional ideal into primes, so this file does not import it; the results that do live in
`TauCeti.RingTheory.ClassGroup.HeightOneSpectrum`, which every consumer of *those* pays for and
consumers of these two do not.

Split out of material adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/FractionalIdeal.lean`
at the roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll). Following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

/-- A principal fractional ideal has trivial ideal class. -/
@[simp]
lemma ClassGroup.mk_toPrincipalIdeal {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (x : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K x) = 1 :=
  ClassGroup.mk_eq_one_iff.mpr
    ⟨⟨(x : K), by rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]⟩⟩

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
