/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Finiteness of the ramification locus of an extension of Dedekind domains

Let `B` be a Dedekind domain, module-finite and torsion-free over a Dedekind domain `A`, with the
extension of fraction fields separable. Mathlib's `Algebra.unramifiedLocus A B` is the set of
primes of `B` at which `B` is unramified over `A`, and Mathlib knows it is open. Here it is shown
that its complement — the ramification locus — is *finite*.

The tool is the different ideal. Mathlib's `not_dvd_differentIdeal_iff` says a prime is unramified
exactly when it does not divide `differentIdeal A B`, and `differentIdeal_ne_bot` says that ideal
is nonzero; a nonzero ideal of a Dedekind domain has only finitely many divisors.

## Main results

* `Algebra.finite_compl_unramifiedLocus`: the ramification locus is finite.

Stated over Dedekind domains directly rather than in an AKLB tower: no ambient fraction fields
`K` and `L` and no `IsIntegralClosure B A L` are needed, since the separability hypothesis can be
carried by `FractionRing A` and `FractionRing B` themselves, which is the form
`not_dvd_differentIdeal_iff` already takes.

This supports Layer 1 of `TauCetiRoadmap/EllipticCurves/README.md`, whose
**separable-implies-unramified** milestone asks that a separable isogeny have `e_w = 1` at *every*
place, "by translation-invariance of the ramification locus". That argument needs the ramification
locus to be finite before translation-invariance can force it to be empty; the finiteness is what
this file supplies. Layer 2's `E[N]` and Layer 3's Hasse kernel count consume that milestone.

## Provenance

Ported from the AINTLIB `HasseWeil` project (`github.com/CBirkbeck/AINTLIB`, Apache-2.0, pinned by
that roadmap at `dev/hasse-weil @ 513e83879e2f`), `HasseWeil/Curves/RamificationFinite.lean`,
declarations `finite_setOf_dvd_differentIdeal`, `finite_setOf_ramificationIdx_ne_one` and
`finite_setOf_under_ramified`.

Changes from the source. The source works in an AKLB tower and rebuilds the standard instances
along the way, including `differentIdeal_ne_bot`, which Mathlib now proves; those are dropped, and
with them the tower. The ramification locus is named by Mathlib's `Algebra.unramifiedLocus` and
the criterion by Mathlib's `Algebra.IsUnramifiedAt`, in place of the source's hand-rolled
`ramifiedUnderLocus` and its `Ideal.ramificationIdx _ _ ≠ 1` spelling. The source's
divisor-finiteness step is Mathlib's `Ideal.finite_factors`, so it neither is rebuilt from the
`UniqueFactorizationMonoid` plumbing nor becomes public API here. Sixteen declarations become one.
-/

public section

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace Algebra

variable (A B : Type*) [CommRing A] [IsDedekindDomain A] [CommRing B] [Algebra A B]
  [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- **A module-finite, torsion-free extension of Dedekind domains whose fraction-field extension
is separable ramifies at only finitely many primes**: the complement of
`Algebra.unramifiedLocus` is finite. A ramified prime divides the different ideal, which is
nonzero and so, being an ideal of a Dedekind domain, has finitely many divisors. -/
theorem finite_compl_unramifiedLocus : (unramifiedLocus A B)ᶜ.Finite := by
  refine Set.Finite.of_finite_image (f := PrimeSpectrum.asIdeal) ?_
    fun _ _ _ _ h => PrimeSpectrum.ext h
  refine ((Ideal.finite_factors (differentIdeal_ne_bot (A := A) (B := B))).image
    _root_.IsDedekindDomain.HeightOneSpectrum.asIdeal).subset ?_
  rintro _ ⟨p, hp, rfl⟩
  have : p.asIdeal.IsPrime := p.isPrime
  have hdvd : p.asIdeal ∣ differentIdeal A B := dvd_differentIdeal_iff.mpr hp
  -- a ramified prime is nonzero: `⊥` divides only `⊥`, and the different ideal is not `⊥`
  have hbot : p.asIdeal ≠ ⊥ := fun h =>
    differentIdeal_ne_bot (A := A) (B := B) (eq_bot_iff.mpr (h ▸ Ideal.le_of_dvd hdvd))
  exact ⟨_root_.IsDedekindDomain.HeightOneSpectrum.ofPrime
    (Ideal.prime_of_isPrime hbot p.isPrime), hdvd, rfl⟩

end Algebra

end
