/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Complements on ideals of a Dedekind domain

This file collects general facts about ideals and height-one primes of a Dedekind domain,
complementing `Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`. In particular, it develops
the predicate `Ideal.IsPrimeTo I S`, saying that `I` is nonzero and divisible by no prime in `S`,
and its induction principle.

The theorem `IsDedekindDomain.HeightOneSpectrum.exists_mem_notMem` was split out of material
adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SIntegers.lean` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll); following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- Distinct height one primes are incomparable: a height one prime is not contained in any
other one, since both are maximal. -/
lemma exists_mem_notMem {v w : HeightOneSpectrum R} (h : w ≠ v) :
    ∃ a ∈ v.asIdeal, a ∉ w.asIdeal := by
  by_contra! hc
  exact h (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)

end IsDedekindDomain.HeightOneSpectrum

namespace Ideal

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- An ideal of a Dedekind domain is **prime to** a set `S` of height-one primes when it is
nonzero and no prime of `S` divides it. Nonzeroness is part of the definition, so `⊥` is prime
to no set at all — not even to `∅`. -/
def IsPrimeTo (I : Ideal R) (S : Set (HeightOneSpectrum R)) : Prop :=
  I ≠ ⊥ ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I

variable {I J : Ideal R} {S T : Set (HeightOneSpectrum R)}

omit [IsDedekindDomain R] in
theorem isPrimeTo_iff : IsPrimeTo I S ↔ I ≠ ⊥ ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ I := Iff.rfl

omit [IsDedekindDomain R] in
theorem IsPrimeTo.ne_bot (h : IsPrimeTo I S) : I ≠ ⊥ := h.1

omit [IsDedekindDomain R] in
theorem IsPrimeTo.not_dvd (h : IsPrimeTo I S) {𝔭 : HeightOneSpectrum R} (h𝔭 : 𝔭 ∈ S) :
    ¬ 𝔭.asIdeal ∣ I := h.2 𝔭 h𝔭

omit [IsDedekindDomain R] in
/-- The zero ideal is prime to no set of primes, not even to the empty set. -/
@[simp]
theorem not_isPrimeTo_bot : ¬ IsPrimeTo (⊥ : Ideal R) S := fun h ↦ h.ne_bot rfl

omit [IsDedekindDomain R] in
@[simp]
theorem isPrimeTo_empty : IsPrimeTo I ∅ ↔ I ≠ ⊥ := by
  rw [isPrimeTo_iff]
  simp

@[simp]
theorem isPrimeTo_top : IsPrimeTo (⊤ : Ideal R) S := by
  refine ⟨top_ne_bot, fun 𝔭 _ hdvd ↦ 𝔭.prime.not_isUnit ?_⟩
  exact isUnit_of_dvd_one (by simpa [Ideal.one_eq_top] using hdvd)

omit [IsDedekindDomain R] in
theorem IsPrimeTo.mono (hST : S ⊆ T) (h : IsPrimeTo I T) : IsPrimeTo I S :=
  ⟨h.ne_bot, fun _𝔭 h𝔭 ↦ h.not_dvd (hST h𝔭)⟩

/-- **Being prime to `S` is multiplicative.** A product of ideals is prime to `S` exactly when
both factors are: neither factor may vanish, and a prime of `S` divides the product exactly when
it divides one of the factors. -/
@[simp]
theorem isPrimeTo_mul_iff : IsPrimeTo (I * J) S ↔ IsPrimeTo I S ∧ IsPrimeTo J S := by
  simp only [IsPrimeTo, ne_eq, Ideal.mul_eq_bot, not_or]
  refine ⟨fun ⟨h0, h⟩ ↦ ⟨⟨h0.1, fun 𝔭 h𝔭 hdvd ↦ h 𝔭 h𝔭 (hdvd.mul_right _)⟩,
    ⟨h0.2, fun 𝔭 h𝔭 hdvd ↦ h 𝔭 h𝔭 (hdvd.mul_left _)⟩⟩, fun ⟨hI, hJ⟩ ↦ ⟨⟨hI.1, hJ.1⟩, ?_⟩⟩
  intro 𝔭 h𝔭 hdvd
  rcases 𝔭.prime.dvd_mul.mp hdvd with h | h
  · exact hI.2 𝔭 h𝔭 h
  · exact hJ.2 𝔭 h𝔭 h

@[simp]
theorem isPrimeTo_asIdeal_iff {𝔭 : HeightOneSpectrum R} :
    IsPrimeTo 𝔭.asIdeal S ↔ 𝔭 ∉ S := by
  refine ⟨fun h h𝔭 ↦ h.not_dvd h𝔭 dvd_rfl, fun h𝔭 ↦ ⟨𝔭.ne_bot, fun 𝔮 h𝔮 hdvd ↦ h𝔭 ?_⟩⟩
  exact HeightOneSpectrum.asIdeal_injective
    ((prime_dvd_prime_iff_eq 𝔮.prime 𝔭.prime).mp hdvd) ▸ h𝔮

/-- **Induction on ideals prime to `S`.** Such an ideal is a finite product of height-one
primes outside `S`, so a property holding at `⊤` and stable under multiplication by a
height-one prime outside `S` holds for all of them. -/
@[elab_as_elim]
theorem IsPrimeTo.induction_on {motive : Ideal R → Prop} (h : IsPrimeTo I S)
    (top : motive ⊤)
    (mul_prime : ∀ (𝔭 : HeightOneSpectrum R) (J : Ideal R), 𝔭 ∉ S →
      IsPrimeTo J S → motive J → motive (𝔭.asIdeal * J)) :
    motive I := by
  revert h
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact fun h ↦ absurd rfl h.ne_bot
  | h₂ x hx => exact fun _ ↦ (Ideal.isUnit_iff.mp hx) ▸ top
  | h₃ J p _ hp ih =>
      intro hprime
      have hJ : IsPrimeTo J S := (isPrimeTo_mul_iff.mp hprime).2
      have hbad : HeightOneSpectrum.ofPrime hp ∉ S :=
        fun h ↦ hprime.2 _ h (dvd_mul_right p J)
      exact mul_prime (HeightOneSpectrum.ofPrime hp) J hbad hJ (ih hJ)

end Ideal

end
