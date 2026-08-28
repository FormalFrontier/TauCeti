/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Complements on ideals of a Dedekind domain

This file collects general facts about ideals and height-one primes of a Dedekind domain,
complementing `Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean`. In particular, it develops
the predicate `Ideal.IsPrimeTo I S`, saying that `I` is nonzero and divisible by no prime in `S`,
together with its induction principle `Ideal.IsPrimeTo.induction_on` and its transport
`Ideal.isPrimeTo_comap_iff` along a ring isomorphism.

It also collects how an isomorphism `e : R ≃+* R'` moves ideals: `Ideal.map e` preserves
divisibility (`Ideal.map_dvd_map_iff_of_ringEquiv`, `Ideal.map_pow_dvd_map_iff_of_ringEquiv`,
stated over commutative *semirings*, since the proofs use only that `Ideal.map e` and
`Ideal.map e.symm` are mutually inverse) and factorisation multiplicities
(`Ideal.count_factors_map_of_ringEquiv`), and Mathlib's transport `equivOfRingEquiv e` of height
one primes is `Ideal.map e` on underlying ideals
(`IsDedekindDomain.HeightOneSpectrum.asIdeal_equivOfRingEquiv`). Those four are the ideal-level
input to the adic-valuation transport in
`TauCeti/RingTheory/DedekindDomain/AdicValuation/Transport.lean`; they are adapted from
[AINTLIB](https://github.com/CBirkbeck/AINTLIB) (Apache-2.0), commit `513e83879e2f`,
`projects/HasseWeil/HasseWeil/WeilPairing/DivisorGalois.lean`.

`Ideal.IsPrimeTo` generalizes the `IsGood` predicate of
`TauCetiRoadmap/ArithmeticDirichletSeries/Suggested.lean`, where it is stated for the bad primes
of an ideal weight on a number field; the design of the predicate — nonzeroness included, so that
`⊥` is prime to no set at all — is taken from there, while nothing in it is specific to a number
field.

The file also identifies any height-one prime of a discrete valuation ring with its maximal ideal
(`IsDedekindDomain.HeightOneSpectrum.eq_maximalIdeal`), which is what lets a condition stated at
the height-one primes of such a ring be read as a condition on its valuation. It was split out of
material adapted from Michael Stoll's elliptic-curves formalisation
(`EllipticCurves/Mathlib/AdicCompletionExtension.lean` at the roadmap's pin `66889eada51a`,
Apache 2.0, by Michael Stoll), where it is the step behind `valuation_adicCompletion_algebraMap`.

The theorem `IsDedekindDomain.HeightOneSpectrum.exists_mem_notMem` was split out of material
adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SIntegers.lean` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll); following this repository's
convention for adapted material, the upstream authorship is credited here rather than in the
copyright header.

`IsDedekindDomain.HeightOneSpectrum.comapOfNeBot` and its projection are likewise adapted from that
formalisation (`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/Basic.lean`
line 539, at the roadmap's pin `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, Apache 2.0, by Michael
Stoll). The construction is the source's; what changed is the hypothesis — the source and this
version take the nonvanishing of the contraction as a hypothesis, where Mathlib's
`HeightOneSpectrum.comap` instead derives it from surjectivity of the map.

`Ideal.ne_bot_of_comap_ne_bot` plays the role of the source's
`comap_ne_bot_of_comap_comap_ne_bot` (`EllipticCurves/Mathlib/Basic.lean` line 270): it is what
discharges that nonvanishing hypothesis when a prime is contracted through an intermediate ring.
It is stated here in the general form — an arbitrary ideal and an injective ring homomorphism,
with the map producing the ideal dropped, since it plays no role — and proved from Mathlib's
`Ideal.comap_bot_of_injective`.
-/

public section

namespace Ideal

section CommSemiring

variable {R R' : Type*} [CommSemiring R] [CommSemiring R']

/-- Divisibility of ideals is unchanged by pushing forward along a ring isomorphism: `Ideal.map e`
and `Ideal.map e.symm` are mutually inverse homomorphisms of the semirings of ideals. -/
theorem map_dvd_map_iff_of_ringEquiv (e : R ≃+* R') (I J : Ideal R) :
    Ideal.map e I ∣ Ideal.map e J ↔ I ∣ J := by
  -- `Ideal.map` sees `e` through `FunLike`, so `e` and its `RingHom` coercion give the same ideal;
  -- passing to the coercion is what lets `Ideal.mapHom` carry the divisibility.
  change Ideal.map (e : R →+* R') I ∣ Ideal.map (e : R →+* R') J ↔ I ∣ J
  refine ⟨fun h ↦ ?_, fun h ↦ by
    simpa only [mapHom_apply] using map_dvd (mapHom (e : R →+* R')) h⟩
  have hcomp : (e.symm : R' →+* R).comp (e : R →+* R') = RingHom.id R := by ext x; simp
  simpa only [mapHom_apply, Ideal.map_map, hcomp, Ideal.map_id] using
    map_dvd (mapHom (e.symm : R' →+* R)) h

/-- The prime-power divisibility `p ^ n ∣ I` is unchanged by pushing forward along a ring
isomorphism. -/
theorem map_pow_dvd_map_iff_of_ringEquiv (e : R ≃+* R') (p I : Ideal R) (n : ℕ) :
    (Ideal.map e p) ^ n ∣ Ideal.map e I ↔ p ^ n ∣ I := by
  rw [← Ideal.map_pow]
  exact map_dvd_map_iff_of_ringEquiv e (p ^ n) I

end CommSemiring

section RingEquivDedekind

variable {R R' : Type*} [CommRing R] [IsDedekindDomain R] [CommRing R'] [IsDedekindDomain R']

/-- Multiplicities in the factorisation of an ideal are unchanged by pushing forward along a ring
isomorphism: the number of times `Ideal.map e p` divides `Ideal.map e I` is the number of times
`p` divides `I`. -/
theorem count_factors_map_of_ringEquiv (e : R ≃+* R') {p I : Ideal R} (hp : Prime p) (hI : I ≠ ⊥) :
    (Associates.mk (Ideal.map e p)).count (Associates.mk (Ideal.map e I)).factors =
      (Associates.mk p).count (Associates.mk I).factors := by
  classical
  have hpb : p ≠ ⊥ := by simpa only [zero_eq_bot] using hp.ne_zero
  have hpmapb : Ideal.map e p ≠ ⊥ := by
    simpa only [ne_eq, map_eq_bot_iff_of_injective e.injective] using hpb
  have hI0 : I ≠ 0 := by simpa only [zero_eq_bot] using hI
  -- `map_isPrime_of_equiv` is an instance, so it fires once `p.IsPrime` is in the context.
  have : p.IsPrime := (prime_iff_isPrime hpb).mp hp
  have hpmap : Prime (Ideal.map e p) := (prime_iff_isPrime hpmapb).mpr (map_isPrime_of_equiv e)
  have hmkImap : Associates.mk (Ideal.map e I) ≠ 0 := Associates.mk_ne_zero.mpr
    (by simpa only [ne_eq, zero_eq_bot, map_eq_bot_iff_of_injective e.injective] using hI)
  have hmkI : Associates.mk I ≠ 0 := Associates.mk_ne_zero.mpr hI0
  -- Both counts are pinned by the same `n ≤ ·` characterisation, through `prime_pow_dvd_iff_le`.
  have key : ∀ n : ℕ, n ≤ (Associates.mk (Ideal.map e p)).count
        (Associates.mk (Ideal.map e I)).factors ↔
      n ≤ (Associates.mk p).count (Associates.mk I).factors := fun n ↦ by
    rw [← Associates.prime_pow_dvd_iff_le hmkImap (Associates.irreducible_mk.mpr hpmap.irreducible),
      ← Associates.prime_pow_dvd_iff_le hmkI (Associates.irreducible_mk.mpr hp.irreducible),
      ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
      Associates.mk_le_mk_iff_dvd]
    exact map_pow_dvd_map_iff_of_ringEquiv e p I n
  exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)

end RingEquivDedekind

section Injective

/-- If the contraction of `J` along an injective ring homomorphism is nonzero, so is `J` itself.

This is the eliminator that discharges the nonvanishing hypothesis of
`IsDedekindDomain.HeightOneSpectrum.comapOfNeBot` when a prime is contracted through an
intermediate ring: contract all the way down to a base where nonvanishing is already known, and
read the intermediate step off from that. Only injectivity of the *lower* map is needed; the map
producing `J` plays no role, so it does not appear. -/
theorem ne_bot_of_comap_ne_bot {R S F : Type*} [Semiring R] [Semiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) (hf : Function.Injective f) {J : Ideal S}
    (h : J.comap f ≠ ⊥) : J ≠ ⊥ :=
  fun h0 ↦ h (h0 ▸ comap_bot_of_injective f hf)

end Injective

end Ideal

namespace IsDedekindDomain.HeightOneSpectrum

section Comap

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]

/-- The height-one prime of `B` obtained by contracting a height-one prime of `C` along a ring
homomorphism `ψ : B →+* C`, given that the contraction is nonzero.

Mathlib's `IsDedekindDomain.HeightOneSpectrum.comap` is the same construction, but it asks for `ψ`
to be **surjective** and derives the `ne_bot` field from that. `comapOfNeBot` **generalises** it:
the surjective case is recovered by supplying `(Ideal.eq_bot_of_comap_eq_bot' hf).mt w.ne_bot`, and
only the converse fails.

The generality is needed because the maps contracted along here are embeddings into completions —
`R → v.adicCompletionIntegers K` — which are neither surjective, so Mathlib's `comap` does not
apply, nor integral `Algebra` maps, so `HeightOneSpectrum.under` does not either. (`ℤ → ℤ_p` is
flat, not integral.) The `ne_bot` hypothesis has to be supplied by hand.

Adapted from Michael Stoll's `EllipticCurves` (`EllipticCurves/Mathlib/Basic.lean` line 539, Apache
2.0, at the roadmap's pin `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`); the `ne_bot`-as-hypothesis
formulation is the source's. -/
def comapOfNeBot (ψ : B →+* C) (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) :
    HeightOneSpectrum B where
  asIdeal := w.asIdeal.comap ψ
  isPrime := w.isPrime.comap ψ
  ne_bot := hne

omit [IsDedekindDomain B] [IsDedekindDomain C] in
-- `(rfl)` elaborates here, where the definition is visible.
/-- The underlying ideal of `comapOfNeBot` is the contracted ideal. -/
@[simp]
lemma comapOfNeBot_asIdeal (ψ : B →+* C) (w : HeightOneSpectrum C)
    (hne : w.asIdeal.comap ψ ≠ ⊥) :
    (comapOfNeBot ψ w hne).asIdeal = w.asIdeal.comap ψ :=
  (rfl)

end Comap

section RingEquivTransport

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- Mathlib's transport `equivOfRingEquiv e` of height one primes along a ring isomorphism `e`
pushes the underlying ideal forward: `(equivOfRingEquiv e v).asIdeal = Ideal.map e v.asIdeal`. -/
theorem asIdeal_equivOfRingEquiv (e : R ≃+* R') (v : HeightOneSpectrum R) :
    (equivOfRingEquiv e v).asIdeal = Ideal.map e v.asIdeal := by
  ext x
  -- `equivOfRingEquiv` transports a prime by comapping along `e.symm`, so membership in its ideal
  -- is by definition membership of `e.symm x`, and the two descriptions agree by
  -- `Ideal.symm_apply_mem_of_equiv_iff`.
  change e.symm x ∈ v.asIdeal ↔ x ∈ Ideal.map e v.asIdeal
  exact Ideal.symm_apply_mem_of_equiv_iff

end RingEquivTransport

end IsDedekindDomain.HeightOneSpectrum

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

/-- A height-one prime ideal is prime to `S` exactly when its spectrum point is not in `S`. -/
@[simp]
theorem isPrimeTo_asIdeal_iff {𝔭 : HeightOneSpectrum R} :
    IsPrimeTo 𝔭.asIdeal S ↔ 𝔭 ∉ S := by
  refine ⟨fun h h𝔭 ↦ h.not_dvd h𝔭 dvd_rfl, fun h𝔭 ↦ ⟨𝔭.ne_bot, fun 𝔮 h𝔮 hdvd ↦ h𝔭 ?_⟩⟩
  exact HeightOneSpectrum.asIdeal_injective
    ((prime_dvd_prime_iff_eq 𝔮.prime 𝔭.prime).mp hdvd) ▸ h𝔮

/-- **Being prime to a set of primes transports along a ring isomorphism.** An ideal pulled back
along `e : R ≃+* A` is prime to `T` exactly when the ideal itself is prime to the image of `T`
under the induced bijection of height-one spectra. -/
theorem isPrimeTo_comap_iff {A : Type*} [CommRing A] [IsDedekindDomain A] (e : R ≃+* A)
    {I : Ideal A} {T : Set (HeightOneSpectrum R)} :
    IsPrimeTo (I.comap e) T ↔ IsPrimeTo I (HeightOneSpectrum.equivOfRingEquiv e '' T) := by
  have hmem (𝔭 : HeightOneSpectrum R) (x : A) :
      x ∈ (HeightOneSpectrum.equivOfRingEquiv e 𝔭).asIdeal ↔ e.symm x ∈ 𝔭.asIdeal := Iff.rfl
  have hbot : I.comap e = ⊥ ↔ I = ⊥ := by
    rw [← Ideal.map_symm]
    exact Ideal.map_eq_bot_iff_of_injective e.symm.injective
  have hdvd (𝔭 : HeightOneSpectrum R) :
      𝔭.asIdeal ∣ I.comap e ↔ (HeightOneSpectrum.equivOfRingEquiv e 𝔭).asIdeal ∣ I := by
    rw [dvd_iff_le, dvd_iff_le]
    constructor
    · intro h y hy
      exact (hmem 𝔭 y).mpr (h (Ideal.mem_comap.mpr (by rwa [e.apply_symm_apply])))
    · intro h x hx
      have hx' := (hmem 𝔭 (e x)).mp (h (Ideal.mem_comap.mp hx))
      rwa [e.symm_apply_apply] at hx'
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨fun hI ↦ h0 (hbot.mpr hI), ?_⟩
    rintro _ ⟨𝔭, h𝔭, rfl⟩
    exact fun hd ↦ h 𝔭 h𝔭 ((hdvd 𝔭).mpr hd)
  · rintro ⟨h0, h⟩
    exact ⟨fun hI ↦ h0 (hbot.mp hI), fun 𝔭 h𝔭 hd ↦ h _ ⟨𝔭, h𝔭, rfl⟩ ((hdvd 𝔭).mp hd)⟩

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

section DiscreteValuationRing

namespace IsDedekindDomain.HeightOneSpectrum

/-- The maximal ideal is the only height-one prime of a discrete valuation ring.

Mathlib has `IsDiscreteValuationRing.maximalIdeal` as a `HeightOneSpectrum` and
`IsLocalRing.eq_maximalIdeal` for ideals, but not that the two agree at the level of
`HeightOneSpectrum`. That identification is what lets a statement about the height-one primes of a
discrete valuation ring be read as a statement about its valuation. -/
-- Not `@[simp]`: the left-hand side is the bare variable `P`, so its head symbol is a variable and
-- the compiler rejects the annotation outright ("the theorem will be tried on every simp step").
lemma eq_maximalIdeal {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (P : HeightOneSpectrum A) : P = IsDiscreteValuationRing.maximalIdeal A :=
  HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal P.isMaximal)

end IsDedekindDomain.HeightOneSpectrum

end DiscreteValuationRing

end
