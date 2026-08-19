/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import TauCeti.RingTheory.DedekindDomain.SInteger.Basic

/-!
# The height one spectrum of a ring of `S`-integers

Let `R` be a Dedekind domain with fraction field `K` and `S` a set of height-one primes of `R`.
`TauCeti/RingTheory/DedekindDomain/SInteger/Basic.lean` shows that the ring of `S`-integers is
again a Dedekind domain, so it has a height one spectrum of its own. This file identifies that
spectrum:
the height-one primes of `𝒪_S` are exactly the height-one primes of `R` **not** in `S`, via
`v ↦ v · 𝒪_S`
(`integerHeightOneSpectrumEquiv`), and the correspondence carries the valuations across unchanged
(`valuation_integerHeightOneSpectrumEquiv`).

Two companion facts record what extension does to prime *powers* for `v ∉ S`:
`integer_comap_map_pow`, that contracting the extension of `v ^ n` returns `v ^ n`, and
`integer_map_le_map_pow_iff`, that containment in a prime power transfers along the extension in
both directions. Multiplicities are turned into such containments by
`le_count_associates_iff_le_pow` in
`TauCeti/RingTheory/DedekindDomain/Factorization.lean`; `integer_map_le_map_pow_iff` is what then
carries them across the extension.

The two directions are `integerPrimeOverOfNotMem`, extending `v ∉ S` to `𝒪_S`, and
`integerPrimeUnder`, contracting a prime of `𝒪_S` back to `R`. That they are mutually inverse is
Mathlib's `Ideal.comap_map_eq_self_of_isMaximal` in one direction — the extension of a maximal
`v ∉ S` stays proper, so contracting it returns `v` — and `integer_map_comap_eq` — every ideal of
`𝒪_S` is extended — in the other.

The valuations transfer through Mathlib's `HeightOneSpectrum.valuation_liesOver`, which relates the
valuation at a prime to the valuation at the prime below it by the ramification index. Here that
index is `1` by Mathlib's `Ideal.ramificationIdx'_map_self_eq_one`, the extended ideal *being* the
prime above. Both readings of
the transfer are supplied — `valuation_integerPrimeOverOfNotMem` for a prime of `R` avoiding `S`,
and `valuation_integerPrimeUnder` for an arbitrary prime of `𝒪_S`.

Inverting `S` therefore removes exactly the primes of `S` from the spectrum and changes nothing
else, which is why the Selmer group of `𝒪_S` relative to `∅` is the Selmer group of `R` relative
to `S`. That identification is what
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 6 needs for weak Mordell–Weil: the finiteness of
`A(S, 2)` is the finiteness of a Selmer group over `𝒪_S`.

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/SIntegers.lean` at the
roadmap's pin `66889eada51a`, Apache 2.0, by Michael Stoll), the source the roadmap's §Provenance
names for the Layer 6 Mordell–Weil lane. Following this repository's convention for adapted
material, the upstream authorship is credited here rather than in the copyright header. This is
the height-one-spectrum half of that file; the Dedekind property came first, and the class-group
computation `Cl(𝒪_S) ≃* Cl(R) ⧸ ⟨[v] : v ∈ S⟩` is
`IsDedekindDomain.integerClassGroupEquiv` in
`TauCeti/RingTheory/DedekindDomain/SInteger/ClassGroup.lean`, which consumes this file.
-/

public section

open IsDedekindDomain

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (S : Set (HeightOneSpectrum R))

/-- For `v ∉ S`, the extension of `v` to `𝒪_S` is a proper ideal. -/
lemma integer_map_asIdeal_ne_top {v : HeightOneSpectrum R} (hv : v ∉ S) :
    Ideal.map (algebraMap R (S.integer K)) v.asIdeal ≠ ⊤ := by
  -- Since `v ∉ S`, the `S`-integers lie in the valuation ring of `v`; the extension of `v` lands
  -- in the pullback of that local ring's maximal ideal, which is proper because `1` does not.
  set f := algebraMap R (S.integer K)
  have hsub : (S.integer K).toSubring ≤ (v.valuation K).valuationSubring.toSubring :=
    fun x hx ↦ (Set.mem_integer_iff K S).mp hx v hv
  let 𝔪 : Ideal (S.integer K) :=
    (IsLocalRing.maximalIdeal (v.valuation K).valuationSubring).comap (Subring.inclusion hsub)
  have hle : Ideal.map f v.asIdeal ≤ 𝔪 :=
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦
      (_root_.Valuation.mem_maximalIdeal_iff K (v.valuation K)).mpr <| by
        rw [Subring.coe_inclusion, Subalgebra.coe_algebraMap]
        exact (v.valuation_lt_one_iff_mem a).mpr ha
  intro htop
  -- if the extension were `⊤` then `1` would lie in `𝔪`, i.e. would have `v`-valuation `< 1`
  have hmem : (1 : S.integer K) ∈ 𝔪 := le_trans htop.ge hle Submodule.mem_top
  have h1 := (_root_.Valuation.mem_maximalIdeal_iff K (v.valuation K)).mp hmem
  simp at h1

/-- For `v ∉ S`, the extension of `v` to `𝒪_S` is maximal. -/
lemma isMaximal_integer_map_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (Ideal.map (algebraMap R (S.integer K)) v.asIdeal).IsMaximal := by
  set f := algebraMap R (S.integer K)
  have := v.isMaximal
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (integer_map_asIdeal_ne_top K S hv)
  have hcle : v.asIdeal ≤ M.comap f :=
    (Ideal.comap_map_eq_self_of_isMaximal f (integer_map_asIdeal_ne_top K S hv)).ge.trans
      (Ideal.comap_mono hle)
  have hceq : M.comap f = v.asIdeal :=
    (v.isMaximal.eq_of_le (hM.isPrime.comap f).ne_top hcle).symm
  rwa [← integer_map_comap_eq K S M, hceq] at hM

/-- The prime of `𝒪_S` above a prime `v ∉ S` of `R`: the extension of `v`. -/
noncomputable def integerPrimeOverOfNotMem {v : HeightOneSpectrum R} (hv : v ∉ S) :
    HeightOneSpectrum (S.integer K) where
  asIdeal := Ideal.map (algebraMap R (S.integer K)) v.asIdeal
  isPrime := (isMaximal_integer_map_asIdeal K S hv).isPrime
  ne_bot := Ideal.map_ne_bot_of_ne_bot v.ne_bot

@[simp] lemma integerPrimeOverOfNotMem_asIdeal {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (integerPrimeOverOfNotMem K S hv).asIdeal
      = Ideal.map (algebraMap R (S.integer K)) v.asIdeal := by
  simp only [integerPrimeOverOfNotMem]

/-- For `v ∉ S`, the contraction of the extension of `v ^ n` is `v ^ n` again. Mathlib's
`Ideal.comap_map_eq_self_of_isMaximal` gives this only for `n = 1`. -/
@[simp] lemma integer_comap_map_pow {v : HeightOneSpectrum R} (hv : v ∉ S) (n : ℕ) :
    (Ideal.map (algebraMap R (S.integer K)) (v.asIdeal ^ n)).comap
        (algebraMap R (S.integer K)) = v.asIdeal ^ n := by
  set f := algebraMap R (S.integer K)
  have hP0 : Ideal.map f v.asIdeal ≠ 0 := Ideal.map_ne_bot_of_ne_bot v.ne_bot
  have hPnu : ¬ IsUnit (Ideal.map f v.asIdeal) :=
    fun h ↦ integer_map_asIdeal_ne_top K S hv (Ideal.isUnit_iff.mp h)
  refine le_antisymm ?_ Ideal.le_comap_map
  have hdvd : (Ideal.map f (v.asIdeal ^ n)).comap f ∣ v.asIdeal ^ n :=
    Ideal.dvd_iff_le.mpr Ideal.le_comap_map
  obtain ⟨j, -, hassoc⟩ := (dvd_prime_pow v.prime n).mp hdvd
  rw [associated_iff_eq] at hassoc
  have hmapQ : Ideal.map f ((Ideal.map f (v.asIdeal ^ n)).comap f) =
      Ideal.map f (v.asIdeal ^ n) := integer_map_comap_eq K S _
  rw [hassoc] at hmapQ
  simp only [Ideal.map_pow] at hmapQ
  rw [hassoc, (pow_inj_of_not_isUnit hPnu hP0).mp hmapQ]

/-- For `v ∉ S`, an ideal `J` of `R` is contained in `v ^ k` exactly when its extension to `𝒪_S`
is contained in the `k`-th power of the prime above `v`. -/
lemma integer_map_le_map_pow_iff {v : HeightOneSpectrum R} (hv : v ∉ S) (J : Ideal R) (k : ℕ) :
    Ideal.map (algebraMap R (S.integer K)) J ≤ (integerPrimeOverOfNotMem K S hv).asIdeal ^ k ↔
      J ≤ v.asIdeal ^ k := by
  rw [integerPrimeOverOfNotMem_asIdeal, ← Ideal.map_pow]
  exact ⟨fun h ↦ Ideal.le_comap_map.trans
    ((Ideal.comap_mono h).trans (integer_comap_map_pow K S hv k).le), Ideal.map_mono⟩

/-- The prime of `R` below a prime `P` of `𝒪_S`: its contraction. -/
noncomputable def integerPrimeUnder (P : HeightOneSpectrum (S.integer K)) :
    HeightOneSpectrum R where
  asIdeal := P.asIdeal.comap (algebraMap R (S.integer K))
  isPrime := P.isPrime.comap _
  ne_bot := integer_comap_ne_bot K S P.ne_bot

@[simp] lemma integerPrimeUnder_asIdeal (P : HeightOneSpectrum (S.integer K)) :
    (integerPrimeUnder K S P).asIdeal = P.asIdeal.comap (algebraMap R (S.integer K)) := by
  simp only [integerPrimeUnder]

/-- A prime under a prime of `𝒪_S` never lies in `S`. -/
lemma integerPrimeUnder_notMem (P : HeightOneSpectrum (S.integer K)) :
    integerPrimeUnder K S P ∉ S := by
  -- The primes of `S` become the unit ideal in `𝒪_S`, and a prime is not the unit ideal.
  intro hv
  have h1 := integer_map_asIdeal_eq_top K S hv
  rw [integerPrimeUnder_asIdeal, integer_map_comap_eq] at h1
  exact P.isPrime.ne_top h1

/-- Extending `v ∉ S` to `𝒪_S` and contracting back returns `v`. -/
@[simp] lemma integerPrimeUnder_integerPrimeOverOfNotMem {v : HeightOneSpectrum R} (hv : v ∉ S) :
    integerPrimeUnder K S (integerPrimeOverOfNotMem K S hv) = v :=
  have := v.isMaximal
  HeightOneSpectrum.ext <|
    Ideal.comap_map_eq_self_of_isMaximal _ (integer_map_asIdeal_ne_top K S hv)

/-- Contracting a prime of `𝒪_S` and extending back returns it. -/
@[simp] lemma integerPrimeOverOfNotMem_integerPrimeUnder (P : HeightOneSpectrum (S.integer K)) :
    integerPrimeOverOfNotMem K S (integerPrimeUnder_notMem K S P) = P :=
  HeightOneSpectrum.ext <| integer_map_comap_eq K S P.asIdeal

/-- **The height-one primes of `𝒪_S` are exactly the height-one primes of `R` not in `S`.** -/
noncomputable def integerHeightOneSpectrumEquiv :
    {v : HeightOneSpectrum R // v ∉ S} ≃ HeightOneSpectrum (S.integer K) where
  toFun v := integerPrimeOverOfNotMem K S v.property
  invFun P := ⟨integerPrimeUnder K S P, integerPrimeUnder_notMem K S P⟩
  left_inv v := Subtype.ext <| integerPrimeUnder_integerPrimeOverOfNotMem K S v.property
  right_inv P := integerPrimeOverOfNotMem_integerPrimeUnder K S P

@[simp] lemma integerHeightOneSpectrumEquiv_apply (v : {v : HeightOneSpectrum R // v ∉ S}) :
    integerHeightOneSpectrumEquiv K S v = integerPrimeOverOfNotMem K S v.property := by
  simp only [integerHeightOneSpectrumEquiv, Equiv.coe_fn_mk]

@[simp] lemma integerHeightOneSpectrumEquiv_symm_apply_coe (P : HeightOneSpectrum (S.integer K)) :
    ((integerHeightOneSpectrumEquiv K S).symm P : HeightOneSpectrum R)
      = integerPrimeUnder K S P := by
  simp only [integerHeightOneSpectrumEquiv, Equiv.coe_fn_symm_mk]

/-- For `v ∉ S`, the prime of `𝒪_S` above `v` lies over `v`. -/
instance liesOver_integerPrimeOverOfNotMem {v : HeightOneSpectrum R} (hv : v ∉ S) :
    (integerPrimeOverOfNotMem K S hv).asIdeal.LiesOver v.asIdeal where
  over := by
    have := v.isMaximal
    rw [Ideal.under, integerPrimeOverOfNotMem_asIdeal,
      Ideal.comap_map_eq_self_of_isMaximal _ (integer_map_asIdeal_ne_top K S hv)]

/-- **The correspondence preserves valuations**: the valuation of `𝒪_S` at the prime above `v` is
the valuation of `R` at `v`. Mathlib's `valuation_liesOver` relates the two by the ramification
index, which is `1` here. -/
@[simp]
lemma valuation_integerPrimeOverOfNotMem {v : HeightOneSpectrum R} (hv : v ∉ S) (x : K) :
    (integerPrimeOverOfNotMem K S hv).valuation K x = v.valuation K x := by
  have h := HeightOneSpectrum.valuation_liesOver (A := R) (B := S.integer K) K v
    (integerPrimeOverOfNotMem K S hv) x
  -- the extended ideal *is* the prime above, so Mathlib's `ramificationIdx'_map_self_eq_one` gives
  -- the index directly
  have hone : Ideal.ramificationIdx' v.asIdeal (integerPrimeOverOfNotMem K S hv).asIdeal = 1 := by
    rw [integerPrimeOverOfNotMem_asIdeal]
    exact Ideal.ramificationIdx'_map_self_eq_one (integer_map_asIdeal_ne_top K S hv)
      (Ideal.map_ne_bot_of_ne_bot v.ne_bot)
  rwa [hone, pow_one, Algebra.algebraMap_self, RingHom.id_apply, eq_comm] at h

/-- The correspondence preserves valuations, phrased through the equivalence. Not a `simp` lemma:
`integerHeightOneSpectrumEquiv_apply` rewrites the left-hand side to
`integerPrimeOverOfNotMem` first, so this form is never in normal form — the `simp` lemma is
`valuation_integerPrimeOverOfNotMem` above. -/
lemma valuation_integerHeightOneSpectrumEquiv (v : {v : HeightOneSpectrum R // v ∉ S}) (x : K) :
    (integerHeightOneSpectrumEquiv K S v).valuation K x
      = (v : HeightOneSpectrum R).valuation K x := by
  rw [integerHeightOneSpectrumEquiv_apply, valuation_integerPrimeOverOfNotMem]

/-- **The correspondence preserves valuations, read downwards**: the valuation of `𝒪_S` at an
arbitrary prime `P` is the valuation of `R` at the prime under `P`. This is the form a consumer
holding a prime of `𝒪_S` — rather than one of `R` avoiding `S` — can apply directly.

Not a `simp` lemma: its left-hand side is an unrestricted `P.valuation K x`, so tagging it would
rewrite every valuation on `𝒪_S`, including the one `valuation_integerPrimeOverOfNotMem` is the
normal form for. -/
lemma valuation_integerPrimeUnder (P : HeightOneSpectrum (S.integer K)) (x : K) :
    P.valuation K x = (integerPrimeUnder K S P).valuation K x :=
  calc P.valuation K x
      = (integerPrimeOverOfNotMem K S (integerPrimeUnder_notMem K S P)).valuation K x := by
        rw [integerPrimeOverOfNotMem_integerPrimeUnder]
    _ = (integerPrimeUnder K S P).valuation K x := valuation_integerPrimeOverOfNotMem K S _ x

end IsDedekindDomain

end
