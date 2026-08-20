/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import TauCeti.RingTheory.Valuation.Discrete.Order

/-!
# Normalized valuations of the fraction field of a Dedekind domain are adic

Mathlib attaches to every height one prime `𝔭` of a Dedekind domain `R` a normalized
`ℤᵐ⁰`-valued valuation `𝔭.valuation K` of the fraction field `K`, and shows that distinct primes
give inequivalent valuations. This file proves the converse: a normalized valuation of `K` whose
valuation ring contains `R` *is* `𝔭.valuation K` for a unique height one prime `𝔭` of `R`, namely
the centre of the valuation on `R`.

## Main definitions

* `Valuation.centerIdeal`: the centre `{r : R | w r < 1}` on `R` of a valuation `w` of `K` whose
  valuation ring contains `R`.
* `Valuation.heightOneSpectrum`: that centre, bundled as a height one prime of `R`.

## Main results

* `Valuation.eq_valuation_of_forall_mem_asIdeal_iff`: a normalized valuation bounded by `1` on `R`
  and of positive value exactly on a height one prime `𝔭` is the adic valuation of `𝔭`.
* `Valuation.valuation_heightOneSpectrum`: the adic valuation of the centre of `w` on `R` is `w`.
* `Valuation.existsUnique_heightOneSpectrum_valuation_eq`: the centre is the only height one prime
  whose adic valuation is `w`.

## Implementation notes

The comparison goes through `Valuation.isEquiv_iff_val_le_one` and the normalization lemma
`Valuation.eq_of_isEquiv_of_surjective`: both valuations are surjective onto `ℤᵐ⁰`, so it is
enough to see that they have the same valuation ring. That in turn uses only that the two
valuations are bounded by `1` on `R` and are `< 1` on the same elements of `R`, together with
Mathlib's `IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq`, which writes an
arbitrary element of `K` as a fraction with denominator outside `𝔭`, in one of the two possible
directions.

`Valuation.centerIdeal` and `Valuation.heightOneSpectrum` keep their bodies unexposed; the
characterization lemmas `Valuation.mem_centerIdeal` and `Valuation.asIdeal_heightOneSpectrum` are
the interface. The latter's definitional proof is parenthesized (`(rfl)`) so that it is not inferred
to be `@[defeq]`, which would require the body to be exposed.
-/

public section

open scoped WithZero

open IsDedekindDomain

namespace Valuation

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
  {w : _root_.Valuation K ℤᵐ⁰}

section CenterIdeal

variable (R) in
/-- The **centre** on `R` of a valuation `w` of `K` whose valuation ring contains `R`: the ideal
of elements of `R` of positive valuation. It is prime (`Valuation.isPrime_centerIdeal`), and it is
nonzero as soon as `w` is nontrivial and `K` is the fraction field of `R`
(`Valuation.centerIdeal_ne_bot`). -/
def centerIdeal (w : _root_.Valuation K ℤᵐ⁰) (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    Ideal R :=
  (IsLocalRing.maximalIdeal w.valuationSubring).comap
    ((algebraMap R K).codRestrict w.valuationSubring fun r ↦
      (w.mem_valuationSubring_iff _).mpr (hR r))

/-- An element belongs to the centre ideal exactly when its valuation is strictly below `1`. -/
@[simp]
theorem mem_centerIdeal {r : R} {hR : ∀ r : R, w (algebraMap R K r) ≤ 1} :
    r ∈ centerIdeal R w hR ↔ w (algebraMap R K r) < 1 := by
  rw [centerIdeal, Ideal.mem_comap, w.mem_maximalIdeal_iff]
  rfl

/-- Off its centre, a valuation bounded by `1` on `R` takes the value `1`. -/
theorem eq_one_of_notMem_centerIdeal {r : R} (hR : ∀ r : R, w (algebraMap R K r) ≤ 1)
    (hr : r ∉ centerIdeal R w hR) : w (algebraMap R K r) = 1 :=
  le_antisymm (hR r) (not_lt.mp (mt mem_centerIdeal.mpr hr))

/-- The centre of a valuation bounded by `1` on `R` is a prime ideal of `R`. -/
theorem isPrime_centerIdeal (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    (centerIdeal R w hR).IsPrime :=
  (IsLocalRing.maximalIdeal w.valuationSubring).comap_isPrime _

/-- The centre of a nontrivial valuation of the fraction field `K` of `R` is a nonzero ideal of
`R`: an element of `K` of value below `1` is a fraction `a / b` whose numerator `a` is a nonzero
element of the centre. -/
theorem centerIdeal_ne_bot [IsDomain R] [IsFractionRing R K] [w.IsNontrivial]
    (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) : centerIdeal R w hR ≠ ⊥ := by
  obtain ⟨y, hy0, hy1⟩ := Valuation.IsNontrivial.exists_lt_one (v := w)
  obtain ⟨ab, hab⟩ := IsLocalization.surj (nonZeroDivisors R) y
  have hb : algebraMap R K (ab.2 : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ab.2.2
  have ha0 : ab.1 ≠ 0 := by
    intro h
    rw [h, map_zero] at hab
    exact (mul_eq_zero.mp hab).elim hy0 hb
  have hmem : ab.1 ∈ centerIdeal R w hR := by
    rw [mem_centerIdeal]
    calc w (algebraMap R K ab.1) = w (y * algebraMap R K (ab.2 : R)) := by rw [hab]
      _ = w y * w (algebraMap R K (ab.2 : R)) := w.map_mul _ _
      _ ≤ w y * 1 := mul_le_mul_right (hR ab.2) _
      _ < 1 := by simpa using hy1
  exact fun h ↦ ha0 (by simpa [h] using hmem)

end CenterIdeal

section Comparison

variable [IsDedekindDomain R] [IsFractionRing R K]

/-- **A normalized valuation of the fraction field of a Dedekind domain `R` that is bounded by `1`
on `R` and of positive value exactly at a height one prime `𝔭` is the adic valuation of `𝔭`.** -/
theorem eq_valuation_of_forall_mem_asIdeal_iff {𝔭 : HeightOneSpectrum R}
    (hw : Function.Surjective w) (hR : ∀ r : R, w (algebraMap R K r) ≤ 1)
    (h𝔭 : ∀ r : R, r ∈ 𝔭.asIdeal ↔ w (algebraMap R K r) < 1) :
    𝔭.valuation K = w := by
  -- On `R` both valuations are bounded by `1` and are `< 1` on the members of `𝔭`, so they take
  -- the value `1` on exactly the same elements of `R`.
  have hone : ∀ r : R, 𝔭.valuation K (algebraMap R K r) = 1 ↔ w (algebraMap R K r) = 1 := by
    intro r
    rw [𝔭.valuation_eq_one_iff_notMem, h𝔭 r]
    exact ⟨fun h ↦ le_antisymm (hR r) (not_lt.mp h), fun h ↦ by simp [h]⟩
  refine eq_of_isEquiv_of_surjective (𝔭.valuation_surjective K) hw
    (isEquiv_iff_val_le_one.mpr fun {x} ↦ ?_)
  obtain ⟨n, d, hnd | hnd⟩ := 𝔭.exists_primeCompl_mul_eq_or_mul_eq x
  · -- `x = n / d` with `d` outside `𝔭`: both valuations of `x` are those of `n`, hence `≤ 1`.
    have hd : 𝔭.valuation K (algebraMap R K (d : R)) = 1 :=
      𝔭.valuation_eq_one_iff_notMem.mpr d.2
    have h₁ : 𝔭.valuation K x = 𝔭.valuation K (algebraMap R K n) := by
      rw [← hnd, map_mul, hd, mul_one]
    have h₂ : w x = w (algebraMap R K n) := by
      rw [← hnd, w.map_mul, (hone (d : R)).mp hd, mul_one]
    exact iff_of_true (h₁ ▸ 𝔭.valuation_le_one n) (h₂ ▸ hR n)
  · -- `x = d / n` with `d` outside `𝔭`: either valuation of `x` is `≤ 1` exactly when the
    -- corresponding valuation of `n` equals `1`.
    have key : ∀ v : _root_.Valuation K ℤᵐ⁰, v (algebraMap R K n) ≤ 1 →
        v (algebraMap R K (d : R)) = 1 → (v x ≤ 1 ↔ v (algebraMap R K n) = 1) := by
      intro v hvn hvd
      have hx : v x * v (algebraMap R K n) = 1 := by rw [← v.map_mul, hnd, hvd]
      refine ⟨fun hle ↦ ?_, fun hn ↦ le_of_eq (by rwa [hn, mul_one] at hx)⟩
      by_contra hne
      have hlt : v x * v (algebraMap R K n) < 1 :=
        calc v x * v (algebraMap R K n) ≤ 1 * v (algebraMap R K n) := mul_le_mul_left hle _
          _ = v (algebraMap R K n) := one_mul _
          _ < 1 := lt_of_le_of_ne hvn hne
      exact absurd hx hlt.ne
    have hd : 𝔭.valuation K (algebraMap R K (d : R)) = 1 :=
      𝔭.valuation_eq_one_iff_notMem.mpr d.2
    rw [key _ (𝔭.valuation_le_one n) hd, key _ (hR n) ((hone (d : R)).mp hd), hone n]

variable (R) in
/-- The height one prime of `R` at which a nontrivial valuation of `K` bounded by `1` on `R` is
centred. Once `w` is moreover normalized, its adic valuation is `w` itself
(`Valuation.valuation_heightOneSpectrum`) and it is the only height one prime with that property
(`Valuation.eq_heightOneSpectrum`). -/
def heightOneSpectrum (w : _root_.Valuation K ℤᵐ⁰) [w.IsNontrivial]
    (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) : HeightOneSpectrum R where
  asIdeal := centerIdeal R w hR
  isPrime := isPrime_centerIdeal hR
  ne_bot := centerIdeal_ne_bot hR

/-- The underlying ideal of `heightOneSpectrum` is the centre ideal. -/
@[simp]
theorem asIdeal_heightOneSpectrum [w.IsNontrivial]
    (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    (heightOneSpectrum R w hR).asIdeal = centerIdeal R w hR := (rfl)

/-- **The adic valuation of the centre of `w` on `R` is `w` itself**: a normalized valuation of the
fraction field of a Dedekind domain whose valuation ring contains that domain is adic. -/
@[simp]
theorem valuation_heightOneSpectrum [w.IsNontrivial] (hw : Function.Surjective w)
    (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    (heightOneSpectrum R w hR).valuation K = w :=
  eq_valuation_of_forall_mem_asIdeal_iff hw hR fun _ ↦ by
    rw [asIdeal_heightOneSpectrum, mem_centerIdeal]

/-- A height one prime whose adic valuation is `w` is the centre of `w`. -/
theorem eq_heightOneSpectrum {𝔮 : HeightOneSpectrum R} [w.IsNontrivial]
    (hw : Function.Surjective w) (hR : ∀ r : R, w (algebraMap R K r) ≤ 1)
    (h : 𝔮.valuation K = w) : 𝔮 = heightOneSpectrum R w hR :=
  HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := K)
    (by rw [h, valuation_heightOneSpectrum hw hR])

variable (R) in
/-- **A normalized valuation of the fraction field of a Dedekind domain `R` whose valuation ring
contains `R` is the adic valuation of a unique height one prime of `R`.** -/
theorem existsUnique_heightOneSpectrum_valuation_eq [w.IsNontrivial]
    (hw : Function.Surjective w) (hR : ∀ r : R, w (algebraMap R K r) ≤ 1) :
    ∃! 𝔭 : HeightOneSpectrum R, 𝔭.valuation K = w :=
  ⟨heightOneSpectrum R w hR, valuation_heightOneSpectrum hw hR,
    fun _ h ↦ eq_heightOneSpectrum hw hR h⟩

end Comparison

end Valuation
