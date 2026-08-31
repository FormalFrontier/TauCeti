/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import TauCeti.NumberTheory.LegendreSymbol.Frobenius
public import TauCeti.NumberTheory.NumberField.IntegralSqrt
import TauCeti.NumberTheory.NumberField.AutomorphismAction
import Mathlib.Algebra.CharP.Basic

/-!
# Frobenius elements of a Galois number field and their action on square roots

For a Galois number field `K/ℚ` and a prime `Q` of `𝓞 K` over the rational prime `p`, an
arithmetic Frobenius at `Q` is a `σ ∈ Gal(K/ℚ)` with `σ x ≡ x ^ #(ℤ ⧸ Q ∩ ℤ) (mod Q)` for all
`x : 𝓞 K` — the exponent is the cardinality of the *base* residue ring `ℤ ⧸ Q ∩ ℤ`, which is
`p` for `Q` over `(p)`, distinguishing the arithmetic Frobenius from the absolute one (whose
exponent would be the residue-field norm `p^f`). This file provides the two number-field
services on top of Mathlib's `RingTheory/Frobenius.lean`:

* **existence** — a Frobenius exists at every nonzero prime of `𝓞 K`
  (`IsArithFrobAt.exists_of_isInvariant` with the number-field instances discharged: the
  residue field of a nonzero prime is finite, and the Galois action on `𝓞 K` has invariants
  `ℤ`); and
* **uniqueness** — at an unramified prime, the Frobenius is unique in the Galois group, by
  combining Mathlib's integral-ring uniqueness theorem with the faithfulness of the Galois
  action; and
* **the square-root action** — for `p` odd and `x ∈ K` with `x² = d ∈ ℤ`, `p ∤ d`, a
  Frobenius at any ideal `Q` over `p` satisfies `σ x = legendreSym p d • x`, transporting the
  `𝓞 K`-level computation `TauCeti.AlgHom.IsArithFrobAt.apply_sqrt` along the Galois action
  on the ring of integers (via `NumberField.algebraMap_smul_eq_apply`), with the `σ x = x`
  characterization read off from it.

`TauCeti.NumberTheory.Multiquadratic.Frobenius` combines the two to describe the Frobenius of
a multiquadratic field on all its generators at once (Layer 1 of the multiquadratic roadmap).

## Main results

* `NumberField.exists_isArithFrobAt`: a Frobenius exists at every nonzero prime of
  `𝓞 K`.
* `NumberField.isArithFrobAt_eq_of_isUnramifiedAt`: two Frobenius elements at an unramified
  prime are equal.
* `NumberField.subsingleton_isArithFrobAt`: the type of Frobenius elements at an unramified
  prime is a subsingleton.
* `NumberField.isArithFrobAt_apply_sqrt`: a Frobenius at `Q ∣ p` sends a square root
  of `d` to `legendreSym p d` times it.
* `NumberField.isArithFrobAt_apply_sqrt_eq_self_iff`: it fixes `√d` iff `d` is a
  quadratic residue mod `p`.
-/

public section

open Ideal

open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

/-- **Frobenius elements exist.** For a Galois number field `K/ℚ` and a *nonzero* prime `Q` of
`𝓞 K`, some `σ ∈ Gal(K/ℚ)` is an arithmetic Frobenius at `Q`. This is Mathlib's
`IsArithFrobAt.exists_of_isInvariant` with the number-field side conditions discharged (a
nonzero prime of `𝓞 K` is maximal, with finite residue field). -/
theorem exists_isArithFrobAt [IsGalois ℚ K] (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    ∃ σ : K ≃ₐ[ℚ] K, IsArithFrobAt ℤ σ Q := by
  have : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ ‹Q.IsPrime›
  exact IsArithFrobAt.exists_of_isInvariant ℤ (K ≃ₐ[ℚ] K) Q

/-- A Frobenius exists at every prime of `𝓞 K` lying over a rational prime — the form used when
`Q` is presented by a `LiesOver` instance rather than a nonvanishing hypothesis. -/
theorem exists_isArithFrobAt_of_liesOver [IsGalois ℚ K] {p : ℕ} [Fact p.Prime]
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    ∃ σ : K ≃ₐ[ℚ] K, IsArithFrobAt ℤ σ Q := by
  have hp : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact exists_isArithFrobAt Q (Ideal.ne_bot_of_liesOver_of_ne_bot hp Q)

/-! ### Uniqueness at unramified primes

Mathlib proves uniqueness for algebra homomorphisms of the integral rings.  The Galois-group
form below first applies that theorem to the action on `𝓞 L`, then uses the faithful Galois
action to recover equality of the automorphisms themselves.  In the number-field setting the
complement of every prime consists of non-zero-divisors, which discharges the remaining
hypothesis of the generic theorem.
-/

/-- **Frobenius elements are unique at an unramified prime.** If `Q` is a nonzero prime of the
ring of integers of a finite Galois extension `L/K`, then two arithmetic Frobenius elements at
`Q` coincide whenever `L/K` is unramified at `Q`.

This is the Galois-group form of `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`. -/
theorem isArithFrobAt_eq_of_isUnramifiedAt {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    {σ τ : L ≃ₐ[K] L} {Q : Ideal (𝓞 L)} [Q.IsPrime] (_hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (hσ : IsArithFrobAt (𝓞 K) σ Q)
    (hτ : IsArithFrobAt (𝓞 K) τ Q) : σ = τ := by
  have heq : MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) σ =
      MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) τ :=
    AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt (φ :=
        MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) σ) (ψ :=
        MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) τ) hσ hτ
      (Ideal.primeCompl_le_nonZeroDivisors Q)
  exact (IsGaloisGroup.faithful (𝓞 K)).eq_of_smul_eq_smul fun x ↦
    DFunLike.congr_fun heq x

/-- The Frobenius elements at a nonzero unramified prime form a subsingleton. -/
theorem subsingleton_isArithFrobAt {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsGalois K L]
    {Q : Ideal (𝓞 L)} [Q.IsPrime] (_hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] :
    Subsingleton {σ : L ≃ₐ[K] L // IsArithFrobAt (𝓞 K) σ Q} where
  allEq σ τ := Subtype.ext (isArithFrobAt_eq_of_isUnramifiedAt _hQ σ.property τ.property)

/-- **A Frobenius acts on square roots by the Legendre symbol.** Let `K` be a number field,
`p` an odd prime, and `σ ∈ Gal(K/ℚ)` an arithmetic Frobenius at an ideal `Q` of `𝓞 K` above
`p`. If `x ∈ K` satisfies `x² = d` for an integer `d` with `p ∤ d`, then

`σ x = legendreSym p d • x`:

the Frobenius fixes `√d` when `d` is a quadratic residue mod `p` and negates it otherwise. -/
theorem isArithFrobAt_apply_sqrt (hodd : p ≠ 2) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d)
    {x : K} (hx : x ^ 2 = algebraMap ℤ K d) (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ x = legendreSym p d • x := by
  -- Apply the `𝓞 K`-level computation to the packaged square root and push down along `𝓞 K ↪ K`.
  have hsmul : σ • integralSqrt hx = legendreSym p d • integralSqrt hx :=
    TauCeti.IsArithFrobAt.smul_sqrt hσ hodd hd (integralSqrt_sq hx)
  have hcoe := congrArg (algebraMap (𝓞 K) K) hsmul
  rw [map_zsmul, algebraMap_integralSqrt, algebraMap_smul_eq_apply] at hcoe
  rwa [algebraMap_integralSqrt] at hcoe

/-- **A Frobenius fixes `√d` iff `d` is a quadratic residue mod `p`.** Under the hypotheses of
`NumberField.isArithFrobAt_apply_sqrt`, `σ x = x` exactly when `legendreSym p d = 1`
(the other case being `σ x = -x`, `legendreSym p d = -1`). This reads the characteristic
biconditional off the `•` form, using that `x ≠ 0` (as `d ≠ 0`). -/
theorem isArithFrobAt_apply_sqrt_eq_self_iff (hodd : p ≠ 2) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d)
    {x : K} (hx : x ^ 2 = algebraMap ℤ K d) (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ x = x ↔ legendreSym p d = 1 := by
  have happ := isArithFrobAt_apply_sqrt hodd hd hx Q hσ
  have hxne : x ≠ 0 := by
    rintro rfl
    refine hd ?_
    have hz : algebraMap ℤ K d = 0 := by rw [← hx]; simp
    rw [FaithfulSMul.algebraMap_injective ℤ K (hz.trans (map_zero _).symm)]
    exact dvd_zero _
  constructor
  · intro hfix
    rw [hfix] at happ
    rcases legendreSym.eq_one_or_neg_one p
        (by rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hd) with h1 | h1
    · exact h1
    · rw [h1, neg_smul, one_smul] at happ
      have hchar : ringChar K ≠ 2 := by rw [ringChar.eq_zero]; norm_num
      exact absurd ((Ring.eq_self_iff_eq_zero_of_char_ne_two hchar).mp happ.symm) hxne
  · intro h1
    rw [happ, h1, one_smul]

end NumberField
