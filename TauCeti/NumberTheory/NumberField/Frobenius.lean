/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import TauCeti.NumberTheory.LegendreSymbol.Frobenius
public import TauCeti.NumberTheory.NumberField.IntegralSqrt
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

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
* **the square-root action** — for `p` odd and `x ∈ K` with `x² = d ∈ ℤ`, `p ∤ d`, a
  Frobenius at any ideal `Q` over `p` satisfies `σ x = legendreSym p d • x`, transporting the
  `𝓞 K`-level computation `TauCeti.AlgHom.IsArithFrobAt.apply_sqrt` along the Galois action
  on the ring of integers (via `integralClosure.coe_smul`), with the `σ x = x`
  characterization read off from it.

`TauCeti.NumberTheory.Multiquadratic.Frobenius` combines the two to describe the Frobenius of
a multiquadratic field on all its generators at once (Layer 1 of the multiquadratic roadmap).

## Main results

* `TauCeti.NumberField.exists_isArithFrobAt`: a Frobenius exists at every nonzero prime of
  `𝓞 K`.
* `TauCeti.NumberField.isArithFrobAt_apply_sqrt`: a Frobenius at `Q ∣ p` sends a square root
  of `d` to `legendreSym p d` times it.
* `TauCeti.NumberField.isArithFrobAt_apply_sqrt_eq_self_iff`: it fixes `√d` iff `d` is a
  quadratic residue mod `p`.
-/

public section

open Ideal

open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

/-- **Frobenius elements exist.** For a Galois number field `K/ℚ` and a *nonzero* prime `Q` of
`𝓞 K`, some `σ ∈ Gal(K/ℚ)` is an arithmetic Frobenius at `Q`. This is Mathlib's
`IsArithFrobAt.exists_of_isInvariant` with the number-field side conditions discharged (a
nonzero prime of `𝓞 K` is maximal, with finite residue field). -/
theorem exists_isArithFrobAt [IsGalois ℚ K] (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    ∃ σ : K ≃ₐ[ℚ] K, IsArithFrobAt ℤ σ Q := by
  haveI : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ ‹Q.IsPrime›
  exact IsArithFrobAt.exists_of_isInvariant ℤ (K ≃ₐ[ℚ] K) Q

/-- A Frobenius exists at every prime of `𝓞 K` lying over a rational prime — the form used when
`Q` is presented by a `LiesOver` instance rather than a nonvanishing hypothesis. -/
theorem exists_isArithFrobAt_of_liesOver [IsGalois ℚ K] {p : ℕ} [Fact p.Prime]
    (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    ∃ σ : K ≃ₐ[ℚ] K, IsArithFrobAt ℤ σ Q := by
  have hp : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact exists_isArithFrobAt Q (Ideal.ne_bot_of_liesOver_of_ne_bot hp Q)

/-- **A Frobenius acts on square roots by the Legendre symbol.** Let `K` be a number field,
`p` an odd prime, and `σ ∈ Gal(K/ℚ)` an arithmetic Frobenius at an ideal `Q` of `𝓞 K` above
`p`. If `x ∈ K` satisfies `x² = d` for an integer `d` with `p ∤ d`, then

`σ x = legendreSym p d • x`:

the Frobenius fixes `√d` when `d` is a quadratic residue mod `p` and negates it otherwise. -/
theorem isArithFrobAt_apply_sqrt (hodd : p ≠ 2) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d)
    {x : K} (hx : x ^ 2 = algebraMap ℤ K d)
    (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(p : ℤ)})]
    {σ : K ≃ₐ[ℚ] K} (hσ : IsArithFrobAt ℤ σ Q) :
    σ x = legendreSym p d • x := by
  -- Apply the `𝓞 K`-level computation to the packaged square root and push down along `𝓞 K ↪ K`.
  have hsmul : σ • integralSqrt hx = legendreSym p d • integralSqrt hx :=
    TauCeti.IsArithFrobAt.smul_sqrt hσ hodd hd (integralSqrt_sq hx)
  have hcoe := congrArg (algebraMap (𝓞 K) K) hsmul
  -- `algebraMap` intertwines the Galois actions on `𝓞 K` and `K` (`integralClosure.coe_smul`).
  have hbridge : algebraMap (𝓞 K) K (σ • integralSqrt hx) =
      σ (algebraMap (𝓞 K) K (integralSqrt hx)) := by
    have hc : algebraMap (𝓞 K) K (σ • integralSqrt hx) =
        σ • algebraMap (𝓞 K) K (integralSqrt hx) :=
      integralClosure.coe_smul σ (integralSqrt hx)
    rw [hc, AlgEquiv.smul_def]
  rw [map_zsmul, algebraMap_integralSqrt, hbridge] at hcoe
  rwa [algebraMap_integralSqrt] at hcoe

/-- **A Frobenius fixes `√d` iff `d` is a quadratic residue mod `p`.** Under the hypotheses of
`TauCeti.NumberField.isArithFrobAt_apply_sqrt`, `σ x = x` exactly when `legendreSym p d = 1`
(the other case being `σ x = -x`, `legendreSym p d = -1`). This reads the characteristic
biconditional off the `•` form, using that `x ≠ 0` (as `d ≠ 0`). -/
theorem isArithFrobAt_apply_sqrt_eq_self_iff (hodd : p ≠ 2) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d)
    {x : K} (hx : x ^ 2 = algebraMap ℤ K d)
    (Q : Ideal (𝓞 K)) [Q.LiesOver (span {(p : ℤ)})]
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

end TauCeti.NumberField
