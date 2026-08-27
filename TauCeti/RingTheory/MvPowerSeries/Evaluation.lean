/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Evaluating a multivariate power series into a power of an adic ideal

Let `S` carry the `I`-adic topology for an ideal `I`, and let `f` be a multivariate power series
evaluated at a family `a : σ → S` through a continuous coefficient map `φ`. This file bounds the
value `eval₂ φ a f` by a power of `I`, in the three forms the estimate is used in: the value is
confined to `I ^ k` as soon as the arguments are and `φ` sends the constant term there, and the
confinement improves when the series vanishes in low total degree or when `φ` sends every
coefficient into a power of `I`.

All three have the same one-line mechanism. `MvPowerSeries.hasSum_eval₂` writes the value as the
sum of its monomial values `φ (coeff d f) * ∏ s, a s ^ d s`; each such monomial is checked to lie
in the relevant power of `I`; and the sum of a family inside `I ^ n` stays inside `I ^ n` because
`I ^ n` is closed (`IsAdic.isClosed_pow`) and `tsum_mem` applies. The three statements differ only
in which power the monomial estimate produces.

Three hypotheses of the source turn out to be unnecessary. Nothing asks for `I` to be maximal or
for `S` to be local, only that the topology be `I`-adic, so the results are stated for an
arbitrary ideal; the coefficient map is an arbitrary continuous `φ : R →+* S` rather than the
identity, since `MvPowerSeries.hasSum_eval₂` is already stated at that generality; and the index
type need not be finite, because the summation argument uses only the `Tendsto a cofinite (𝓝 0)`
already carried by `HasEval`. Taking `I` to be `IsLocalRing.maximalIdeal S` and `φ` to be
`RingHom.id S` recovers the source statements.

## Main results

* `MvPowerSeries.eval₂_mem_pow` : arguments in `I ^ k`, and a constant term whose image under
  `φ` lies in `I ^ k`, confine the value to `I ^ k`.
* `MvPowerSeries.eval₂_mem_pow_mul` : a series vanishing below total degree `c`, evaluated at
  arguments of `I ^ j`, takes values in `I ^ (c * j)`.
* `MvPowerSeries.eval₂_mem_pow_add_mul` : if moreover `φ` sends every coefficient into `I ^ k`,
  the value lies in `I ^ (k + c * j)`.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` (`github.com/MichaelStollBayreuth/EllipticCurves`,
Apache-2.0) at commit `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, file
`EllipticCurves/WeierstrassFormalGroup/Eval.lean`, where these are
`ChabautyColeman.MvPSeries.eval_mem_maximalIdeal_pow`, `..._pow_mul` and `..._pow_add_mul`. That
development evaluates through its own `ChabautyColeman.MvPSeries.eval`, which is by definition
`MvPowerSeries.eval₂ (RingHom.id _)`; the wrapper is dropped here and the statements are made
directly about Mathlib's `MvPowerSeries.eval₂`, as are the generalisations noted above. The
monomial estimates and the closed-ideal summation argument are the source's.
-/

public section

namespace MvPowerSeries

section Monomial

variable {σ : Type*} {S : Type*} [CommRing S] {a : σ → S} {I : Ideal S}

/-- The monomial estimate behind all three results: a product of powers of elements of `I ^ j`
lies in `I ^ (j * ∑ exponents)`. Stated over an arbitrary `Finset` so that the induction has
somewhere to run. -/
private theorem prod_mem_pow_mul_sum {j : ℕ} (hmem : ∀ i, a i ∈ I ^ j) (d : σ →₀ ℕ)
    (t : Finset σ) : (∏ s ∈ t, a s ^ d s) ∈ I ^ (j * ∑ s ∈ t, d s) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert s t hs ih =>
    rw [Finset.prod_insert hs, Finset.sum_insert hs, Nat.mul_add, pow_add]
    exact Ideal.mul_mem_mul (pow_mul I j (d s) ▸ Ideal.pow_mem_pow (hmem s) (d s)) ih

/-- A monomial of total degree at least `c`, evaluated at arguments of `I ^ j`, lies in
`I ^ (c * j)`: it carries at least `c` of them. -/
private theorem prod_mem_pow_mul {j c : ℕ} (hmem : ∀ i, a i ∈ I ^ j) {d : σ →₀ ℕ}
    (hge : c ≤ d.degree) : d.prod (fun s e ↦ a s ^ e) ∈ I ^ (c * j) := by
  have hle : c * j ≤ j * d.degree := by
    calc c * j ≤ d.degree * j := by gcongr
      _ = j * d.degree := mul_comm _ _
  have hprod : d.prod (fun s e ↦ a s ^ e) ∈ I ^ (j * d.degree) := by
    have hdeg : d.degree = ∑ s ∈ d.support, d s := rfl
    rw [Finsupp.prod, hdeg]
    exact prod_mem_pow_mul_sum hmem d d.support
  exact SetLike.le_def.mp (Ideal.pow_le_pow_right hle) hprod

end Monomial

section Eval

variable {σ : Type*}
variable {R : Type*} [CommRing R] [UniformSpace R] [IsTopologicalSemiring R] [IsUniformAddGroup R]
variable {S : Type*} [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [CompleteSpace S]
    [T2Space S] [IsTopologicalRing S] [IsLinearTopology S S]
variable {φ : R →+* S} {a : σ → S} {I : Ideal S}

/-- **The value lies in `I ^ k` when the arguments do and `φ` sends the constant term there.**
Every monomial of positive degree already carries an argument, hence a factor from `I ^ k`; the
constant monomial is covered by the hypothesis on the image of the constant term. -/
theorem eval₂_mem_pow (hφ : Continuous φ) (ha : HasEval a) (hI : IsAdic I) {k : ℕ}
    (hmem : ∀ i, a i ∈ I ^ k) (f : MvPowerSeries σ R)
    (hcc : φ (constantCoeff f) ∈ I ^ k) :
    eval₂ φ a f ∈ I ^ k := by
  classical
  have htot := hasSum_eval₂ hφ ha f
  have hval : ∀ d : σ →₀ ℕ, φ (coeff d f) * d.prod (fun s e ↦ a s ^ e) ∈ I ^ k := by
    intro d
    rcases eq_or_ne d 0 with rfl | hd
    · simpa using hcc
    · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
      rw [Finsupp.prod, ← Finset.prod_erase_mul _ _ hi]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem _ (hmem i) _
          (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))))
  have hsum := tsum_mem (hI.isClosed_pow k) hval
  rwa [htot.tsum_eq] at hsum

/-- **Small coefficient images improve the bound.** If in addition `φ` sends every coefficient of
`f` into `I ^ k`, the two contributions multiply and the value lies in `I ^ (k + c * j)`. -/
theorem eval₂_mem_pow_add_mul (hφ : Continuous φ) (ha : HasEval a) (hI : IsAdic I) {j c k : ℕ}
    (hmem : ∀ i, a i ∈ I ^ j) (f : MvPowerSeries σ R)
    (hcoeff : ∀ d : σ →₀ ℕ, φ (coeff d f) ∈ I ^ k)
    (hlow : ∀ d : σ →₀ ℕ, d.degree < c → coeff d f = 0) :
    eval₂ φ a f ∈ I ^ (k + c * j) := by
  classical
  have htot := hasSum_eval₂ hφ ha f
  have hval : ∀ d : σ →₀ ℕ, φ (coeff d f) * d.prod (fun s e ↦ a s ^ e) ∈ I ^ (k + c * j) := by
    intro d
    rcases lt_or_ge d.degree c with hlt | hge
    · rw [hlow d hlt, map_zero, zero_mul]
      exact zero_mem _
    · rw [pow_add]
      exact Ideal.mul_mem_mul (hcoeff d) (prod_mem_pow_mul hmem hge)
  have hsum := tsum_mem (hI.isClosed_pow (k + c * j)) hval
  rwa [htot.tsum_eq] at hsum

/-- **A series vanishing below total degree `c`, evaluated at arguments of `I ^ j`, takes values
in `I ^ (c * j)`.** This is the `k = 0` case of `eval₂_mem_pow_add_mul`: every coefficient image
lies in `I ^ 0 = ⊤`, so that hypothesis is vacuous and the exponent collapses. -/
theorem eval₂_mem_pow_mul (hφ : Continuous φ) (ha : HasEval a) (hI : IsAdic I) {j c : ℕ}
    (hmem : ∀ i, a i ∈ I ^ j) (f : MvPowerSeries σ R)
    (hcoeff : ∀ d : σ →₀ ℕ, d.degree < c → coeff d f = 0) :
    eval₂ φ a f ∈ I ^ (c * j) := by
  simpa using eval₂_mem_pow_add_mul (k := 0) hφ ha hI hmem f (fun _ ↦ by simp) hcoeff

end Eval

end MvPowerSeries
