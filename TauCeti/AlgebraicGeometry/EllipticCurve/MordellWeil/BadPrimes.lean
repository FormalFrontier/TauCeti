/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Localization.Integral
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT
public import TauCeti.RingTheory.AdjoinRoot.Factors
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.DedekindDomain.SelmerGroup
import TauCeti.RingTheory.Valuation.RootMonic

/-!
# The bad primes of a Weierstrass curve, and the arithmetic away from them

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal
form over a field `K`, and let `R` be a Dedekind domain with fraction field `K`. The **bad
primes** of `W` over `R` are the primes dividing `2` or the discriminant `Δ`, together with those
occurring in a denominator of `a₂`, `a₄` or `a₆`. There are finitely many of them, and away from
them the Weierstrass equation is as well behaved as it can be: the coefficients are integral, the
root `θ` of `f` in a field factor `K[X] ⧸ (p)` of the étale algebra is integral, and — this is the
point of putting `Δ` in the set — the derivative `f' θ = 3θ² + 2a₂θ + a₄` is a *unit*.

That last statement is the arithmetic heart of Step 6 of the weak Mordell–Weil theorem. It is
proved by evaluating at `θ` the Bézout identity behind `separable_f`, which exhibits `Δ` as
`f' θ` times an explicit quadratic in `θ`. Both factors are integral at a good prime and their
product is a unit, so both are units.

Everything here is stated at a prime `w` of the ring of integers of a field factor that does not
lie above a bad prime of `R`. The estimates combine into `even_valuationOfNeZero_sub_root`: at
such a prime the valuation of `x - θ` is **even**, for `(x, y)` any point of `W` with `f x ≠ 0`.
That is the arithmetic content of Step 6 of the weak Mordell–Weil theorem with all the group
theory stripped away; `TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.SelmerGroupA` puts the
group theory back and reads it as membership in a Selmer group.

## Main definitions

* `WeierstrassCurve.Affine.badPrimes`: the set `S` of bad primes of `W` over `R`.
* `WeierstrassCurve.Affine.ringOfIntegersFactor`: the integral closure of `R` in the field factor
  `K[X] ⧸ (p)`, a Dedekind domain with fraction field `K[X] ⧸ (p)`.

## Main results

* `WeierstrassCurve.Affine.finite_badPrimes`: there are only finitely many bad primes.
* `WeierstrassCurve.Affine.valuation_root_le_one`: at a prime not above a bad prime, the root `θ`
  is integral.
* `WeierstrassCurve.Affine.valuation_deriv_root_eq_one`: at a prime not above a bad prime,
  `f' θ` is a unit. This is where `Δ` earns its place in `badPrimes`.
* `WeierstrassCurve.Affine.valuation_cofactor_eq_one`: at such a prime, if `x` is integral and
  `x - θ` is not a unit, then the cofactor of `x - θ` in the Weierstrass equation is a unit.
* `WeierstrassCurve.Affine.valuation_projFactor_torsion_eq_one`: at such a prime, the component
  of the corrected `2`-torsion representative `x - T + fCofactor x` is a unit.
* `WeierstrassCurve.Affine.even_valuationOfNeZero_sub_root`: at such a prime, the valuation of
  `x - θ` is even. This is the arithmetic core of Step 6.

## Implementation notes

The three `Valuation` lemmas about the monic cubic `t³ + at² + bt + c` are `private`. They are
specializations of `TauCeti.RingTheory.Valuation.RootMonic` to the shape of a Weierstrass
equation, used only to discharge coefficient hypotheses in this file and its sequel, so they are
proof plumbing rather than API. The general statements they specialize are the exported ones. This
is also why the `Core` section lives in this file rather than in `SelmerGroupA`: it is the last
consumer of those private helpers.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6 (Mordell–Weil), Step 6 of the weak
Mordell–Weil theorem: the image of the descent map lies in `A(S,2)`, where `S` is the set of bad
primes defined here.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/WeakMordellWeil.lean`, sections `Cubic`, `BadPrimes`, `RingOfIntegers` and
`Core`. The
source carries its own `HeightOneSpectrum.below`; at our Mathlib pin that map is
`HeightOneSpectrum.under`, which is used here instead. The source is written against Lean
`v4.32.0`; this is a forward port.
-/

public section

open Polynomial

section Cubic

-- `Nontrivial L` is what `compute_degree!` needs to know the leading coefficient `1` is nonzero,
-- i.e. that the cubic really has degree `3`.
variable {L Γ : Type*} [CommRing L] [Nontrivial L] [LinearOrderedCommGroupWithZero Γ]
  (ν : Valuation L Γ) {t a b c : L}

/-- The non-leading coefficients of `X³ + aX² + bX + c` are `a`, `b`, `c` (and zeros), so they
are integral as soon as `a`, `b`, `c` are. This is the coefficient hypothesis that
`RootMonic`'s general lemmas take. -/
private lemma cubic_coeff_le_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1) :
    ∀ i < (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree,
      ν ((X ^ 3 + C a * X ^ 2 + C b * X + C c).coeff i) ≤ 1 := by
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  intro i hi
  rw [hdeg] at hi
  interval_cases i <;> simp [ha, hb, hc]

/-- A monic cubic with integral coefficients, evaluated at an element of value `> 1`, is
dominated by its leading term. -/
private lemma Valuation.map_cubic_of_one_lt (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1)
    (ht : 1 < ν t) :
    ν (t ^ 3 + a * t ^ 2 + b * t + c) = ν t ^ 3 := by
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  have h := ν.map_eval_eq_of_one_lt hp (cubic_coeff_le_one ν ha hb hc) ht
  rw [hdeg] at h
  simpa using h

/-- A root of a monic cubic with integral coefficients is integral. -/
private lemma Valuation.le_one_of_root_cubic (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hc : ν c ≤ 1)
    (heq : t ^ 3 + a * t ^ 2 + b * t + c = 0) :
    ν t ≤ 1 := by
  have hp : (X ^ 3 + C a * X ^ 2 + C b * X + C c).Monic := by monicity!
  have hdeg : (X ^ 3 + C a * X ^ 2 + C b * X + C c).natDegree = 3 := by compute_degree!
  refine ν.le_one_of_root_monic hp (cubic_coeff_le_one ν ha hb hc) ?_
  simpa using heq

end Cubic

namespace WeierstrassCurve.Affine

open IsDedekindDomain

-- Step 6 needs neither `DecidableEq K` nor the group structure on points, so the variables are
-- declared afresh rather than inherited from the `x - T` map.
variable {K : Type*} [Field K] (W : Affine K)

/- Notation local to this file and its sequel: for a monic irreducible factor `p` of `f`,
`𝕃 p` is the field factor `K[X] ⧸ (p)` of `W.A`, `ι p : K →+* 𝕃 p` is the canonical embedding,
and `θ p` is the image of the root `T` of `f` in `𝕃 p`. -/
local notation:max "𝕃" p:max => AdjoinRoot (p : K[X])
local notation:max "ι" p:max => algebraMap K (AdjoinRoot (p : K[X]))
local notation:max "θ" p:max => AdjoinRoot.root (p : K[X])

/-- The set of **bad primes** of `R`: those dividing `2` or the discriminant of `W`, and those
occurring in a denominator of `a₂`, `a₄` or `a₆` (the latter three are the supports of the
coefficients in the sense of `IsDedekindDomain.HeightOneSpectrum.Support`). Away from these, the
`x - T` map lands in the `2`-Selmer group. -/
def badPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] :
    Set (HeightOneSpectrum R) :=
  {v | v.valuation K 2 ≠ 1} ∪ {v | v.valuation K W.Δ ≠ 1} ∪ HeightOneSpectrum.Support R W.a₂ ∪
    HeightOneSpectrum.Support R W.a₄ ∪ HeightOneSpectrum.Support R W.a₆

/-- There are only finitely many bad primes: `2` and `W.Δ` are nonzero, and the support of any
element of `K` is finite. -/
lemma finite_badPrimes (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
    [IsFractionRing R K] [W.IsElliptic] [W.IsCharNeTwoNF] : (W.badPrimes R).Finite :=
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (ringChar_ne_two W)
  ((((HeightOneSpectrum.finite_setOfPred_valuation_ne_one h2).union
    (HeightOneSpectrum.finite_setOfPred_valuation_ne_one W.isUnit_Δ.ne_zero)).union
      (HeightOneSpectrum.Support.finite R W.a₂)).union
        (HeightOneSpectrum.Support.finite R W.a₄)).union
          (HeightOneSpectrum.Support.finite R W.a₆)

section BadPrimes

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R}

/-- **Membership in `badPrimes`, as an arithmetic condition.** A prime is bad exactly when `2` or
`Δ` fails to be a unit there, or one of `a₂`, `a₄`, `a₆` fails to be integral there.

This is the characteristic lemma for `badPrimes`: the five projections below are read off from it,
and it is what a consumer should use rather than unfolding the nested unions in the definition. -/
@[simp]
lemma mem_badPrimes_iff :
    v ∈ W.badPrimes R ↔
      v.valuation K 2 ≠ 1 ∨ v.valuation K W.Δ ≠ 1 ∨ 1 < v.valuation K W.a₂ ∨
        1 < v.valuation K W.a₄ ∨ 1 < v.valuation K W.a₆ := by
  simp only [badPrimes, Set.mem_union, Set.mem_ofPred_eq, HeightOneSpectrum.Support]
  tauto

/-- The five good-prime conditions, packaged: at a prime that is not bad, `2` and `Δ` are units
and `a₂`, `a₄`, `a₆` are integral. -/
lemma notMem_badPrimes_iff :
    v ∉ W.badPrimes R ↔
      v.valuation K 2 = 1 ∧ v.valuation K W.Δ = 1 ∧ v.valuation K W.a₂ ≤ 1 ∧
        v.valuation K W.a₄ ≤ 1 ∧ v.valuation K W.a₆ ≤ 1 := by
  rw [W.mem_badPrimes_iff R]
  push Not
  rfl

/-- At a good prime, `a₂` is integral: a prime where it is not lies in its support, hence is
bad. -/
lemma valuation_a₂_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₂ ≤ 1 :=
  ((W.notMem_badPrimes_iff R).mp hv).2.2.1

/-- At a good prime, `a₄` is integral. -/
lemma valuation_a₄_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₄ ≤ 1 :=
  ((W.notMem_badPrimes_iff R).mp hv).2.2.2.1

/-- At a good prime, `a₆` is integral. -/
lemma valuation_a₆_le_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.a₆ ≤ 1 :=
  ((W.notMem_badPrimes_iff R).mp hv).2.2.2.2

/-- At a good prime, the discriminant is a unit. This is the half of `badPrimes` that makes the
reduction of `W` nonsingular there, and it is what `valuation_deriv_root_eq_one` consumes. -/
lemma valuation_Δ_eq_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K W.Δ = 1 :=
  ((W.notMem_badPrimes_iff R).mp hv).2.1

/-- At a good prime, `2` is a unit: the `2`-component of `badPrimes`, read off like the other four.

Nothing in these files consumes it. Step 6 needs `Δ` to be a unit and `a₂`, `a₄`, `a₆` to be
integral at a good prime, and never the valuation of `2`; it is recorded here so that the
projections out of `badPrimes` are complete. In the source this file is adapted from, its uses are
in the semilocal comparison (`EllipticCurves/SelmerGroup.lean`), a later rung of the descent. -/
lemma valuation_two_eq_one_of_notMem_badPrimes (hv : v ∉ W.badPrimes R) :
    v.valuation K 2 = 1 :=
  ((W.notMem_badPrimes_iff R).mp hv).1

end BadPrimes

section RingOfIntegers

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]

/-- The ring of integers of the field factor `K[X] ⧸ (p)` over `R`. -/
noncomputable abbrev ringOfIntegersFactor (p : W.f.Factors) : Type _ :=
  integralClosure R (𝕃 p)

/-- The ring of integers of a field factor is a Dedekind domain: it is the integral closure of
`R` in a finite separable extension of the fraction field `K`. -/
instance isDedekindDomain_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF]
    (p : W.f.Factors) : IsDedekindDomain (W.ringOfIntegersFactor R p) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isDedekindDomain R K (𝕃 p) _

/-- A field factor is the fraction field of its ring of integers. -/
instance isFractionRing_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF]
    (p : W.f.Factors) : IsFractionRing (W.ringOfIntegersFactor R p) (𝕃 p) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isFractionRing_of_finite_extension R K (𝕃 p) _

/-- The ring of integers of a field factor is torsion-free over `R`, as `R` embeds into it. -/
instance instIsTorsionFreeRingOfIntegersFactor (p : W.f.Factors) :
    Module.IsTorsionFree R (W.ringOfIntegersFactor R p) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  have hinj : Function.Injective (algebraMap R (𝕃 p)) := by
    rw [IsScalarTower.algebraMap_eq R K (𝕃 p)]
    exact (ι p).injective.comp (IsFractionRing.injective R K)
  exact fun a b hab ↦ hinj (congrArg Subtype.val hab)

/-- The `w`-adic valuation of an element of `K` is the valuation at the prime of `R` under `w`,
raised to the ramification index. -/
lemma valuation_algebraMap_eq [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)) (z : K) :
    (HeightOneSpectrum.under R w).valuation K z ^
        ((HeightOneSpectrum.under R w).asIdeal.ramificationIdx' w.asIdeal) =
      w.valuation (𝕃 p) (ι p z) :=
  HeightOneSpectrum.valuation_liesOver _ _ _ z

/-- If `z` is integral at the prime under `w`, then it is integral at `w`. -/
lemma valuation_algebraMap_le_one [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor R p)) {z : K}
    (hz : (HeightOneSpectrum.under R w).valuation K z ≤ 1) :
    w.valuation (𝕃 p) (ι p z) ≤ 1 := by
  rw [← W.valuation_algebraMap_eq R p w z]
  simpa using pow_le_pow_left' hz _

/-- A prime `w` not lying above a bad prime lies over a good prime of `R`. -/
lemma under_notMem_badPrimes [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
    {w : HeightOneSpectrum (W.ringOfIntegersFactor R p)}
    (hw : w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) (W.badPrimes R)) :
    HeightOneSpectrum.under R w ∉ W.badPrimes R :=
  fun hv ↦ hw ((HeightOneSpectrum.mem_primesAbove_iff R _ _ w).mpr hv)

/-- `θ` satisfies the Weierstrass cubic in the field factor `K[X] ⧸ (p)`. -/
lemma root_cubic_eq_zero (p : W.f.Factors) :
    θ p ^ 3 + ι p W.a₂ * θ p ^ 2 + ι p W.a₄ * θ p + ι p W.a₆ = 0 := by
  have hz : AdjoinRoot.mk (p : K[X]) W.f = 0 := AdjoinRoot.mk_eq_zero.mpr p.dvd
  simpa [f, AdjoinRoot.algebraMap_eq] using hz

/-- The cofactor `f / (X - x)`, computed in the field factor `K[X] ⧸ (p)`. -/
lemma mk_fCofactor_eq (p : W.f.Factors) (x : K) :
    AdjoinRoot.mk (p : K[X]) (W.fCofactor x) =
      θ p ^ 2 + (ι p x + ι p W.a₂) * θ p + (ι p x ^ 2 + ι p W.a₂ * ι p x + ι p W.a₄) := by
  simp only [fCofactor, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    ← AdjoinRoot.algebraMap_eq]

variable [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
  {w : HeightOneSpectrum (W.ringOfIntegersFactor R p)}

/-- At a prime `w` not above a bad prime, `a₂` is integral. -/
lemma valuation_a₂_le_one_of_notMem_primesAbove
    (hw : w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) (W.badPrimes R)) :
    w.valuation (𝕃 p) (ι p W.a₂) ≤ 1 :=
  W.valuation_algebraMap_le_one R p w
    (W.valuation_a₂_le_one_of_notMem_badPrimes R (W.under_notMem_badPrimes R p hw))

/-- At a prime `w` not above a bad prime, `a₄` is integral. -/
lemma valuation_a₄_le_one_of_notMem_primesAbove
    (hw : w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) (W.badPrimes R)) :
    w.valuation (𝕃 p) (ι p W.a₄) ≤ 1 :=
  W.valuation_algebraMap_le_one R p w
    (W.valuation_a₄_le_one_of_notMem_badPrimes R (W.under_notMem_badPrimes R p hw))

/-- At a prime `w` not above a bad prime, `a₆` is integral. -/
lemma valuation_a₆_le_one_of_notMem_primesAbove
    (hw : w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) (W.badPrimes R)) :
    w.valuation (𝕃 p) (ι p W.a₆) ≤ 1 :=
  W.valuation_algebraMap_le_one R p w
    (W.valuation_a₆_le_one_of_notMem_badPrimes R (W.under_notMem_badPrimes R p hw))

/-- At a prime `w` not above a bad prime, the root `θ` is integral: it satisfies the monic cubic
`f`, whose coefficients are integral at `w`. -/
lemma valuation_root_le_one
    (hw : w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) (W.badPrimes R)) :
    w.valuation (𝕃 p) (θ p) ≤ 1 :=
  Valuation.le_one_of_root_cubic _
    (W.valuation_a₂_le_one_of_notMem_primesAbove R p hw)
    (W.valuation_a₄_le_one_of_notMem_primesAbove R p hw)
    (W.valuation_a₆_le_one_of_notMem_primesAbove R p hw)
    (W.root_cubic_eq_zero p)

/-- An element of `K` with trivial valuation at the prime under `w` has trivial valuation
at `w`. -/
lemma valuation_algebraMap_eq_one {z : K}
    (hz : (HeightOneSpectrum.under R w).valuation K z = 1) :
    w.valuation (𝕃 p) (ι p z) = 1 := by
  rw [← W.valuation_algebraMap_eq R p w z, hz, one_pow]

/-- At a prime `w` not above a bad prime, `f' θ = 3θ² + 2a₂θ + a₄` is a unit.

This is where `Δ` earns its place in `badPrimes`: evaluating the Bézout identity behind
`separable_f` at `θ` gives `v(θ) * f' θ = Δ` for an explicit quadratic `v`. Both factors are
integral at `w` and the product is a unit, so both are units. -/
lemma valuation_deriv_root_eq_one
    (hw : w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) (W.badPrimes R)) :
    w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1 := by
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set A₂ := algebraMap K L W.a₂ with hA₂def
  set A := algebraMap K L W.a₄ with hAdef
  set B := algebraMap K L W.a₆ with hBdef
  have hA₂ : ν A₂ ≤ 1 := W.valuation_a₂_le_one_of_notMem_primesAbove R p hw
  have hA : ν A ≤ 1 := W.valuation_a₄_le_one_of_notMem_primesAbove R p hw
  have hB : ν B ≤ 1 := W.valuation_a₆_le_one_of_notMem_primesAbove R p hw
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p hw
  -- the Bézout identity, evaluated at `θ`
  have hΔ : algebraMap K L W.Δ = -64 * A₂ ^ 3 * B + 16 * A₂ ^ 2 * A ^ 2 - 64 * A ^ 3
      - 432 * B ^ 2 + 288 * A₂ * A * B := by
    rw [Δ_of_isCharNeTwoNF W]
    simp only [map_neg, map_sub, map_mul, map_add, map_pow, map_ofNat, hA₂def, hAdef, hBdef]
  have hid : (3 * t ^ 2 + 2 * A₂ * t + A) * ((32 * A₂ ^ 2 - 96 * A) * t ^ 2
        + (32 * A₂ ^ 3 - 112 * A₂ * A + 144 * B) * t
        + (16 * A₂ ^ 2 * A - 64 * A ^ 2 + 48 * A₂ * B)) =
      algebraMap K L W.Δ := by
    rw [hΔ]
    linear_combination (-(288 * A - 96 * A₂ ^ 2) * t - (240 * A₂ * A - 64 * A₂ ^ 3 - 432 * B)) *
      W.root_cubic_eq_zero p
  -- both factors are integral, and their product is a unit
  have hD : 3 * t ^ 2 + 2 * A₂ * t + A ∈ ν.integer :=
    add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem ht 2))
      (mul_mem (mul_mem (ofNat_mem _ 2) hA₂) ht)) hA
  have hC : (32 * A₂ ^ 2 - 96 * A) * t ^ 2 + (32 * A₂ ^ 3 - 112 * A₂ * A + 144 * B) * t
      + (16 * A₂ ^ 2 * A - 64 * A ^ 2 + 48 * A₂ * B) ∈ ν.integer := by
    refine add_mem (add_mem (mul_mem ?_ (pow_mem ht 2)) (mul_mem ?_ ht)) ?_
    · exact sub_mem (mul_mem (ofNat_mem _ 32) (pow_mem hA₂ 2)) (mul_mem (ofNat_mem _ 96) hA)
    · exact add_mem (sub_mem (mul_mem (ofNat_mem _ 32) (pow_mem hA₂ 3))
        (mul_mem (mul_mem (ofNat_mem _ 112) hA₂) hA)) (mul_mem (ofNat_mem _ 144) hB)
    · exact add_mem (sub_mem (mul_mem (mul_mem (ofNat_mem _ 16) (pow_mem hA₂ 2)) hA)
        (mul_mem (ofNat_mem _ 64) (pow_mem hA 2))) (mul_mem (mul_mem (ofNat_mem _ 48) hA₂) hB)
  refine ν.eq_one_of_mul_eq_one hD hC ?_
  rw [hid]
  exact W.valuation_algebraMap_eq_one R p
    (W.valuation_Δ_eq_one_of_notMem_badPrimes R (W.under_notMem_badPrimes R p hw))

/-- The cofactor of `x - θ` in the Weierstrass cubic, rewritten around the derivative: it differs
from `f' θ = 3θ² + 2a₂θ + a₄` by the multiple `(x - θ)(x + 2θ + a₂)`.

Both `valuation_cofactor_eq_one` and `valuation_projFactor_torsion_eq_one` turn on this single
identity — the first to see that the cofactor is a unit when `x - θ` is not, the second to see
that the two coincide when `x = θ`. It is stated in the shape `mk_fCofactor_eq` produces, so that
both call sites rewrite with it directly. -/
private lemma cofactor_eq_sub_mul_add_deriv {L : Type*} [CommRing L] (s t A₂ A : L) :
    t ^ 2 + (s + A₂) * t + (s ^ 2 + A₂ * s + A)
      = (s - t) * (s + 2 * t + A₂) + (3 * t ^ 2 + 2 * A₂ * t + A) := by
  ring

/-- At a prime `w` not above a bad prime, if `x` is `w`-integral and `x - θ` is not a `w`-unit,
then the cofactor `θ² + (x + a₂)θ + (x² + a₂x + a₄)` is a `w`-unit: modulo `x - θ` it equals
`f' θ`.

Stated in the shape `mk_fCofactor_eq` produces, so that it applies to the image of `fCofactor x`
in the field factor without reshaping. -/
lemma valuation_cofactor_eq_one {x : K}
    (hw : w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) (W.badPrimes R))
    (hx : w.valuation (𝕃 p) (ι p x) ≤ 1)
    (hlt : w.valuation (𝕃 p) (ι p x - θ p) < 1) :
    w.valuation (𝕃 p) (θ p ^ 2 + (ι p x + ι p W.a₂) * θ p
      + (ι p x ^ 2 + ι p W.a₂ * ι p x + ι p W.a₄)) = 1 := by
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set s := algebraMap K L x
  set A₂ := algebraMap K L W.a₂
  set A := algebraMap K L W.a₄
  have hA₂ : ν A₂ ≤ 1 := W.valuation_a₂_le_one_of_notMem_primesAbove R p hw
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p hw
  have hderiv : ν (3 * t ^ 2 + 2 * A₂ * t + A) = 1 := W.valuation_deriv_root_eq_one R p hw
  have h2t : s + 2 * t + A₂ ∈ ν.integer :=
    add_mem (add_mem hx (mul_mem (ofNat_mem _ 2) ht)) hA₂
  have hlt' : ν ((s - t) * (s + 2 * t + A₂)) < ν (3 * t ^ 2 + 2 * A₂ * t + A) := by
    rw [hderiv, map_mul]
    exact (mul_le_of_le_one_right' h2t).trans_lt hlt
  rw [cofactor_eq_sub_mul_add_deriv s t A₂ A, ν.map_add_eq_of_lt_right hlt', hderiv]

/-- If `x` is a root of `f`, then at a prime `w` not above a bad prime the `p`-component of the
`x - T` representative is a unit.

Both `x` and `θ` are roots of `f`, so `x - θ` times the cofactor is `0` and, `L` being a field,
one of the two factors vanishes. If `x = θ` the component is `f' θ`; if the cofactor vanishes the
component is `x - θ` and `f' θ = -(x - θ)(x + 2θ + a₂)`. Either way `valuation_deriv_root_eq_one`
makes it a unit. -/
lemma valuation_projFactor_torsion_eq_one {x : K} (hx : W.f.eval x = 0)
    (hw : w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) (W.badPrimes R)) :
    w.valuation (𝕃 p) (ι p x - θ p + AdjoinRoot.mk (p : K[X]) (W.fCofactor x)) = 1 := by
  rw [W.mk_fCofactor_eq p x]
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set s := algebraMap K L x with hsdef
  set A₂ := algebraMap K L W.a₂ with hA₂def
  set A := algebraMap K L W.a₄ with hAdef
  set B := algebraMap K L W.a₆ with hBdef
  have hA₂ : ν A₂ ≤ 1 := W.valuation_a₂_le_one_of_notMem_primesAbove R p hw
  have hA : ν A ≤ 1 := W.valuation_a₄_le_one_of_notMem_primesAbove R p hw
  have hB : ν B ≤ 1 := W.valuation_a₆_le_one_of_notMem_primesAbove R p hw
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p hw
  have hderiv : ν (3 * t ^ 2 + 2 * A₂ * t + A) = 1 := W.valuation_deriv_root_eq_one R p hw
  -- `x` is a root of the cubic too, hence integral at `w`
  have hs : s ^ 3 + A₂ * s ^ 2 + A * s + B = 0 := by
    rw [hsdef, hA₂def, hAdef, hBdef, ← W.map_eval_f, hx, map_zero]
  have hs1 : ν s ≤ 1 := ν.le_one_of_root_cubic hA₂ hA hB hs
  have hprod : (s - t) * (t ^ 2 + (s + A₂) * t + (s ^ 2 + A₂ * s + A)) = 0 := by
    linear_combination hs - W.root_cubic_eq_zero p
  rcases mul_eq_zero.mp hprod with h0 | h0
  · -- `x = θ`: the component is `f' θ`
    rw [h0, zero_add, cofactor_eq_sub_mul_add_deriv s t A₂ A, h0, zero_mul, zero_add, hderiv]
  · -- the cofactor vanishes: the component is `x - θ`, and `f' θ = -(x - θ)(x + 2θ + a₂)`
    rw [h0, add_zero]
    have hst : s - t ∈ ν.integer := sub_mem hs1 ht
    have h2t : s + 2 * t + A₂ ∈ ν.integer :=
      add_mem (add_mem hs1 (mul_mem (ofNat_mem _ 2) ht)) hA₂
    -- the same identity again: with the cofactor `0`, it reads `(x - θ)(x + 2θ + a₂) = -f' θ`
    have hneg : (s - t) * (s + 2 * t + A₂) = -(3 * t ^ 2 + 2 * A₂ * t + A) := by
      linear_combination h0
    exact ν.eq_one_of_mul_eq_one hst h2t (by rw [hneg, Valuation.map_neg, hderiv])

end RingOfIntegers

section Core

variable [W.IsElliptic] [W.IsCharNeTwoNF]
  (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (p : W.f.Factors)
  {x y : K} (h : W.Equation x y) (hx : W.f.eval x ≠ 0)
  (u : (AdjoinRoot (p : K[X]))ˣ)
  (hu : (u : AdjoinRoot (p : K[X])) =
    algebraMap K (AdjoinRoot (p : K[X])) x - AdjoinRoot.root (p : K[X]))
  (w : HeightOneSpectrum (W.ringOfIntegersFactor R p))
  (hw : w ∉ HeightOneSpectrum.primesAbove R (W.ringOfIntegersFactor R p) (W.badPrimes R))

include h hx hu hw

/-- Non-integral case: `x` has a pole at the prime of `R` under `w`.

The coefficients `a₂`, `a₄`, `a₆` and the root `θ` are `w`-integral, so `1 < ν x` makes the
leading term of the cubic dominate: `ν (f x) = ν x ³`, hence `ν y ² = ν x ³`. Also `ν θ ≤ 1 < ν x`
gives `ν (x - θ) = ν x`. Therefore `ν (x - θ) = ν (y / x) ²` is an even power. -/
private lemma even_valuationOfNeZero_sub_root_of_one_lt
    (hx' : 1 < w.valuation (𝕃 p) (ι p x)) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  set L := 𝕃 p
  set ν := w.valuation L
  have hx0 : algebraMap K L x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx'
    exact absurd hx' (by simp)
  have hx0' : ν (algebraMap K L x) ≠ 0 := ν.ne_zero_iff.mpr hx0
  have hy0 : algebraMap K L y ≠ 0 := (_root_.map_ne_zero _).mpr (W.y_ne_zero_of_eval_f_ne_zero h hx)
  -- the Weierstrass equation, transported to `L`
  have heq : (algebraMap K L y) ^ 2 = algebraMap K L x ^ 3 +
      algebraMap K L W.a₂ * algebraMap K L x ^ 2 +
      algebraMap K L W.a₄ * algebraMap K L x + algebraMap K L W.a₆ := by
    rw [← W.map_eval_f, (equation_iff_eval_f_eq_sq W x y).mp h, map_pow]
  have hval : ν (algebraMap K L y) ^ 2 = ν (algebraMap K L x) ^ 3 := by
    rw [← map_pow, heq, ν.map_cubic_of_one_lt (W.valuation_a₂_le_one_of_notMem_primesAbove R p hw)
      (W.valuation_a₄_le_one_of_notMem_primesAbove R p hw)
      (W.valuation_a₆_le_one_of_notMem_primesAbove R p hw) hx']
  -- `ν (x - θ) = ν x`, since `θ` is integral and `x` is not
  have hu' : ν (u : L) = ν (algebraMap K L x) := by
    rw [hu]
    exact Valuation.map_sub_eq_of_lt_left _ ((W.valuation_root_le_one R p hw).trans_lt hx')
  have hkey : ν (u : L) = ν ((Units.mk0 _ (div_ne_zero hy0 hx0) : Lˣ) : L) ^ 2 := by
    rw [hu', Units.val_mk0, map_div₀, div_pow, hval, eq_div_iff (pow_ne_zero 2 hx0'), mul_comm]
    exact (pow_succ _ 2).symm
  simpa using w.dvd_toAdd_valuationOfNeZero hkey

/-- Integral case: `x` is integral at the prime of `R` under `w`.

Over `L` the Weierstrass equation factors as `y ² = (x - θ) * c` with cofactor
`c = x ² + θ x + θ ² + a₂ (x + θ) + a₄`. If `x - θ` is a `w`-unit there is nothing to do.
Otherwise `ν (x - θ) < 1`, and since `c = (x - θ) * (x + 2 θ + a₂) + f' θ` with `f' θ` a `w`-unit,
the cofactor is a `w`-unit. Hence `ν (x - θ) = ν y ²` is an even power. -/
private lemma even_valuationOfNeZero_sub_root_of_le_one
    (hx' : w.valuation (𝕃 p) (ι p x) ≤ 1) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  set L := 𝕃 p
  set ν := w.valuation L
  set t := θ p
  set A₂ := algebraMap K L W.a₂ with hA₂def
  set A := algebraMap K L W.a₄ with hAdef
  have ht : ν t ≤ 1 := W.valuation_root_le_one R p hw
  have hderiv : ν (3 * t ^ 2 + 2 * A₂ * t + A) = 1 := W.valuation_deriv_root_eq_one R p hw
  -- `y ² = (x - θ) * (x ² + θ x + θ ² + a₂ (x + θ) + a₄)` over `L`
  have heqL : (algebraMap K L y) ^ 2 = algebraMap K L x ^ 3 + A₂ * algebraMap K L x ^ 2 +
      A * algebraMap K L x + algebraMap K L W.a₆ := by
    rw [hA₂def, hAdef, ← W.map_eval_f, (equation_iff_eval_f_eq_sq W x y).mp h, map_pow]
  have hfac : (u : L) * (t ^ 2 + (algebraMap K L x + A₂) * t
        + (algebraMap K L x ^ 2 + A₂ * algebraMap K L x + A)) =
      (algebraMap K L y) ^ 2 := by
    rw [hu]
    linear_combination -W.root_cubic_eq_zero p - heqL
  have hu1 : ν (u : L) ≤ 1 := by rw [hu]; exact ν.map_sub_le hx' ht
  by_cases hlt : ν (u : L) = 1
  · -- `x - θ` is a unit, so its valuation is trivially even
    have hkey : ν (u : L) = ν ((1 : Lˣ) : L) ^ 2 := by rw [Units.val_one, map_one, one_pow, hlt]
    simpa using w.dvd_toAdd_valuationOfNeZero hkey
  -- otherwise `w` divides `x - θ`, and then it cannot divide the cofactor
  replace hlt : ν (u : L) < 1 := lt_of_le_of_ne hu1 hlt
  rw [hu] at hlt
  have hcof : ν (t ^ 2 + (algebraMap K L x + A₂) * t
      + (algebraMap K L x ^ 2 + A₂ * algebraMap K L x + A)) = 1 :=
    W.valuation_cofactor_eq_one R p hw hx' hlt
  have hy0 : algebraMap K L y ≠ 0 := (_root_.map_ne_zero _).mpr (W.y_ne_zero_of_eval_f_ne_zero h hx)
  have hkey : ν (u : L) = ν ((Units.mk0 _ hy0 : Lˣ) : L) ^ 2 := by
    rw [Units.val_mk0, ← map_pow, ← hfac, map_mul, hcof, mul_one]
  simpa using w.dvd_toAdd_valuationOfNeZero hkey

/-- The arithmetic core of Step 6, generic case, with all the group theory stripped away: for
`(x, y)` on `W` with `f x ≠ 0`, and `w` a prime of the ring of integers of the field factor
`K[X] ⧸ (p)` not lying above a bad prime, the `w`-adic valuation of `x - θ` is even.

The proof splits on whether `x` has a pole at the prime of `R` under `w`. -/
lemma even_valuationOfNeZero_sub_root :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero u) := by
  by_cases hx' : 1 < w.valuation (𝕃 p) (ι p x)
  · exact W.even_valuationOfNeZero_sub_root_of_one_lt R p h hx u hu w hw hx'
  · exact W.even_valuationOfNeZero_sub_root_of_le_one R p h hx u hu w hw (not_lt.mp hx')

end Core

end WeierstrassCurve.Affine

end
