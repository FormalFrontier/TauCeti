/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
-- Proof-only: the integral basis of a finite extension of the fraction field.
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
-- Proof-only: polynomial rings over a field are Noetherian UFDs, hence integrally closed.
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
-- Proof-only: the five Tau Ceti prerequisites — the `expand`/`map` ring maps on polynomial
-- rings, root adjunction, the purely inseparable embedding criterion, and integral-closure
-- transfer. No statement below mentions them, so none is re-exported.
import TauCeti.RingTheory.MvPolynomial.Basic
import TauCeti.RingTheory.MvPolynomial.Expand
import TauCeti.FieldTheory.IntermediateField.Adjoin.Roots
import TauCeti.FieldTheory.PurelyInseparable.Embedding
import TauCeti.RingTheory.IntegralClosure.Transfer

/-!
# The integral closure of a polynomial ring in a purely inseparable extension is finite

Let `k` be a field, `P = k[X_1, …, X_r]`, `K` its fraction field and `M / K` a finite purely
inseparable extension of exponent `e`, `q = p ^ e`. The integral closure of `P` in `M` is a finite
`P`-module. This is the purely inseparable half of normalization-finiteness, the only part that
is genuinely absent from Mathlib (whose `IsIntegralClosure.finite` argues through the trace form
and needs separability), and it is Stacks, Lemma 10.161.13 (tag 032O) run once for `r` variables
over a field.

The argument. Pick a `K`-basis `m_j` of `M` inside the integral closure. Each `m_j ^ q` lies in
`K` and is integral over `P`, hence lies in `P` (`P` is a UFD). Let `k' / k` be a finite
extension containing `q`-th roots of the finitely many coefficients of the `m_j ^ q`, and let
`P' = k'[X_1, …, X_r]` be a `P`-algebra through `X_i ↦ X_i ^ q`. Then `P'` is a finite `P`-module,
integrally closed with fraction field `K'`, and `M` embeds over `K` into `K'` because the `q`-th
powers of the `m_j` become `q`-th powers there. So the integral closure of `P` in `M` maps
injectively and `P`-linearly into the integral closure of `P` in `K'`, which is `P'`, and a
submodule of a finite module over a Noetherian ring is finite.

## Main results

* `IsIntegral.exists_algebraMap_eq_iterateFrobenius`: the `q`-th power of an element
  integral over the (integrally closed) base ring lies in that ring.
* `TauCeti.IsIntegralClosure.finite_of_forall_exists_pow_eq`: the abstract assembly — an
  integral closure in a purely inseparable extension is finite as soon as some overring finite
  over the base, and an integral closure of it in a larger field, absorbs the `q`-th powers of a
  generating set.
* `TauCeti.IsIntegralClosure.finite_mvPolynomial_of_isPurelyInseparable`: the theorem for
  polynomial rings over a field.

## Provenance

Roadmap: EllipticCurves, the Layers 0-1 target *Function-field foundations and isogenies*
(`TauCetiRoadmap/EllipticCurves/README.md:1096`), through the support module
`RingTheory/IntegralClosure/NormalizationFinite`. The mathematics is the second paragraph of the
proof of Stacks, Lemma 10.161.13 (tag 032O), with its "some details omitted" spelled out.
-/

public section

namespace TauCeti

universe u

/-- Source: Stacks, Lemma 10.161.13 (tag 032O), proof: "And this integral closure is equal to
`R′[x^{1/q}]`" — the elementwise input: for `x` integral over an integrally closed domain `A`,
lying in a purely inseparable extension `M` of its fraction field `K`, the `p ^ n`-th power
`x ^ (p ^ n)` lies in `K` and is integral over `A`, hence comes from `A`. -/
theorem _root_.IsIntegral.exists_algebraMap_eq_iterateFrobenius {A K M : Type*} [CommRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [Field M] [Algebra K M]
    [Algebra A M] [IsScalarTower A K M] [IsPurelyInseparable.HasExponent K M]
    (p : ℕ) [ExpChar K p] {n : ℕ} (hn : IsPurelyInseparable.exponent K M ≤ n) {x : M}
    (hx : IsIntegral A x) :
    ∃ a : A, algebraMap A K a = IsPurelyInseparable.iterateFrobenius K M p hn x := by
  -- `A` is integrally closed, so it suffices that the value is integral over `A` — and that is
  -- read off in `M`, where the value becomes the `p ^ n`-th power of an element integral over `A`.
  refine IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.tower_bot (algebraMap K M).injective ?_)
  rw [IsPurelyInseparable.algebraMap_iterateFrobenius]
  exact hx.pow _

/-- Source: Stacks, Lemma 10.161.13 (tag 032O), proof: "As `R[x]` is Noetherian it suffices to
show that the integral closure of `R[x]` in `L′(x^{1/q})` is finite over `R[x]`. And this
integral closure is equal to `R′[x^{1/q}]` … finite over `R[x]`." The abstract assembly. Let `C`
be the integral closure of a Noetherian ring `A` in a purely inseparable extension `M` of a field
`K` over `A`, of exponent at most `n`. (In the application `K` is the fraction field of `A`; the
argument only uses the tower `A → K → M`, so that is not assumed.) Let `A'` be an integral
closure of `A` in a field `K'` over `K`, finite over `A`, such that for a generating set `s` of
`M` over `K` the `p ^ n`-th power of each `x ∈ s` (an element of `K`) becomes a `p ^ n`-th power
of an element of `A'` in `K'`. Then `M` embeds into `K'` over `K`, and `C` is a finite
`A`-module. -/
theorem IsIntegralClosure.finite_of_forall_exists_pow_eq (A K M C A' K' : Type*) [CommRing A]
    [IsNoetherianRing A] [Field K] [Field M] [Algebra A K] [Algebra K M]
    [Algebra A M] [IsScalarTower A K M] [CommRing C] [Algebra A C] [Algebra C M]
    [IsScalarTower A C M] [IsIntegralClosure C A M] [CommRing A'] [Field K'] [Algebra A A']
    [Module.Finite A A'] [Algebra A' K'] [Algebra A K'] [Algebra K K'] [IsScalarTower A A' K']
    [IsScalarTower A K K'] [IsIntegralClosure A' A K']
    [IsPurelyInseparable.HasExponent K M] (p : ℕ) [ExpChar K p] {n : ℕ}
    (hn : IsPurelyInseparable.exponent K M ≤ n) {s : Set M}
    (hs : IntermediateField.adjoin K s = ⊤)
    (h : ∀ x ∈ s, ∃ y : A', algebraMap A' K' y ^ p ^ n =
      algebraMap K K' (IsPurelyInseparable.iterateFrobenius K M p hn x)) :
    Module.Finite A C := by
  -- (i) the root hypothesis embeds `M` into `K'` over `K` (leaf B2)
  obtain ⟨ι⟩ := IsPurelyInseparable.nonempty_algHom_of_forall_exists_pow_eq K M p hn K' hs
    fun x hx ↦ ((h x hx).elim fun y hy ↦ ⟨algebraMap A' K' y, hy⟩)
  -- (ii) finiteness then descends along that embedding, `A'` being the integral closure of `A`
  -- in `K'` by hypothesis (leaf T2)
  exact IsIntegralClosure.finite_of_injective (C' := A') (ι.restrictScalars A)
    (ι.restrictScalars A).toRingHom.injective

/-! ### Steps of the polynomial-ring case

The lemmas below are the instance-free steps of
`IsIntegralClosure.finite_mvPolynomial_of_isPurelyInseparable`, split out to keep that proof
readable. Its `Algebra`/`IsScalarTower` plumbing is deliberately *not* split out: building those
instances away from their use site creates diamonds against
`OreLocalization.instSMulOfIsScalarTower`. -/

/-- A `K`-basis of `M` consisting of elements integral over `A`, together with the preimages in
`A` of the `p ^ n`-th powers of its vectors. This is Mathlib's integral basis fed through
`IsIntegral.exists_algebraMap_eq_iterateFrobenius` one vector at a time. -/
private theorem exists_basis_iterateFrobenius_eq_algebraMap (A K M : Type*) [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [Field M]
    [Algebra K M] [Algebra A M] [IsScalarTower A K M] [FiniteDimensional K M]
    [IsPurelyInseparable.HasExponent K M] (p : ℕ) [ExpChar K p] {n : ℕ}
    (hn : IsPurelyInseparable.exponent K M ≤ n) :
    ∃ (sb : Finset M) (b : Module.Basis sb K M) (g : sb → A), ∀ j,
      algebraMap A K (g j) = IsPurelyInseparable.iterateFrobenius K M p hn (b j) := by
  obtain ⟨sb, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K M
  choose g hgg using fun j ↦ (hb j).exists_algebraMap_eq_iterateFrobenius p hn
  exact ⟨sb, b, g, hgg⟩

/-- A finite extension of `k` in which every coefficient of each of the finitely many polynomials
`g j` has an `m`-th root. This is `exists_finiteDimensional_forall_exists_pow_eq` applied to the
union of their coefficient sets; keeping the `Finset` bookkeeping here lets the caller pass the
root hypothesis on to `MvPolynomial.exists_pow_eq_map_expand` unchanged. -/
private theorem exists_finiteDimensional_forall_coeff_exists_pow_eq {k : Type u} [Field k]
    {σ ι : Type*} [Finite ι] (g : ι → MvPolynomial σ k) {m : ℕ} (hm : 0 < m) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      ∀ j, ∀ d ∈ (g j).support, ∃ y : k', y ^ m = algebraMap k k' ((g j).coeff d) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨k', _, _, hfin, hroot⟩ := exists_finiteDimensional_forall_exists_pow_eq k
    (Finset.univ.biUnion fun j ↦ (g j).support.image fun d ↦ (g j).coeff d) hm
  exact ⟨k', inferInstance, inferInstance, hfin, fun j d hd ↦ hroot _
    (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩)⟩

/-- Adjoining a `K`-basis of `M` to `K` gives all of `M`: the basis already spans, and `adjoin`
contains the span. -/
private theorem adjoin_range_eq_top_of_basis {K M ι : Type*} [Field K] [Field M] [Algebra K M]
    (b : Module.Basis ι K M) : IntermediateField.adjoin K (Set.range b) = ⊤ :=
  eq_top_iff.mpr fun x _ ↦
    (Submodule.span_le (p := (IntermediateField.adjoin K (Set.range b)).toSubmodule)).mpr
      (IntermediateField.subset_adjoin K _) (b.mem_span x)

/-- Source: Stacks, Lemma 10.161.13 (tag 032O): "If `R` is N-2 then `R[x]` is N-2", second
paragraph of the proof, for `R = k` a field and `r` variables at once. **The purely inseparable
core of normalization-finiteness.** For `P = k[X_1, …, X_r]` with fraction field `K` and a finite
purely inseparable extension `M / K`, any integral closure `C` of `P` in `M` is a finite
`P`-module. No separability is assumed; characteristic zero is the case `q = 1`. -/
theorem IsIntegralClosure.finite_mvPolynomial_of_isPurelyInseparable (k : Type*) [Field k]
    {σ : Type*} [Finite σ] (K M : Type*) [Field K] [Field M] [Algebra (MvPolynomial σ k) K]
    [IsFractionRing (MvPolynomial σ k) K] [Algebra K M] [Algebra (MvPolynomial σ k) M]
    [IsScalarTower (MvPolynomial σ k) K M] [IsPurelyInseparable K M] [FiniteDimensional K M]
    (C : Type*) [CommRing C] [Algebra (MvPolynomial σ k) C] [Algebra C M]
    [IsScalarTower (MvPolynomial σ k) C M] [IsIntegralClosure C (MvPolynomial σ k) M] :
    Module.Finite (MvPolynomial σ k) C := by
  classical
  obtain ⟨p, _⟩ := ExpChar.exists k
  -- `Algebra k K` is NOT an instance (Lean does not compose algebra maps), so the exponential
  -- characteristic is transported along `k → MvPolynomial σ k → K` in two steps instead.
  have _ : ExpChar K p := expChar_of_injective_algebraMap
    (IsFractionRing.injective (MvPolynomial σ k) K) p
  set n := IsPurelyInseparable.exponent K M
  -- a `K`-basis of `M` integral over `P`, and (D1) the preimages in `P` of the `p ^ n`-th powers
  obtain ⟨sb, b, g, hgg⟩ :=
    exists_basis_iterateFrobenius_eq_algebraMap (MvPolynomial σ k) K M p (le_refl n)
  -- B1: a finite extension of `k` holding `p ^ n`-th roots of the coefficients of the `g j`
  obtain ⟨k', _, _, hk'fin, hk'root⟩ :=
    exists_finiteDimensional_forall_coeff_exists_pow_eq g (pow_pos (expChar_pos k p) n)
  have _ : ExpChar k' p := expChar_of_injective_algebraMap (algebraMap k k').injective p
  -- the coefficient extension `P → P'`, injective and finite
  set f : MvPolynomial σ k →+* MvPolynomial σ k' :=
    (MvPolynomial.map (algebraMap k k')).comp
      (MvPolynomial.expand (σ := σ) (R := k) (p ^ n)).toRingHom
  have hfinj : Function.Injective f :=
    (MvPolynomial.map_injective _ (algebraMap k k').injective).comp
      (MvPolynomial.expand_injective (pow_pos (expChar_pos k p) n))
  have hffin : f.Finite :=
    RingHom.Finite.comp (MvPolynomial.finite_map (RingHom.finite_algebraMap.mpr hk'fin))
      (MvPolynomial.finite_expand (pow_pos (expChar_pos k p) n))
  -- make `P'` a finite `P`-algebra, and `K' := Frac P'` a `P`-algebra through it
  let _ : Algebra (MvPolynomial σ k) (MvPolynomial σ k') := f.toAlgebra
  have : Module.Finite (MvPolynomial σ k) (MvPolynomial σ k') := hffin
  -- `Algebra P (Frac P')` and its scalar tower are NOT built by hand: `FractionRing` is an
  -- `OreLocalization`, which already derives them from `Algebra P P'`. Introducing them manually
  -- creates a diamond against `OreLocalization.instSMulOfIsScalarTower`.
  have hPK' : Function.Injective
      (algebraMap (MvPolynomial σ k) (FractionRing (MvPolynomial σ k'))) :=
    (IsFractionRing.injective (MvPolynomial σ k') _).comp hfinj
  -- `K` is an ABSTRACT fraction field of `P`, so the map to `K'` is `IsFractionRing.lift`, not
  -- `FractionRing.liftAlgebra`: no diamond arises because `K` is not `FractionRing P`.
  let _ : Algebra K (FractionRing (MvPolynomial σ k')) := (IsFractionRing.lift hPK').toAlgebra
  have : IsScalarTower (MvPolynomial σ k) K (FractionRing (MvPolynomial σ k')) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (IsFractionRing.lift_algebraMap hPK' x).symm
  refine IsIntegralClosure.finite_of_forall_exists_pow_eq (MvPolynomial σ k) K M C
    (MvPolynomial σ k') (FractionRing (MvPolynomial σ k')) p (le_refl n)
    (s := Set.range b) ?_ ?_
  · exact adjoin_range_eq_top_of_basis b
  · -- the root hypothesis, from A5 applied to `g j`
    rintro _ ⟨j, rfl⟩
    obtain ⟨y, hy⟩ := MvPolynomial.exists_pow_eq_map_expand (algebraMap k k') p n
      (g := g j) (hk'root j)
    refine ⟨y, ?_⟩
    rw [← map_pow, hy]
    have hfg : MvPolynomial.map (algebraMap k k') (MvPolynomial.expand (p ^ n) (g j))
        = algebraMap (MvPolynomial σ k) (MvPolynomial σ k') (g j) := by
      rw [RingHom.algebraMap_toAlgebra]
      rfl
    rw [hfg, ← IsScalarTower.algebraMap_apply, ← hgg j, ← IsScalarTower.algebraMap_apply]

end TauCeti
