/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
public import TauCeti.RingTheory.DedekindDomain.Ideal
public import TauCeti.RingTheory.DedekindDomain.ValuationOfNeZero

/-!
# Extension of adic completions along an extension of Dedekind domains

Let `R` be a Dedekind domain with fraction field `K`, let `L/K` be an extension and `B` a
Dedekind domain with fraction field `L` extending `R`, and let `w` be a height-one prime of `B`
lying over the height-one prime `v` of `R`. Completing at `v` and at `w` gives fields `K_v` and
`L_w`, and the inclusion `K → L` extends continuously to a ring homomorphism `K_v →+* L_w`.

This file constructs that homomorphism, `adicCompletionExtension`, records that the valuation of
`L_w` restricted along it is the valuation of `K_v` raised to the ramification index, restricts it
to the rings of integers as `adicCompletionIntegersExtension`, and shows that the maximal ideal
contracts to the maximal ideal. It also identifies the valuation attached to the maximal ideal of
`𝒪_v` — a discrete valuation ring — with the valuation of the completion itself, which is what
lets a statement about height-one primes of `𝒪_v` be read as a statement about `K_v`.

This is the local-to-global bridge of the explicit `2`-descent: comparing a square class of a
global étale algebra with its images in the completions passes through exactly these maps.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.adicCompletionExtension`: the induced ring homomorphism
  `K_v →+* L_w`.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersExtension`: its restriction
  `𝒪_v →+* 𝒪_w` to the rings of integers.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.valuation_maximalIdeal_adicCompletionIntegers`: the
  valuation attached to the maximal ideal of `𝒪_v` is the valuation of `K_v`.
* `IsDedekindDomain.HeightOneSpectrum.valuation_adicCompletionIntegers`: the same identification
  at an arbitrary height-one prime of `𝒪_v`, for every element of `K_v`.
* `IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_maximalIdeal_adicCompletionIntegers` and
  `IsDedekindDomain.HeightOneSpectrum.valuation_adicCompletion_algebraMap`: the two restrictions
  of it the square-class conditions of the `2`-descent are stated in — on units of `K`, and on the
  image of `K`.
* `IsDedekindDomain.HeightOneSpectrum.valued_adicCompletionExtension`: along the extension the
  valuation is raised to the ramification index.
* `IsDedekindDomain.HeightOneSpectrum.comap_maximalIdeal_adicCompletionIntegersExtension`: the
  maximal ideal of `𝒪_w` contracts to the maximal ideal of `𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.continuous_adicCompletionExtension` and
  `IsDedekindDomain.HeightOneSpectrum.eq_adicCompletionExtension_of_continuous`: the extension is
  continuous, and is the only continuous ring homomorphism `K_v →+* L_w` extending `K → L`. Together
  these are its universal property, usable without unfolding the definition.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, Layer 6, lines 813–822: the "Explicit 2-descent (core,
this layer)" bullet. The semilocal comparison behind it — matching the unramifiedness of a square
class at the primes of the field factors with unramifiedness over the valuation ring of `K_v` —
consumes every result here. Nothing in this file mentions a curve.

## Provenance

Adapted, with the authors' proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/Mathlib/AdicCompletionExtension.lean`.

That file in turn credits the FLT project
(`github.com/ImperialCollegeLondon/FLT`, `FLT/DedekindDomain/Completion/BaseChange.lean`, by
Kevin Buzzard, Andrew Yang and Matthew Jasper) for the completion-extension material, rebased
there onto Mathlib's `valuation_liesOver` and `uniformContinuous_algebraMap_liesOver`; the same
rebasing is used here, so both are credited.

The three completion-integers results — `span_singleton_eq_maximalIdeal_pow`,
`exists_valued_sub_lt_one` and `residueFieldEquivAdicCompletionIntegers` — come from that same
Stoll file; they are the substrate its residue-field comparison rests on, restated here against
this repository's `HeightOneSpectrum` interface.

Only the part the `2`-descent consumes is ported: the Henselian and completeness chain of the
source, which serves other consumers, is deliberately left out. The source is written against Lean
`v4.32.0`; this is a forward port.

## Implementation notes

`Mathlib.NumberTheory.NumberField.Completion.FinitePlace` is the sole Mathlib import. It is needed
for two instances — `IsDiscreteValuationRing (v.adicCompletionIntegers K)` and
`(Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsRankOneDiscrete`. Both are stated there for an
arbitrary Dedekind domain and its fraction field, not for number fields, so nothing in this file
depends on number-field theory; they simply live in that module upstream. This note records the
reason so the placement of a `NumberTheory` import inside `RingTheory` is not mistaken for a
layering slip.

It also transitively supplies the ramification-valuation and adic-valuation modules, so those are
not imported directly.
-/

public section

open IsDedekindDomain WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- An irreducible element of the ring of integers of a completion has valuation `exp (-1)`. -/
theorem valued_algebraMap_eq_exp_neg_one_of_irreducible {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) = exp (-1) := by
  -- `v.adicCompletionIntegers K` is by definition `Valued.v.valuationSubring`, which is what lets
  -- `π`'s maximal ideal be retyped as an ideal of the valuation subring here.
  have hgen : IsLocalRing.maximalIdeal (Valued.v : Valuation (v.adicCompletion K)
      ℤᵐ⁰).valuationSubring = Ideal.span {π} := hπ.maximalIdeal_eq
  have huni := Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) hgen
  rwa [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective K)] at huni

/-- The valuation associated to the maximal ideal of the ring of integers of an adic completion is
the valuation of the completion.

This is what lets a condition stated at the height-one primes of `𝒪_v` be read as a condition on
`K_v`: `𝒪_v` is a discrete valuation ring, so it has exactly one, and it induces `Valued.v`.

Not `@[simp]`: this is the special case `P = IsDiscreteValuationRing.maximalIdeal _` of
`valuation_adicCompletionIntegers`, which carries the annotation instead. With both marked, the
`simpNF` linter rejects this one — "simp can prove this" — because the general form subsumes it. -/
theorem valuation_maximalIdeal_adicCompletionIntegers (x : v.adicCompletion K) :
    (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers K)).valuation
      (v.adicCompletion K) x = Valued.v x := by
  -- reduce to elements of the ring of integers
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := v.adicCompletionIntegers K) x
  rw [map_div₀, map_div₀]
  suffices h : ∀ y : v.adicCompletionIntegers K,
      (IsDiscreteValuationRing.maximalIdeal (v.adicCompletionIntegers K)).valuation
        (v.adicCompletion K) (algebraMap _ _ y) = Valued.v (algebraMap _ _ y) by
    rw [h, h]
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  -- decompose `y` as a unit times a power of a uniformizer
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ
  rw [valuation_of_algebraMap]
  have hu1 : (IsDiscreteValuationRing.maximalIdeal
      (v.adicCompletionIntegers K)).intValuation (u : v.adicCompletionIntegers K) = 1 := by
    simp [IsDiscreteValuationRing.maximalIdeal]
  have hu2 : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (u : v.adicCompletionIntegers K)) = 1 :=
    (adicCompletionIntegers.integers K v).valuation_unit u
  have hπ1 : (IsDiscreteValuationRing.maximalIdeal
      (v.adicCompletionIntegers K)).intValuation π = exp (-1) :=
    (IsDiscreteValuationRing.maximalIdeal _).intValuation_singleton hπ.ne_zero
      hπ.maximalIdeal_eq
  have hπ2 : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) =
      exp (-1) := v.valued_algebraMap_eq_exp_neg_one_of_irreducible hπ
  simp only [map_mul, map_pow]
  rw [hu1, hu2, hπ1, hπ2]

/-- The valuation of the height-one prime of `𝒪_v` at the image of a unit of `K` is the `v`-adic
valuation of that unit. This is the form the square-class conditions of the `2`-descent are
stated in. -/
theorem valuationOfNeZero_maximalIdeal_adicCompletionIntegers (u : Kˣ) :
    (IsDiscreteValuationRing.maximalIdeal
        (v.adicCompletionIntegers K)).valuationOfNeZero
      (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u) =
      v.valuationOfNeZero u := by
  rw [valuationOfNeZero_eq_iff, valuationOfNeZero_eq,
    valuation_maximalIdeal_adicCompletionIntegers]
  exact v.valuedAdicCompletion_eq_valuation' _

/-- Any height-one prime `P` of the valuation ring `𝒪_v` — necessarily its maximal ideal —
induces on `K_v` the valuation of the completion. -/
@[simp]
theorem valuation_adicCompletionIntegers (P : HeightOneSpectrum (v.adicCompletionIntegers K))
    (x : v.adicCompletion K) :
    P.valuation (v.adicCompletion K) x = Valued.v x := by
  rw [P.eq_maximalIdeal, valuation_maximalIdeal_adicCompletionIntegers]

/-- Any height-one prime `P` of the valuation ring `𝒪_v` — necessarily its maximal ideal —
induces on `K` the valuation `v` itself: the restriction to `K` of
`valuation_adicCompletionIntegers`. -/
theorem valuation_adicCompletion_algebraMap (P : HeightOneSpectrum (v.adicCompletionIntegers K))
    (z : K) :
    P.valuation (v.adicCompletion K) (algebraMap K (v.adicCompletion K) z) = v.valuation K z := by
  rw [valuation_adicCompletionIntegers]
  exact v.valuedAdicCompletion_eq_valuation' z

/-- An element of the ring of integers of a completion of valuation `exp (-e)` generates the
`e`-th power of the maximal ideal. -/
theorem span_singleton_eq_maximalIdeal_pow {x : v.adicCompletionIntegers K} {e : ℕ}
    (hx : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) x) =
      exp (-(e : ℤ))) :
    Ideal.span {x} = IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ e := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hx
    exact absurd hx.symm exp_ne_zero
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  have hu : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (u : v.adicCompletionIntegers K)) = 1 :=
    (adicCompletionIntegers.integers K v).valuation_unit u
  have hval : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (↑u * π ^ n)) = exp (-(n : ℤ)) := by
    rw [map_mul, map_mul, hu, one_mul, map_pow, map_pow,
      v.valued_algebraMap_eq_exp_neg_one_of_irreducible hπ, ← exp_nsmul]
    simp
  rw [hval, exp_inj, neg_inj, Int.natCast_inj] at hx
  subst hx
  rw [Ideal.span_singleton_eq_span_singleton.mpr (associated_unit_mul_left _ _ u.isUnit),
    ← Ideal.span_singleton_pow, hπ.maximalIdeal_eq]

/-- Any element of the ring of integers of the completion is congruent to an element of `R`
modulo the maximal ideal — equivalently, `R` surjects onto the residue field of `𝒪_v`.

This is approximation at the single threshold `1`, not density: it says nothing about
approximating to arbitrarily small valuation. -/
theorem exists_valued_sub_lt_one (x : v.adicCompletionIntegers K) :
    ∃ a : R, Valued.v ((x : v.adicCompletion K) - algebraMap R (v.adicCompletion K) a) < 1 := by
  -- approximate by an element of `K` first
  have hball : {y | Valued.v (y - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) := by
    rw [Valued.mem_nhds]
    exact ⟨1, fun y hy ↦ by simpa using hy⟩
  obtain ⟨w, hwball, z, rfl⟩ :=
    mem_closure_iff_nhds.mp (denseRange_algebraMap (K := K) v _) _ hball
  rw [Set.mem_ofPred_eq] at hwball
  -- the approximating element is integral at `v`
  have hz1 : v.valuation K z ≤ 1 := by
    rw [← v.valuedAdicCompletion_eq_valuation' z]
    calc Valued.v (algebraMap K (v.adicCompletion K) z)
        = Valued.v (algebraMap K (v.adicCompletion K) z - (x : v.adicCompletion K)
            + (x : v.adicCompletion K)) := by ring_nf
      _ ≤ max (Valued.v (algebraMap K (v.adicCompletion K) z - (x : v.adicCompletion K)))
            (Valued.v (x : v.adicCompletion K)) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le hwball.le x.2
  -- then approximate that element of `K` by an element of `R`
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hz1 1
  refine ⟨a, ?_⟩
  have ha' : Valued.v (algebraMap K (v.adicCompletion K) z -
      algebraMap R (v.adicCompletion K) a) < 1 := by
    rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K), ← map_sub,
      -- `valuedAdicCompletion_eq_valuation'` states its left side through `WithVal.equiv`, so a
      -- bare `rw` does not match the `algebraMap` spelling in the goal; `show` supplies the
      -- defeq bridge that lets the equation apply.
      show Valued.v (algebraMap K (v.adicCompletion K) (z - algebraMap R K a)) =
        v.valuation K (z - algebraMap R K a) from v.valuedAdicCompletion_eq_valuation' _,
      Valuation.map_sub_swap]
    simpa using ha
  calc Valued.v ((x : v.adicCompletion K) - algebraMap R (v.adicCompletion K) a)
      = Valued.v (((x : v.adicCompletion K) - algebraMap K (v.adicCompletion K) z)
          + (algebraMap K (v.adicCompletion K) z - algebraMap R (v.adicCompletion K) a)) := by
        ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ < 1 := max_lt (by rwa [Valuation.map_sub_swap] at hwball) ha'

/-- The residue field of `v` maps isomorphically onto the residue field of the ring of integers of
the completion at `v`. -/
noncomputable def residueFieldEquivAdicCompletionIntegers :
    (R ⧸ v.asIdeal) ≃+*
      (v.adicCompletionIntegers K ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  refine RingEquiv.ofBijective (Ideal.quotientMap (IsLocalRing.maximalIdeal _)
    (algebraMap R (v.adicCompletionIntegers K))
    (le_of_eq (v.under_maximalIdeal_adicCompletionIntegers (K := K)).symm)) ⟨?_, ?_⟩
  · exact Ideal.quotientMap_injective'
      (le_of_eq (v.under_maximalIdeal_adicCompletionIntegers (K := K)))
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := v.exists_valued_sub_lt_one (K := K) x
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk]
    refine Ideal.Quotient.eq.mpr ?_
    refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
      ℤᵐ⁰))).mpr ?_
    push_cast [IsScalarTower.algebraMap_apply R (v.adicCompletionIntegers K)
      (v.adicCompletion K)]
    rw [Valuation.map_sub_swap]
    exact ha

/-- **The residue-field equivalence on a quotient representative.** This is the characterization
consumers should use; the equivalence's construction as an `Ideal.quotientMap` is an implementation
detail and should not be unfolded. -/
@[simp]
theorem residueFieldEquivAdicCompletionIntegers_apply_mk (a : R) :
    v.residueFieldEquivAdicCompletionIntegers (K := K) (Ideal.Quotient.mk v.asIdeal a) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
        (algebraMap R (v.adicCompletionIntegers K) a) := (rfl)

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

section Extension

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

variable (K L)

/-- The extension of adic completions along `w ∣ v`: the ring homomorphism `K_v →+* L_w`
continuously extending `K → L`. -/
noncomputable def adicCompletionExtension : v.adicCompletion K →+* w.adicCompletion L :=
  haveI : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  (adicCompletion.equiv L w).symm.toRingHom.comp <|
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom

/-- Under `toCompletion`, the image of `x` is `UniformSpace.Completion.map` of the algebra map
applied to `x.toCompletion`. -/
@[simp]
lemma toCompletion_adicCompletionExtension (x : v.adicCompletion K) :
    (adicCompletionExtension K L v w x).toCompletion =
      UniformSpace.Completion.map
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) x.toCompletion :=
  (rfl)

/-- The square with sides `K → K_v → L_w` and `K → L → L_w` commutes. -/
-- Not `@[simp]`: the `simpNF` linter rejects it, because `simp` rewrites the left-hand side
-- further through `WithVal.equiv_symm_apply`, so this is not in simp normal form.
lemma adicCompletionExtension_coe (x : K) :
    adicCompletionExtension K L v w (x : v.adicCompletion K) =
      (algebraMap K L x : w.adicCompletion L) := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  apply adicCompletion.ext
  rw [toCompletion_adicCompletionExtension, adicCompletion.coe_toCompletion,
    UniformSpace.Completion.map_coe
      (uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w)]
  -- `WithVal` is a type synonym, so `algebraMap (WithVal _) (WithVal _)` is `algebraMap K L`
  -- transported along it; these two rewrites name that identification rather than leaving it to
  -- a bare `rfl`.
  rw [WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply]
  rfl

/-- `adicCompletionExtension` is continuous. -/
theorem continuous_adicCompletionExtension :
    Continuous (adicCompletionExtension K L v w) := by
  have h : (adicCompletionExtension K L v w : v.adicCompletion K → w.adicCompletion L) =
      adicCompletion.ofCompletion ∘ UniformSpace.Completion.map
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) ∘
        adicCompletion.toCompletion := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, ← toCompletion_adicCompletionExtension,
      adicCompletion.ofCompletion_toCompletion]
  rw [h]
  exact (adicCompletion.continuous_ofCompletion L w).comp
    (UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v))

/-- `adicCompletionExtension` is the *only* continuous ring homomorphism `K_v →+* L_w` extending
`K → L`: `K` is dense in `K_v`, so a continuous map out of it is pinned by its values there.

This is the universal property, available without unfolding the definition. -/
theorem eq_adicCompletionExtension_of_continuous {f : v.adicCompletion K →+* w.adicCompletion L}
    (hf : Continuous f)
    (hfK : ∀ x : K, f (x : v.adicCompletion K) = (algebraMap K L x : w.adicCompletion L)) :
    f = adicCompletionExtension K L v w :=
  DFunLike.coe_injective <| (v.denseRange_algebraMap K).equalizer hf
    (continuous_adicCompletionExtension K L v w)
    (funext fun x ↦ by
      simp only [Function.comp_apply, algebraMap_adicCompletion, Algebra.algebraMap_self_apply]
      rw [hfK x, adicCompletionExtension_coe])

open WithZeroTopology in
/-- The valuation on `L_w` restricted along `K_v → L_w` is the valuation on `K_v` raised to the
ramification index of `w` over `v`. -/
@[simp]
lemma valued_adicCompletionExtension (x : v.adicCompletion K) :
    Valued.v (adicCompletionExtension K L v w x) =
      Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  rw [← adicCompletion.valued_toCompletion L w (adicCompletionExtension K L v w x),
    toCompletion_adicCompletionExtension, ← adicCompletion.valued_toCompletion K v x]
  have hsurjK : Function.Surjective (⇑(Valued.v : Valuation (v.valuation K).Completion ℤᵐ⁰)) :=
    Valued.valuedCompletion_surjective_iff.mpr <| .of_comp (v.valuation_surjective K)
  have hsurjL : Function.Surjective (⇑(Valued.v : Valuation (w.valuation L).Completion ℤᵐ⁰)) :=
    Valued.valuedCompletion_surjective_iff.mpr <| .of_comp (w.valuation_surjective L)
  generalize x.toCompletion = y
  revert y
  apply funext_iff.mp
  symm
  apply UniformSpace.Completion.ext
  · exact (Valued.continuous_valuation_of_surjective hsurjK).pow _
  · exact (Valued.continuous_valuation_of_surjective hsurjL).comp
      UniformSpace.Completion.continuous_map
  intro a
  rw [UniformSpace.Completion.map_coe
      (uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w),
    Valued.valuedCompletion_apply, Valued.valuedCompletion_apply]
  exact valuation_liesOver (K := K) L v w (WithVal.equiv (v.valuation K) a)

/-- The extension maps the ring of integers of `K_v` into the ring of integers of `L_w`. -/
@[simp]
lemma adicCompletionExtension_mem_adicCompletionIntegers (x : v.adicCompletionIntegers K) :
    adicCompletionExtension K L v w (x : v.adicCompletion K) ∈ w.adicCompletionIntegers L := by
  rw [mem_adicCompletionIntegers, valued_adicCompletionExtension]
  exact pow_le_one' ((mem_adicCompletionIntegers ..).mp x.2) _

/-- The restriction of `adicCompletionExtension` to the rings of integers. -/
noncomputable def adicCompletionIntegersExtension :
    v.adicCompletionIntegers K →+* w.adicCompletionIntegers L :=
  ((adicCompletionExtension K L v w).comp
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).codRestrict
      (w.adicCompletionIntegers L).toSubring
      fun x ↦ adicCompletionExtension_mem_adicCompletionIntegers K L v w x

/-- `adicCompletionIntegersExtension` agrees with `adicCompletionExtension` on the integers. -/
@[simp]
lemma coe_adicCompletionIntegersExtension (x : v.adicCompletionIntegers K) :
    (adicCompletionIntegersExtension K L v w x : w.adicCompletion L) =
      adicCompletionExtension K L v w (x : v.adicCompletion K) :=
  (rfl)

/-- The maximal ideal of the ring of integers of `L_w` contracts to the maximal ideal of the ring
of integers of `K_v`.

Stated with `Ideal.comap` of the explicit ring homomorphism, not `Ideal.under`: `Ideal.under A` is
`Ideal.comap (algebraMap A B)` and so needs an `Algebra (v.adicCompletionIntegers K)
(w.adicCompletionIntegers L)` instance, which does not exist — the extension is a bare `RingHom`.
Naming it `under_` would assert a contraction along an `algebraMap` that is not there. -/
@[simp]
lemma comap_maximalIdeal_adicCompletionIntegersExtension :
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).comap
        (adicCompletionIntegersExtension K L v w) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  ext x
  rw [Ideal.mem_comap]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (w.adicCompletion L)
    (WithZero (Multiplicative ℤ))))).trans <| Iff.trans ?_
      (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
        (WithZero (Multiplicative ℤ))))).symm
  rw [coe_adicCompletionIntegersExtension K L v w, valued_adicCompletionExtension]
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  exact pow_lt_one_iff
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal v.ne_bot)

end Extension

end IsDedekindDomain.HeightOneSpectrum

end
