/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.AffineModel.Extension
public import TauCeti.RingTheory.DedekindDomain.KummerDedekind

/-!
# Kummer's theorem at an affine model: the places over a place, exactly

Let `F' / k'` be a finite extension of an extension of fields `F / k`, let `R` be an affine model
of `F / k` and let `S` be a module-finite affine model of `F' / k'` over `R`, as in
`TauCeti/FieldTheory/FunctionField/AffineModel/Extension.lean`.  Let `y : S` and let `𝔭` be a
height one prime of `R` **prime to the conductor** of `R[y]` in `S` — Stichtenoth's monogenicity
hypothesis `𝒪'_P = 𝒪_P[y]`, in the form that only asks for it after localizing at `𝔭`.  Then the
factorization

`φ ≡ ∏ᵢ γᵢ ^ εᵢ (mod 𝔭)`,  `φ` the minimal polynomial of `y` over `R`,

determines the places of `F' / k'` over the place of `𝔭` completely: they are in bijection with
the monic irreducible factors `γᵢ`, and the place attached to `γᵢ` has relative degree `deg γᵢ`
and ramification index `εᵢ`.  This is Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed.,
Corollary 3.3.8 — the conclusion that
`TauCeti/FieldTheory/FunctionField/Place/Extension/Kummer.lean` deliberately does not draw: its
Theorem 3.3.7 bounds the splitting of a place without the monogenicity hypothesis, and neither
computes the ramification indices nor rules out further places over `P`.

The proof is the affine-model dictionary of
`TauCeti/FieldTheory/FunctionField/AffineModel/Extension.lean` — the places over the place of `𝔭`
are the primes of `S` over `𝔭`, with `e` the ramification index and `f` the residue degree of the
centre — composed with the Kummer–Dedekind criterion of
`TauCeti/RingTheory/DedekindDomain/KummerDedekind.lean`.  Nothing about function fields enters
beyond that dictionary; in particular no hypothesis on `k`, `k'` or the constant fields is needed.

The polynomial being factored is Stichtenoth's `φ`: `R` is integrally closed with fraction field
`F`, so `minpoly R y` maps to `minpoly F y` under `R → F`, by Mathlib's
`minpoly.isIntegrallyClosed_eq_field_fractions`.  The conductor hypothesis holds at every prime
as soon as `S = R[y]`, since then the conductor is the unit ideal by Mathlib's
`conductor_eq_top_of_adjoin_eq_top`.

The places of `F' / k'` outside the finite chart of `S` are reached, as always, by running the
same statement at a second model, exactly as for the fundamental identity.

## Main definitions

* `TauCeti.Place.restrictOfPrimeEquivNormalizedFactors`: the places of `F' / k'` over the place of
  `𝔭`, in bijection with the normalized irreducible factors of `minpoly R y` modulo `𝔭`.

## Main results

* `TauCeti.Place.restrictOfPrimeEquivNormalizedFactors_symm_apply_coe_eq_ofPrime`: the place
  attached to the class of a lift `Q` is the place of the prime `span (𝔭 S ∪ {Q (y)})` of `S`.
* `TauCeti.Place.valuation_restrictOfPrimeEquivNormalizedFactors_symm_apply_lt_one`: the place
  attached to a factor is a zero of that factor evaluated at `y`.
* `TauCeti.Place.relativeDegree_restrictOfPrimeEquivNormalizedFactors_symm_apply`: the relative
  degree of the place attached to a factor is the degree of that factor.
* `TauCeti.Place.ramificationIdx_restrictOfPrimeEquivNormalizedFactors_symm_apply`: its
  ramification index is the multiplicity of that factor.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Corollary 3.3.8.
-/

public section

open IsDedekindDomain Polynomial UniqueFactorizationMonoid

namespace TauCeti

namespace Place

universe u u' v v' w w'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable {R : Type w} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable {S : Type w'} [CommRing S] [IsDedekindDomain S] [Algebra S F'] [IsFractionRing S F']
variable [Algebra R S] [Algebra R F'] [IsScalarTower R S F'] [IsScalarTower R F F']
variable [Algebra.IsIntegral F F']
variable [Algebra k R] [IsScalarTower k R F] [Algebra k' S] [IsScalarTower k' S F']
variable [Module.Finite R S]
variable (k F) (𝔭 : HeightOneSpectrum R) {y : S}

attribute [local instance] Ideal.Quotient.field

variable (hy : (conductor R y).comap (algebraMap R S) ⊔ 𝔭.asIdeal = ⊤) (hy' : IsIntegral R y)

include hy hy'

open scoped Classical in
/-- **Kummer's theorem** (Stichtenoth, Corollary 3.3.8): when the height one prime `𝔭` of the
model `R` is prime to the conductor of `R[y]` in the model `S`, the places of `F' / k'` lying over
the place of `𝔭` are exactly the normalized irreducible factors of `minpoly R y` modulo `𝔭`. -/
noncomputable def restrictOfPrimeEquivNormalizedFactors :
    {P' : Place k' F' // P'.restrict k F = ofPrime k F 𝔭} ≃
      {d : (R ⧸ 𝔭.asIdeal)[X] |
        d ∈ normalizedFactors ((minpoly R y).map (Ideal.Quotient.mk 𝔭.asIdeal))} :=
  have := FaithfulSMul.of_field_isFractionRing R S F F'
  (restrictOfPrimeEquivPrimesOver k F 𝔭).trans
    (KummerDedekind.primesOverEquivNormalizedFactorsMinPolyMk 𝔭.isMaximal 𝔭.ne_bot hy hy')

open scoped Classical in
/-- The prime of `S` over `𝔭` that the Kummer–Dedekind correspondence attaches to a normalized
irreducible factor `d` of `minpoly R y` modulo `𝔭`, as a height one prime. -/
private noncomputable def primeOfFactor {d : (R ⧸ 𝔭.asIdeal)[X]}
    (hd : d ∈ normalizedFactors ((minpoly R y).map (Ideal.Quotient.mk 𝔭.asIdeal))) :
    HeightOneSpectrum S :=
  have := FaithfulSMul.of_field_isFractionRing R S F F'
  ⟨_, ((KummerDedekind.primesOverEquivNormalizedFactorsMinPolyMk
      𝔭.isMaximal 𝔭.ne_bot hy hy').symm ⟨d, hd⟩).2.1,
    Ideal.ne_bot_of_mem_primesOver 𝔭.ne_bot
      ((KummerDedekind.primesOverEquivNormalizedFactorsMinPolyMk
        𝔭.isMaximal 𝔭.ne_bot hy hy').symm ⟨d, hd⟩).2⟩

open scoped Classical in
/-- The place attached to a factor is the place of the prime attached to it. -/
private theorem coe_restrictOfPrimeEquivNormalizedFactors_symm_apply {d : (R ⧸ 𝔭.asIdeal)[X]}
    (hd : d ∈ normalizedFactors ((minpoly R y).map (Ideal.Quotient.mk 𝔭.asIdeal))) :
    ((restrictOfPrimeEquivNormalizedFactors (k' := k') (F' := F') k F 𝔭 hy hy').symm ⟨d, hd⟩).1 =
      ofPrime k' F' (primeOfFactor (F' := F') F 𝔭 hy hy' hd) :=
  have := FaithfulSMul.of_field_isFractionRing R S F F'
  restrictOfPrimeEquivPrimesOver_symm_apply_coe k F 𝔭 (primeOfFactor (F' := F') F 𝔭 hy hy' hd)
    ((KummerDedekind.primesOverEquivNormalizedFactorsMinPolyMk
      𝔭.isMaximal 𝔭.ne_bot hy hy').symm ⟨d, hd⟩).2

omit [IsFractionRing S F'] [Algebra.IsIntegral F F'] [Module.Finite R S] in
open scoped Classical in
/-- The prime attached to the class of a lift `Q` is `𝔭 S` together with `Q (y)`. -/
private theorem asIdeal_primeOfFactor {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk 𝔭.asIdeal) ∈
      normalizedFactors ((minpoly R y).map (Ideal.Quotient.mk 𝔭.asIdeal))) :
    (primeOfFactor (F' := F') F 𝔭 hy hy' hQ).asIdeal =
      Ideal.span (𝔭.asIdeal.map (algebraMap R S) ∪ {aeval y Q}) :=
  have := FaithfulSMul.of_field_isFractionRing R S F F'
  KummerDedekind.primesOverEquivNormalizedFactorsMinPolyMk_symm_apply_coe
    𝔭.isMaximal 𝔭.ne_bot hy hy' hQ

open scoped Classical in
/-- **The place attached to a Kummer factor, explicitly**: for `Q` a lift of a normalized
irreducible factor of `minpoly R y` modulo `𝔭`, the place of `F' / k'` attached to that factor is
the place of the prime of `S` spanned by `𝔭 S` together with `Q (y)`. -/
theorem restrictOfPrimeEquivNormalizedFactors_symm_apply_coe_eq_ofPrime {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk 𝔭.asIdeal) ∈
      normalizedFactors ((minpoly R y).map (Ideal.Quotient.mk 𝔭.asIdeal)))
    (𝔓 : HeightOneSpectrum S)
    (h𝔓 : 𝔓.asIdeal = Ideal.span (𝔭.asIdeal.map (algebraMap R S) ∪ {aeval y Q})) :
    ((restrictOfPrimeEquivNormalizedFactors (k' := k') (F' := F') k F 𝔭 hy hy').symm
        ⟨Q.map (Ideal.Quotient.mk 𝔭.asIdeal), hQ⟩).1 = ofPrime k' F' 𝔓 := by
  have h : primeOfFactor (F' := F') F 𝔭 hy hy' hQ = 𝔓 :=
    HeightOneSpectrum.ext ((asIdeal_primeOfFactor F 𝔭 hy hy' hQ).trans h𝔓.symm)
  rw [coe_restrictOfPrimeEquivNormalizedFactors_symm_apply, h]

open scoped Classical in
/-- **The place attached to a Kummer factor is the one where that factor vanishes**: for `Q` a lift
of a normalized irreducible factor of `minpoly R y` modulo `𝔭`, the place of `F' / k'` attached to
that factor has a zero at `Q (y)`.  Since distinct factors give distinct places, this identifies
the bijection concretely. -/
theorem valuation_restrictOfPrimeEquivNormalizedFactors_symm_apply_lt_one {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk 𝔭.asIdeal) ∈
      normalizedFactors ((minpoly R y).map (Ideal.Quotient.mk 𝔭.asIdeal))) :
    ((restrictOfPrimeEquivNormalizedFactors (k' := k') (F' := F') k F 𝔭 hy hy').symm
        ⟨Q.map (Ideal.Quotient.mk 𝔭.asIdeal), hQ⟩).1.valuation
      (algebraMap S F' (aeval y Q)) < 1 := by
  rw [coe_restrictOfPrimeEquivNormalizedFactors_symm_apply, valuation_ofPrime_algebraMap_lt_one_iff,
    asIdeal_primeOfFactor]
  exact Ideal.subset_span (by simp)

open scoped Classical in
/-- **The relative degree of a Kummer factor is its degree** (Stichtenoth, Corollary 3.3.8): the
place of `F' / k'` over the place of `𝔭` attached to a normalized irreducible factor `d` of
`minpoly R y` modulo `𝔭` has relative degree `d.natDegree`. -/
theorem relativeDegree_restrictOfPrimeEquivNormalizedFactors_symm_apply {d : (R ⧸ 𝔭.asIdeal)[X]}
    (hd : d ∈ normalizedFactors ((minpoly R y).map (Ideal.Quotient.mk 𝔭.asIdeal))) :
    relativeDegree k F
        ((restrictOfPrimeEquivNormalizedFactors (k' := k') (F' := F') k F 𝔭 hy hy').symm
          ⟨d, hd⟩).1 =
      d.natDegree := by
  have := FaithfulSMul.of_field_isFractionRing R S F F'
  rw [coe_restrictOfPrimeEquivNormalizedFactors_symm_apply, relativeDegree_ofPrime (R := R) k F]
  exact KummerDedekind.inertiaDeg_primesOverEquivNormalizedFactorsMinPolyMk_symm_apply
    𝔭.isMaximal 𝔭.ne_bot hy hy' hd

open scoped Classical in
/-- **The ramification index of a Kummer factor is its multiplicity** (Stichtenoth,
Corollary 3.3.8): the place of `F' / k'` over the place of `𝔭` attached to a normalized
irreducible factor `d` of `minpoly R y` modulo `𝔭` has ramification index the multiplicity of `d`
in `minpoly R y` modulo `𝔭`. -/
theorem ramificationIdx_restrictOfPrimeEquivNormalizedFactors_symm_apply {d : (R ⧸ 𝔭.asIdeal)[X]}
    (hd : d ∈ normalizedFactors ((minpoly R y).map (Ideal.Quotient.mk 𝔭.asIdeal))) :
    ramificationIdx F
        ((restrictOfPrimeEquivNormalizedFactors (k' := k') (F' := F') k F 𝔭 hy hy').symm
          ⟨d, hd⟩).1 =
      multiplicity d ((minpoly R y).map (Ideal.Quotient.mk 𝔭.asIdeal)) := by
  have := FaithfulSMul.of_field_isFractionRing R S F F'
  rw [coe_restrictOfPrimeEquivNormalizedFactors_symm_apply, ramificationIdx_ofPrime (R := R) k F]
  exact KummerDedekind.ramificationIdx_primesOverEquivNormalizedFactorsMinPolyMk_symm_apply
    𝔭.isMaximal 𝔭.ne_bot hy hy' hd

end Place

end TauCeti
