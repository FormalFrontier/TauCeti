/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ClassGroup.ElementaryTwoQuotient
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation
public import TauCeti.NumberTheory.NumberField.Quadratic.ConjugationNorm

/-!
# Quadratic conjugation acts on the class group by inversion

For a quadratic number field `K = ℚ(√d)`, `TauCeti.NumberField.ringOfIntegersQuadraticConj` is the
ring automorphism `σ : 𝓞 K ≃+* 𝓞 K` restricting field conjugation. Its induced action on the class
group `Cl(𝓞 K)` is an involution (recorded in `Quadratic/Conjugation.lean`); this file sharpens the
involution to **inversion**, the genus-theoretic mechanism `I · σI` principal, and concludes that
`σ` therefore acts trivially on the maximal elementary-2 quotient `Cl(𝓞 K)/Cl(𝓞 K)²`.

The reduction has two moves. First a general **bridge**: for a ring isomorphism `f : R ≃+* R'` of
Dedekind domains, `ClassGroup.mulEquiv f` sends the class of an ideal to the class of its
pushforward `Ideal.map f` (`ClassGroup.mulEquiv_mk0`), derived from the fraction-field computation
`ClassGroup.mulEquiv_mk_fractionRing`. Second the **inversion**: the ideal class of `σI` is the
inverse of the class of `I` because `I · σI` is principal — the norm-principality theorem
`isPrincipal_mul_map_ringOfIntegersQuadraticConj` (in `Quadratic/ConjugationNorm.lean`) combined
with `ClassGroup.mk0_eq_mk0_inv_iff`. Reducing to `IsSquare (C⁻¹ / C)` in the elementary-2 quotient
then gives the identity on `Cl/Cl²`.

This is Layer 3 of the multiquadratic roadmap: the summit isomorphism
`Gal(K_gen/K) ≅ Cl(K)/Cl(K)²` factors the conjugation action through its triviality on `Cl/Cl²`.

## Main results

* `ClassGroup.mulEquiv_mk0`: the class-group equivalence induced by a ring isomorphism sends the
  class of an ideal to the class of its image ideal.
* `TauCeti.NumberField.mulEquiv_ringOfIntegersQuadraticConj_eq_inv`: quadratic conjugation acts on
  `Cl(𝓞 K)` by inversion.
* `TauCeti.NumberField.elementaryTwoQuotientCongr_ringOfIntegersQuadraticConj_eq_self`: hence
  quadratic conjugation is the identity on the maximal elementary-2 quotient `Cl(𝓞 K)/Cl(𝓞 K)²`.
-/

public section

open scoped nonZeroDivisors

open NumberField Polynomial

namespace ClassGroup

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- Transport of a `coeIdeal` along `FractionalIdeal.ringEquivOfRingEquiv f` is the `coeIdeal` of
the pushforward ideal `Ideal.map f`. This is the fraction-field shadow of `Ideal.map` used to
compute the induced class-group map on `ClassGroup.mk0`. -/
private theorem ringEquivOfRingEquiv_coeIdeal [IsDomain R] [IsDomain R'] (K L : Type*) [Field K]
    [Field L] [Algebra R K] [Algebra R' L] [IsFractionRing R K] [IsFractionRing R' L] (f : R ≃+* R')
    (I : Ideal R) :
    FractionalIdeal.ringEquivOfRingEquiv K L f (I : FractionalIdeal R⁰ K) =
      (Ideal.map (f : R →+* R') I : FractionalIdeal R'⁰ L) := by
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  rw [← FractionalIdeal.val_eq_coe, FractionalIdeal.ringEquivOfRingEquiv_apply_val,
    FractionalIdeal.val_eq_coe, FractionalIdeal.coe_coeIdeal, FractionalIdeal.coe_coeIdeal]
  ext x
  simp only [Submodule.mem_map, FractionalIdeal.mem_coeSubmodule]
  constructor
  · rintro ⟨y, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨f r, Ideal.mem_map_of_mem _ hr, by
      simp [IsFractionRing.semilinearEquivOfRingEquiv_algebraMap]⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective (f : R →+* R') f.surjective).mp hs
    exact ⟨algebraMap R K r, ⟨r, hr, rfl⟩, by
      simp [IsFractionRing.semilinearEquivOfRingEquiv_algebraMap]⟩

/-- The pushforward of a nonzero ideal along a ring isomorphism is nonzero, hence stays a nonzero
divisor in the ideal monoid. -/
theorem map_ideal_mem_nonZeroDivisors [IsDomain R] [IsDomain R'] (f : R ≃+* R')
    {I : Ideal R} (hI : I ∈ (Ideal R)⁰) :
    Ideal.map (f : R →+* R') I ∈ (Ideal R')⁰ := by
  rw [mem_nonZeroDivisors_iff_ne_zero] at hI ⊢
  rw [ne_eq, Ideal.zero_eq_bot,
    Ideal.map_eq_bot_iff_of_injective (f := (f : R →+* R')) f.injective, ← Ideal.zero_eq_bot]
  exact hI

/-- **The class-group map induced by a ring isomorphism, on ideal classes.** For a ring isomorphism
`f : R ≃+* R'` of Dedekind domains, `ClassGroup.mulEquiv f` sends the class of a nonzero ideal `I`
to the class of its pushforward `Ideal.map f I`. This is the bridge between the abstract functorial
action `ClassGroup.mulEquiv` and the concrete pushforward of ideals. -/
theorem mulEquiv_mk0 [IsDedekindDomain R] [IsDedekindDomain R'] (f : R ≃+* R') (I : (Ideal R)⁰) :
    ClassGroup.mulEquiv f (ClassGroup.mk0 I) =
      ClassGroup.mk0 ⟨Ideal.map (f : R →+* R') (I : Ideal R),
        map_ideal_mem_nonZeroDivisors f I.2⟩ := by
  rw [← ClassGroup.mk_mk0 (FractionRing R) I, ClassGroup.mulEquiv_mk_fractionRing,
    ← ClassGroup.mk_mk0 (FractionRing R')]
  congr 1
  apply Units.ext
  simp only [Units.coe_mapEquiv, FractionalIdeal.coe_mk0, RingEquiv.coe_toMulEquiv]
  exact ringEquivOfRingEquiv_coeIdeal (FractionRing R) (FractionRing R') f I

end ClassGroup

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **Quadratic conjugation acts on the class group by inversion.** The induced action of quadratic
conjugation `σ = ringOfIntegersQuadraticConj` on `Cl(𝓞 K)` sends each class to its inverse, because
`I · σI` is principal (`isPrincipal_mul_map_ringOfIntegersQuadraticConj`). This sharpens
`mulEquiv_ringOfIntegersQuadraticConj_involutive` from an involution to inversion. -/
theorem mulEquiv_ringOfIntegersQuadraticConj_eq_inv (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (C : ClassGroup (𝓞 K)) :
    ClassGroup.mulEquiv (ringOfIntegersQuadraticConj hmin hgen) C = C⁻¹ := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective C
  rw [ClassGroup.mulEquiv_mk0, ClassGroup.mk0_eq_mk0_inv_iff]
  obtain ⟨x, hx⟩ := (isPrincipal_mul_map_ringOfIntegersQuadraticConj hmin hgen I).principal
  have hIne : (I : Ideal (𝓞 K)) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hmapne : Ideal.map (ringOfIntegersQuadraticConj hmin hgen) (I : Ideal (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot,
      Ideal.map_eq_bot_iff_of_injective (ringOfIntegersQuadraticConj hmin hgen).injective,
      ← Ideal.zero_eq_bot]
    exact hIne
  refine ⟨x, ?_, ?_⟩
  · intro hx0
    subst hx0
    rw [Submodule.span_zero_singleton] at hx
    exact mul_ne_zero hIne hmapne (hx.trans Ideal.zero_eq_bot.symm)
  · rw [mul_comm]
    exact hx

/-- **Quadratic conjugation acts trivially on `Cl(𝓞 K)/Cl(𝓞 K)²`.** Because it acts on `Cl(𝓞 K)` by
inversion (as `I · σI` is principal), the induced `ZMod 2`-linear map on the maximal elementary-2
quotient is the identity. This is the capstone reduction feeding the genus-field 2-rank theorems. -/
theorem elementaryTwoQuotientCongr_ringOfIntegersQuadraticConj_eq_self
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (x : TauCeti.ClassGroup.ElementaryTwoQuotient (𝓞 K)) :
    TauCeti.ClassGroup.elementaryTwoQuotientCongr
      (ClassGroup.mulEquiv (ringOfIntegersQuadraticConj hmin hgen)) x = x := by
  obtain ⟨C, rfl⟩ := TauCeti.ClassGroup.elementaryTwoQuotientMk_surjective (𝓞 K) x
  rw [TauCeti.ClassGroup.elementaryTwoQuotientCongr_mk,
    mulEquiv_ringOfIntegersQuadraticConj_eq_inv hmin hgen,
    TauCeti.ClassGroup.elementaryTwoQuotientMk_eq_iff]
  exact ⟨C⁻¹, by rw [div_eq_mul_inv]⟩

end TauCeti.NumberField
