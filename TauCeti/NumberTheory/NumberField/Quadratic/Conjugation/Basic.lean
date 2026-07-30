/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.PowerBasis
public import TauCeti.NumberTheory.ClassGroup.Equiv
public import TauCeti.NumberTheory.NumberField.Quadratic.Basic

/-!
# Quadratic conjugation on a quadratic number field

For a quadratic number field `K` — presented by an algebraic integer `θ : 𝓞 K` generating `K`
over `ℚ` whose minimal polynomial over `ℤ` is `X² - d` — this file constructs the nontrivial
`ℚ`-algebra automorphism of `K`, characterised by `θ ↦ -θ`, and restricts it to a ring
automorphism of `𝓞 K`. This is the field-theoretic conjugation of `ℚ(√d)`.

It is the automorphism whose induced action on the class group `Cl(𝓞 K)` is by **inversion** — the
genus-theoretic fact that `I · σI` is principal — which is the mechanism behind the summit
isomorphism `Gal(K_gen/K) ≅ Cl(K)/Cl(K)²` of the multiquadratic roadmap (Layer 3: the genus field
and the 2-rank theorem). Here we build the automorphism and record that it is an involution on `K`,
on `𝓞 K`, and on `Cl(𝓞 K)`; the refinement of that involution to inversion (which needs `I · σI`
principal) is developed downstream.

See D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*, for the
classical genus theory this supports.

## Main definitions and results

* `TauCeti.NumberField.quadraticConj`: the conjugation `K ≃ₐ[ℚ] K`, sending `θ ↦ -θ`, with
  `quadraticConj_gen` (`quadraticConj θ = -θ`) and `quadraticConj_involutive`.
* `TauCeti.NumberField.ringOfIntegersQuadraticConj`: its restriction to a ring automorphism
  `𝓞 K ≃+* 𝓞 K`, with `coe_ringOfIntegersQuadraticConj`, `ringOfIntegersQuadraticConj_gen`, and
  `ringOfIntegersQuadraticConj_involutive`.
* `TauCeti.NumberField.mulEquiv_ringOfIntegersQuadraticConj_involutive`: the induced action on
  `ClassGroup (𝓞 K)` is an involution.
-/

public section

open Polynomial NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- `X² - C a` is invariant under negating the variable: it is an even polynomial. -/
private theorem X_pow_two_sub_C_comp_neg (a : ℚ) :
    (X ^ 2 - C a).comp (-X) = X ^ 2 - C a := by
  rw [sub_comp, pow_comp, X_comp, C_comp]; ring

/-- `θ` and `-θ` have the same minimal polynomial over `ℚ` (both `X² - d`, an even polynomial). -/
private theorem minpoly_rat_eq_neg (hmin : minpoly ℤ θ = X ^ 2 - C d) :
    minpoly ℚ (θ : K) = minpoly ℚ (-(θ : K)) := by
  rw [minpoly.neg, minpoly_rat_quadratic hmin, natDegree_X_pow_sub_C, X_pow_two_sub_C_comp_neg]
  ring

/-- The power basis `1, θ` of the quadratic field `K` over `ℚ`. -/
private noncomputable def quadraticPowerBasis (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    PowerBasis ℚ K :=
  PowerBasis.ofAdjoinEqTop' θ.isIntegral_coe.tower_top hgen

private theorem quadraticPowerBasis_gen (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    (quadraticPowerBasis hgen).gen = (θ : K) :=
  PowerBasis.ofAdjoinEqTop'_gen _ hgen

/-- `-θ` also generates `K` over `ℚ`, so it too carries a power basis. -/
private theorem adjoin_neg_eq_top (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Algebra.adjoin ℚ {(-(θ : K))} = ⊤ := by
  have hmem : (θ : K) ∈ Algebra.adjoin ℚ {(-(θ : K))} := by
    have h := neg_mem (Algebra.self_mem_adjoin_singleton ℚ (-(θ : K)))
    rwa [neg_neg] at h
  refine le_antisymm le_top ?_
  rw [← hgen]
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hmem)

/-- The power basis `1, -θ` of `K` over `ℚ`. -/
private noncomputable def quadraticPowerBasisNeg (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    PowerBasis ℚ K :=
  PowerBasis.ofAdjoinEqTop' θ.isIntegral_coe.tower_top.neg (adjoin_neg_eq_top hgen)

private theorem quadraticPowerBasisNeg_gen (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    (quadraticPowerBasisNeg hgen).gen = -(θ : K) :=
  PowerBasis.ofAdjoinEqTop'_gen _ (adjoin_neg_eq_top hgen)

/-- **Quadratic conjugation.** The nontrivial `ℚ`-automorphism of the quadratic field `K = ℚ(√d)`,
characterised by `θ ↦ -θ`. Since `θ` and `-θ` share a minimal polynomial, it is the
`PowerBasis.equivOfMinpoly` between their power bases. -/
noncomputable def quadraticConj (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : K ≃ₐ[ℚ] K :=
  (quadraticPowerBasis hgen).equivOfMinpoly (quadraticPowerBasisNeg hgen) (by
    rw [quadraticPowerBasis_gen, quadraticPowerBasisNeg_gen]; exact minpoly_rat_eq_neg hmin)

/-- Quadratic conjugation sends the generator `θ` to `-θ`. -/
@[simp] theorem quadraticConj_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    quadraticConj hmin hgen (θ : K) = -(θ : K) := by
  rw [quadraticConj]
  nth_rewrite 1 [← quadraticPowerBasis_gen hgen]
  rw [PowerBasis.equivOfMinpoly_gen, quadraticPowerBasisNeg_gen]

/-- Quadratic conjugation is an involution on `K` (applying it twice is the identity). -/
@[simp] theorem quadraticConj_involutive (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Function.Involutive (quadraticConj hmin hgen) := by
  have hext : (quadraticConj hmin hgen).toAlgHom.comp (quadraticConj hmin hgen).toAlgHom
      = AlgHom.id ℚ K := by
    apply (quadraticPowerBasis hgen).algHom_ext
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, quadraticPowerBasis_gen,
      quadraticConj_gen, map_neg, neg_neg, AlgHom.id_apply]
  intro x
  have := AlgHom.congr_fun hext x
  simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, AlgHom.id_apply] using this

/-- **Quadratic conjugation on the ring of integers.** The restriction of `quadraticConj` to
`𝓞 K`, a ring automorphism `𝓞 K ≃+* 𝓞 K`. This is the automorphism whose action on
`ClassGroup (𝓞 K)` is by inversion (the genus-theoretic fact that `I · σI` is principal). -/
noncomputable def ringOfIntegersQuadraticConj (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : 𝓞 K ≃+* 𝓞 K :=
  RingOfIntegers.mapRingEquiv (quadraticConj hmin hgen).toRingEquiv

/-- Passing to `K`, `ringOfIntegersQuadraticConj x` is `quadraticConj` of the image of `x`. -/
@[simp] theorem coe_ringOfIntegersQuadraticConj (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (x : 𝓞 K) :
    (ringOfIntegersQuadraticConj hmin hgen x : K) = quadraticConj hmin hgen (x : K) := by
  rw [ringOfIntegersQuadraticConj, RingOfIntegers.mapRingEquiv_apply, AlgEquiv.coe_ringEquiv]

/-- Quadratic conjugation on `𝓞 K` sends the generator `θ` to `-θ`. -/
@[simp] theorem ringOfIntegersQuadraticConj_gen (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    ringOfIntegersQuadraticConj hmin hgen θ = -θ := by
  have h : (ringOfIntegersQuadraticConj hmin hgen θ : K) = ((-θ : 𝓞 K) : K) := by
    rw [coe_ringOfIntegersQuadraticConj, quadraticConj_gen]; push_cast; ring
  exact RingOfIntegers.coe_injective h

/-- Quadratic conjugation is an involution on `𝓞 K` (applying it twice is the identity). -/
@[simp] theorem ringOfIntegersQuadraticConj_involutive (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Function.Involutive (ringOfIntegersQuadraticConj hmin hgen) := by
  intro x
  have h : (ringOfIntegersQuadraticConj hmin hgen (ringOfIntegersQuadraticConj hmin hgen x) : K)
      = (x : K) := by
    rw [coe_ringOfIntegersQuadraticConj, coe_ringOfIntegersQuadraticConj]
    exact quadraticConj_involutive hmin hgen (x : K)
  exact RingOfIntegers.coe_injective h

/-- Quadratic conjugation acts as an **involution on the class group** `Cl(𝓞 K)`. This is the
group-action shadow of `ringOfIntegersQuadraticConj_involutive`, and the first step towards the
genus-theoretic fact that the induced action is inversion (hence trivial on `Cl/Cl²`). -/
@[simp] theorem mulEquiv_ringOfIntegersQuadraticConj_involutive (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Function.Involutive (ClassGroup.mulEquiv (ringOfIntegersQuadraticConj hmin hgen)) :=
  ClassGroup.mulEquiv_involutive (ringOfIntegersQuadraticConj_involutive hmin hgen)

end TauCeti.NumberField
