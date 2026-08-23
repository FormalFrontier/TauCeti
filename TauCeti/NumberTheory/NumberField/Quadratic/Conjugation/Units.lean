/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.InfinitePlace
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Norm
public import TauCeti.NumberTheory.NumberField.Units.ElementaryTwoQuotient

/-!
# Units and quadratic conjugation

This file records two sign and square-class consequences for units in a quadratic number field.
A unit whose product with its quadratic conjugate is one is, up to sign, totally positive. It
follows from Dirichlet's unit theorem that a real quadratic field in which every unit has
conjugation norm one has a totally positive unit that is not a square.

These are the archimedean unit inputs to the narrow ambiguous class number formula.

## Main results

* `isTotallyPositive_or_isTotallyPositive_neg_of_mul_ringOfIntegersQuadraticConj_eq_one`:
  a norm-one unit is, up to sign, totally positive.
* `NumberField.exists_unit_isTotallyPositive_and_notMem_square`: if every unit is totally positive
  up to sign and the unit rank is nonzero, there is a totally positive unit that is not a square.
-/

public section

open Polynomial NumberField
open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **A unit of norm one is `±` a totally positive unit.** If `u σu = 1` then `u / σu = u²` is
totally positive, so `u` and `σu` have the same sign at every real place; since every real
embedding of a quadratic field is one fixed embedding, or that embedding composed with `σ`, all
real embeddings give `u` the same sign. -/
theorem isTotallyPositive_or_isTotallyPositive_neg_of_mul_ringOfIntegersQuadraticConj_eq_one
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {u : 𝓞 K}
    (hnorm : u * ringOfIntegersQuadraticConj hmin hgen u = 1) :
    IsTotallyPositive (u : K) ∨ IsTotallyPositive (-(u : K)) := by
  have hu : u ≠ 0 := left_ne_zero_of_mul_eq_one hnorm
  have huK : (u : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hu
  have hσ : (u : K) * quadraticConj hmin hgen (u : K) = 1 := by
    simpa only [coe_mul_ringOfIntegersQuadraticConj, map_one] using
      congrArg (fun x : 𝓞 K => (x : K)) hnorm
  have hσne : quadraticConj hmin hgen (u : K) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hσ; exact zero_ne_one hσ
  refine isTotallyPositive_or_isTotallyPositive_neg_of_isTotallyPositive_div_quadraticConj
    hmin hgen (z := (u : K)) ?_
  have hdiv : (u : K) / quadraticConj hmin hgen (u : K) = (u : K) ^ 2 := by
    rw [div_eq_iff hσne]
    linear_combination (-(u : K)) * hσ
  rw [hdiv]
  exact isTotallyPositive_sq huK

/-- **A totally positive unit has conjugation norm one.** Its conjugation norm is `±1`, and
total positivity rules out the negative sign because the field norm is positive. -/
theorem mul_ringOfIntegersQuadraticConj_eq_one_of_isTotallyPositive
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (u : (𝓞 K)ˣ)
    (hpos : IsTotallyPositive ((u : 𝓞 K) : K)) :
    (u : 𝓞 K) * ringOfIntegersQuadraticConj hmin hgen (u : 𝓞 K) = 1 := by
  rcases mul_ringOfIntegersQuadraticConj_eq_one_or_neg_one hmin hgen u with h | h
  · exact h
  · have hnorm_pos := norm_pos_of_isTotallyPositive
      (RingOfIntegers.coe_ne_zero_iff.mpr u.ne_zero) hpos
    have hnorm_neg : Algebra.norm ℚ (((u : 𝓞 K) : K)) = -1 := by
      apply (algebraMap ℚ K).injective
      rw [algebraMap_norm_eq_mul_ringOfIntegersQuadraticConj hmin hgen, h]
      simp
    rw [hnorm_neg] at hnorm_pos
    norm_num at hnorm_pos

/-- **A unit of conjugation norm `-1` makes the quadratic generator totally positive up to
sign.** The quotient of `θu` by its quadratic conjugate is the square `u²`. -/
theorem unit_gen_mul_isTotallyPositive_or_isTotallyPositive_neg_of_norm_eq_neg_one
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) (u : (𝓞 K)ˣ)
    (hnorm : (u : 𝓞 K) * ringOfIntegersQuadraticConj hmin hgen (u : 𝓞 K) = -1) :
    IsTotallyPositive (((θ * (u : 𝓞 K) : 𝓞 K) : K)) ∨
      IsTotallyPositive (-((θ * (u : 𝓞 K) : 𝓞 K) : K)) := by
  have hθK : ((θ : 𝓞 K) : K) ≠ 0 := coe_gen_ne_zero hmin
  have huK : ((u : 𝓞 K) : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr u.ne_zero
  have hu' : ((u : 𝓞 K) : K) * quadraticConj hmin hgen ((u : 𝓞 K) : K) = -1 := by
    simpa only [coe_mul_ringOfIntegersQuadraticConj, map_neg, map_one] using
      congrArg (fun x : 𝓞 K => (x : K)) hnorm
  have hcjK : quadraticConj hmin hgen (((θ * (u : 𝓞 K) : 𝓞 K) : K)) =
      -(θ : K) * quadraticConj hmin hgen ((u : 𝓞 K) : K) := by
    push_cast
    rw [map_mul, quadraticConj_gen hmin hgen]
  have hcjne : quadraticConj hmin hgen ((u : 𝓞 K) : K) ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hu'
    exact zero_ne_one (neg_eq_zero.mp hu'.symm).symm
  have hdiv : (((θ * (u : 𝓞 K) : 𝓞 K) : K)) /
      quadraticConj hmin hgen (((θ * (u : 𝓞 K) : 𝓞 K) : K)) = ((u : 𝓞 K) : K) ^ 2 := by
    rw [hcjK, div_eq_iff (by simp [hθK, hcjne])]
    push_cast
    linear_combination ((θ : K) * ((u : 𝓞 K) : K)) * hu'
  exact isTotallyPositive_or_isTotallyPositive_neg_of_isTotallyPositive_div_quadraticConj
    hmin hgen (by rw [hdiv]; exact isTotallyPositive_sq huK)

/-- A degree-two number field with a real place has two real places and unit rank one. -/
theorem Units.rank_eq_one_of_finrank_eq_two_of_not_isTotallyComplex
    (hfin : Module.finrank ℚ K = 2) (hreal : ¬ IsTotallyComplex K) : Units.rank K = 1 := by
  have hnr : InfinitePlace.nrRealPlaces K ≠ 0 := fun h =>
    hreal (nrRealPlaces_eq_zero_iff.mp h)
  have hsum := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hcard : Fintype.card (InfinitePlace K) = 2 := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  rw [Units.rank, hcard]

/-- **If the unit rank is nonzero and every unit is totally positive up to sign, there is a
totally positive nonsquare unit.** Otherwise the unit group would be generated by `-1` and the
squares, giving the square subgroup index at most two, contrary to
`NumberField.units_sq_index_eq`. -/
theorem exists_unit_isTotallyPositive_and_notMem_square (hrank : Units.rank K ≠ 0)
    (hsign : ∀ u : (𝓞 K)ˣ,
      IsTotallyPositive ((u : 𝓞 K) : K) ∨ IsTotallyPositive (-((u : 𝓞 K) : K))) :
    ∃ ε : (𝓞 K)ˣ, IsTotallyPositive ((ε : 𝓞 K) : K) ∧ ε ∉ Subgroup.square (𝓞 K)ˣ := by
  by_contra hcon
  have hsquare : ∀ ε : (𝓞 K)ˣ, IsTotallyPositive ((ε : 𝓞 K) : K) →
      ε ∈ Subgroup.square (𝓞 K)ˣ := by
    intro ε hε
    by_contra hmem
    exact hcon ⟨ε, hε, hmem⟩
  set H := Subgroup.square (𝓞 K)ˣ with hH
  -- Every unit is a square or `-1` times a square, so the quotient by the squares has at most two
  -- elements.
  have hcover : ∀ u : (𝓞 K)ˣ, QuotientGroup.mk' H u = 1 ∨
      QuotientGroup.mk' H u = QuotientGroup.mk' H (-1) := by
    intro u
    rcases hsign u with h | h
    · exact Or.inl ((QuotientGroup.eq_one_iff _).mpr (hsquare u h))
    · have hmem : (-1 : (𝓞 K)ˣ) * u ∈ H := by
        rw [neg_one_mul]
        exact hsquare (-u) (by simpa using h)
      have h2 : QuotientGroup.mk' H ((-1 : (𝓞 K)ˣ) * u) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hmem
      rw [map_mul] at h2
      refine Or.inr ?_
      calc QuotientGroup.mk' H u = (QuotientGroup.mk' H (-1))⁻¹ := eq_inv_of_mul_eq_one_right h2
        _ = QuotientGroup.mk' H ((-1 : (𝓞 K)ˣ)⁻¹) := (map_inv _ _).symm
        _ = QuotientGroup.mk' H (-1) := by rw [inv_neg_one]
  have hsurj : Function.Surjective
      (![1, QuotientGroup.mk' H (-1)] : Fin 2 → (𝓞 K)ˣ ⧸ H) := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective H x
    rcases hcover u with h | h
    · exact ⟨0, by simpa using h.symm⟩
    · exact ⟨1, by simpa using h.symm⟩
  have hindex : H.index ≤ 2 := by
    rw [Subgroup.index_eq_card]
    simpa using Nat.card_le_card_of_surjective _ hsurj
  rw [hH, NumberField.units_sq_index_eq] at hindex
  have hfour : 2 ^ 2 ≤ 2 ^ (Units.rank K + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at hfour
  omega

end NumberField
