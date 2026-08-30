/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DominantCone
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Denominator.Reflection
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Numerator

public section

/-!
# The Weyl denominator identity

The **Weyl denominator identity** is the equality

`∏_{α > 0} (1 - e^{-α}) = ∑_{w ∈ W} sgn(w) e^{w ⬝ 0}`

in the integral group algebra `ℤ[M]` of the weight space of a root system: the Weyl denominator
`TauCeti.weylDenominator` is the Weyl numerator `TauCeti.weylNumerator` of the weight `0`. Written
without the dot action `w ⬝ 0 = w(ρ) - ρ` it is the familiar
`∏_{α>0}(1 - e^{-α}) = ∑_w sgn(w) e^{w(ρ) - ρ}`, or, after multiplying by `e^{ρ}`, the symmetric
form `∏_{α>0}(e^{α/2} - e^{-α/2}) = ∑_w sgn(w) e^{w(ρ)}`.

It is the case `λ = 0` of the Weyl character formula, whose right-hand side is the numerator of a
dominant weight; the formula divides by this identity, so the identity is proved first and on its
own, with no representation theory involved.

## The argument

The two sides are compared coefficient by coefficient, and the dot orbit of `0` separates the two
cases.

* **On the orbit.** The coefficient of `N(0)` at `w ⬝ 0` is `sgn(w)`, because the dot orbit of the
  dominant weight `0` is free. The coefficient of `Δ` there is the same: `Δ` is alternating for the
  dot action (`TauCeti.coeff_weylDenominator_dotAction`) and its constant term is `1`
  (`TauCeti.coeff_weylDenominator_zero`: the empty set is the only set of positive roots summing
  to `0`).
* **Off the orbit.** `N(0)` vanishes there by its support statement, and so must `Δ`. Suppose not,
  and move the weight by the dot action into the dominant region, which changes the coefficient
  only by a sign; a coefficient of `Δ` on a dot-action wall vanishes
  (`TauCeti.coeff_weylDenominator_eq_zero_of_coroot'_eq_neg_one`), so the `ρ`-shift of the moved
  weight is *strictly* dominant. Now the geometric heart of the identity applies: an exponent of
  `Δ` is `-ν` for a sum `ν` of positive roots, strict dominance of `ρ - ν` bounds every
  `⟨ν, αᵢ^∨⟩` above by `1`, these pairings are integers, and the only antidominant member of the
  positive root cone is `0` (`TauCeti.eq_zero_of_mem_posRootCone_of_forall_coroot'_nonpos`). So the
  moved weight is `0`, which does lie on the orbit — a contradiction.

## Main results

* `TauCeti.coeff_weylDenominator_zero`: the constant term of `Δ` is `1`.
* `TauCeti.weylDenominator_eq_weylNumerator_zero`: **the Weyl denominator identity**, `Δ = N(0)`.
* `TauCeti.support_coeff_weylDenominator` and `TauCeti.card_support_coeff_weylDenominator`:
  consequently `Δ` is supported on the dot orbit of `0` and has exactly `|W|` terms.

## References

This is the "Weyl denominator identity, proved combinatorially" step of Layer 6 ("the Weyl
character, dimension, and Kostant formulas") of
`TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24.3.
* J.-P. Serre, *Complex Semisimple Lie Algebras*, Ch. VII, §7.
-/

namespace TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N) [Finite ι] [CharZero R] (b : P.Base)

/-- **The constant term of the Weyl denominator is `1`.** Expanding `∏_{α>0}(1 - e^{-α})` indexes
the terms by the sets of positive roots, and the empty set is the only one whose sum vanishes. -/
@[simp]
theorem coeff_weylDenominator_zero : (weylDenominator P b).coeff 0 = 1 := by
  classical
  simp only [weylDenominator_eq_sum_powerset, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single]
  refine (Finset.sum_eq_single_of_mem (∅ : Finset ι) (Finset.empty_mem_powerset _) ?_).trans ?_
  · intro T hT hTne
    have hsum : ∑ i ∈ T, P.root i ≠ 0 :=
      sum_root_ne_zero_of_mem_posRoots P b (Finset.nonempty_iff_ne_empty.mpr hTne)
        fun i hi => (mem_posRootsFinset P b i).mp (Finset.mem_powerset.mp hT hi)
    exact Finsupp.single_eq_of_ne (Ne.symm (neg_ne_zero.mpr hsum))
  · simp

section Cone

variable [LinearOrder R] [IsStrictOrderedRing R] [Invertible (2 : R)] [P.IsCrystallographic]
  [P.IsReduced] [P.IsRootSystem]

/-- The Weyl denominator vanishes at a weight whose `ρ`-shift is strictly dominant, unless that
weight is `0`.

An exponent of `Δ` is minus a sum `ν` of positive roots, so strict dominance of `ρ - ν` bounds
every `⟨ν, αᵢ^∨⟩` above by `1`; these pairings are integers, hence nonpositive, and the only
antidominant member of the positive root cone is `0`. -/
private theorem eq_zero_of_coeff_weylDenominator_ne_zero {y : M}
    (hy : (weylDenominator P b).coeff y ≠ 0)
    (hdom : y + weylVector P b ∈ openDominantChamber P b) : y = 0 := by
  obtain ⟨T, hT, hyT⟩ : ∃ T ⊆ posRootsFinset P b, y = -∑ i ∈ T, P.root i := by
    by_contra hcon
    push Not at hcon
    exact hy (coeff_weylDenominator_eq_zero P b hcon)
  have hcone : (∑ i ∈ T, P.root i) ∈ posRootCone P b :=
    AddSubmonoid.sum_mem _ fun i hi =>
      root_mem_posRootCone_of_mem_posRoots P b ((mem_posRootsFinset P b i).mp (hT hi))
  have hzero : ∑ i ∈ T, P.root i = 0 := by
    refine eq_zero_of_mem_posRootCone_of_forall_coroot'_nonpos b hcone fun i hi => ?_
    obtain ⟨m, hm⟩ := exists_intCast_eq_coroot'_of_mem_posRootCone P b hcone i
    have hlt : P.coroot' i (∑ j ∈ T, P.root j) < 1 := by
      have h0 := (mem_openDominantChamber P b _).mp hdom i hi
      rw [coroot'_add_weylVector P b hi, hyT, map_neg] at h0
      linarith
    rw [hm] at hlt ⊢
    have hm1 : m < 1 := by exact_mod_cast hlt
    exact_mod_cast (by omega : m ≤ 0)
  rw [hyT, hzero, neg_zero]

end Cone

section Identity

variable [LinearOrder R] [IsStrictOrderedRing R] [Invertible (2 : R)] [P.IsCrystallographic]
  [P.IsReduced] [P.flip.IsReduced] [P.IsRootSystem] [Fintype P.weylGroup]

/-- **The Weyl denominator identity**: the Weyl denominator is the Weyl numerator of the weight
`0`,

`∏_{α > 0} (1 - e^{-α}) = ∑_{w ∈ W} sgn(w) e^{w ⬝ 0}`,

an identity in the integral group algebra of the weight space. Written without the dot action, the
right-hand side is `∑_{w ∈ W} sgn(w) e^{w(ρ) - ρ}`.

This is the case `λ = 0` of the Weyl character formula, in which the character of the trivial
module is `1`. -/
theorem weylDenominator_eq_weylNumerator_zero :
    weylDenominator P b = weylNumerator P b 0 := by
  refine AddMonoidAlgebra.coeff_inj.mp (Finsupp.ext fun x => ?_)
  by_cases hx : ∃ v : P.weylGroup, dotAction P b v 0 = x
  · -- On the dot orbit of `0` both sides have the sign of the translating element.
    obtain ⟨v, rfl⟩ := hx
    rw [coeff_weylDenominator_dotAction, coeff_weylDenominator_zero, mul_one,
      coeff_weylNumerator_dotAction P b (zero_mem_dominantChamber P b) v]
  · -- Off the dot orbit of `0` the numerator vanishes; so must the denominator.
    push Not at hx
    rw [coeff_weylNumerator_eq_zero P b hx]
    by_contra hne
    obtain ⟨w, hw⟩ := exists_mem_dominantChamber P b (x + weylVector P b)
    have hyd : dotAction P b w x + weylVector P b ∈ dominantChamber P b := by
      rw [dotAction_add_weylVector]
      exact hw
    have hyne : (weylDenominator P b).coeff (dotAction P b w x) ≠ 0 := by
      rw [coeff_weylDenominator_dotAction]
      exact mul_ne_zero (by exact_mod_cast Units.ne_zero (weylSign P b w)) hne
    -- A coefficient on a dot-action wall vanishes, so the `ρ`-shift is *strictly* dominant.
    have hopen : dotAction P b w x + weylVector P b ∈ openDominantChamber P b := by
      rw [mem_openDominantChamber]
      intro i hi
      rcases lt_or_eq_of_le ((mem_dominantChamber P b _).mp hyd i hi) with h | h
      · exact h
      · rw [coroot'_add_weylVector P b hi] at h
        exact absurd (coeff_weylDenominator_eq_zero_of_coroot'_eq_neg_one P b hi
          (by linarith)) hyne
    exact hx w⁻¹ (by
      rw [← eq_zero_of_coeff_weylDenominator_ne_zero P b hyne hopen, dotAction_inv_dotAction])

/-- **The Weyl denominator is supported exactly on the dot orbit of `0`**, one term for each
element of the Weyl group. -/
theorem support_coeff_weylDenominator [DecidableEq M] :
    (weylDenominator P b).coeff.support
      = Finset.univ.image fun w : P.weylGroup => dotAction P b w 0 := by
  rw [weylDenominator_eq_weylNumerator_zero]
  exact support_coeff_weylNumerator P b (zero_mem_dominantChamber P b)

/-- **The Weyl denominator has exactly `|W|` terms.** Expanding the product over the positive roots
gives `2^{|Φ⁺|}` terms, which collapse to one for each element of the Weyl group. -/
theorem card_support_coeff_weylDenominator :
    (weylDenominator P b).coeff.support.card = Fintype.card P.weylGroup := by
  rw [weylDenominator_eq_weylNumerator_zero]
  exact card_support_coeff_weylNumerator P b (zero_mem_dominantChamber P b)

end Identity

end TauCeti
