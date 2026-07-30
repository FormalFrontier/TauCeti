/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.ClassGroup.ElementaryTwoQuotient
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Basic
public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Norm

/-!
# Quadratic conjugation acts on the class group by inversion

For a quadratic number field `K = ℚ(√d)`, `TauCeti.NumberField.ringOfIntegersQuadraticConj` is the
ring automorphism `σ : 𝓞 K ≃+* 𝓞 K` restricting field conjugation. Its induced action on the class
group `Cl(𝓞 K)` is an involution (recorded in `Quadratic/Conjugation/Basic.lean`); this file
sharpens the involution to **inversion**, the genus-theoretic mechanism `I · σI` principal, and
concludes that `σ` therefore acts trivially on the maximal elementary-2 quotient `Cl(𝓞 K)/Cl(𝓞 K)²`.

The reduction has two moves. First the general **bridge** `ClassGroup.mulEquiv_mk0` (in
`ClassGroup/Equiv.lean`): for a ring isomorphism `f : R ≃+* R'` of Dedekind domains,
`ClassGroup.mulEquiv f` sends the class of an ideal to the class of its pushforward `Ideal.map f`.
Second the **inversion**: the ideal class of `σI` is the inverse of the class of `I` because
`I · σI` is principal — the norm-principality theorem
`isPrincipal_mul_map_ringOfIntegersQuadraticConj` (in `Quadratic/Conjugation/Norm.lean`) combined
with `ClassGroup.mk0_eq_mk0_inv_iff`. The generic fact that pointwise inversion is trivial on the
elementary-2 quotient
(`TauCeti.ClassGroup.elementaryTwoQuotientCongr_apply_eq_self_of_apply_eq_inv`) then gives the
identity on `Cl/Cl²`.

This is Layer 3 of the multiquadratic roadmap: the summit isomorphism
`Gal(K_gen/K) ≅ Cl(K)/Cl(K)²` factors the conjugation action through its triviality on `Cl/Cl²`.

See D. A. Cox, *Primes of the Form x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*, for the
classical genus theory behind the inversion action of conjugation on the class group.

## Main results

* `TauCeti.NumberField.mulEquiv_ringOfIntegersQuadraticConj_apply_eq_inv`: quadratic conjugation
  acts on `Cl(𝓞 K)` by inversion.
* `TauCeti.NumberField.elementaryTwoQuotientCongr_ringOfIntegersQuadraticConj_apply_eq_self`: hence
  quadratic conjugation is the identity on the maximal elementary-2 quotient `Cl(𝓞 K)/Cl(𝓞 K)²`.
-/

public section

open scoped nonZeroDivisors

open NumberField Polynomial

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **Quadratic conjugation acts on the class group by inversion.** The induced action of quadratic
conjugation `σ = ringOfIntegersQuadraticConj` on `Cl(𝓞 K)` sends each class to its inverse, because
`I · σI` is principal (`isPrincipal_mul_map_ringOfIntegersQuadraticConj`). This sharpens
`mulEquiv_ringOfIntegersQuadraticConj_involutive` from an involution to inversion. -/
theorem mulEquiv_ringOfIntegersQuadraticConj_apply_eq_inv (hmin : minpoly ℤ θ = X ^ 2 - C d)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (C : ClassGroup (𝓞 K)) :
    ClassGroup.mulEquiv (ringOfIntegersQuadraticConj hmin hgen) C = C⁻¹ := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective C
  rw [ClassGroup.mulEquiv_mk0, ClassGroup.mk0_eq_mk0_inv_iff]
  obtain ⟨x, hx⟩ :=
    (isPrincipal_mul_map_ringOfIntegersQuadraticConj hmin hgen (I : Ideal (𝓞 K))).principal
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
@[simp] theorem elementaryTwoQuotientCongr_ringOfIntegersQuadraticConj_apply_eq_self
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤)
    (x : TauCeti.ClassGroup.ElementaryTwoQuotient (𝓞 K)) :
    TauCeti.ClassGroup.elementaryTwoQuotientCongr
      (ClassGroup.mulEquiv (ringOfIntegersQuadraticConj hmin hgen)) x = x :=
  TauCeti.ClassGroup.elementaryTwoQuotientCongr_apply_eq_self_of_apply_eq_inv
    (ClassGroup.mulEquiv (ringOfIntegersQuadraticConj hmin hgen))
    (mulEquiv_ringOfIntegersQuadraticConj_apply_eq_inv hmin hgen) x

end TauCeti.NumberField
