/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ExponentialSlope
public import TauCeti.Analysis.Normed.Operator.LinearPMap.Shift
public import TauCeti.Analysis.Semigroups.ExponentialShift
public import TauCeti.Analysis.Semigroups.Generator.Basic

/-!
# Generators of exponentially shifted semigroups

The exponentially shifted semigroup `t ↦ exp (-omega t) S(t)` has the same generator domain as
`S`, and its generator is `A - omega I`.  This identifies the shift used to move semigroup growth
bounds with the scalar shift used in unbounded-resolvent hypotheses.

## Main result

* `TauCeti.Semigroups.StronglyContinuousSemigroup.generator_expShift`: the generator of
  `exp (-omega t) S(t)` is `A - omega I`.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section II.1.
-/

public section

noncomputable section

namespace TauCeti.Semigroups.StronglyContinuousSemigroup

open Filter

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Exponentially shifting a semigroup shifts the limit of a generator difference quotient by
`-omega I`. -/
private theorem tendsto_expShift_genQuot (S : StronglyContinuousSemigroup X) (omega : ℝ)
    {x Ax : X}
    (hgen : Tendsto (fun t : ℝ => (1 / t) • (S.realOperator t x - x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds Ax)) :
    Tendsto (fun t : ℝ => (1 / t) • ((S.expShift omega).realOperator t x - x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Ax - omega • x)) := by
  have hexp : Tendsto (fun t : ℝ => Real.exp (-(omega * t)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hcont : ContinuousAt (fun t : ℝ => Real.exp (-(omega * t))) 0 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hconst : Tendsto (fun _ : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (nhds x) :=
    tendsto_const_nhds
  have hshift := (hexp.smul hgen).add
    ((tendsto_exp_mul_sub_one_div (-omega)).smul hconst)
  have hshift' : Tendsto
      (fun t : ℝ => Real.exp (-(omega * t)) •
          ((1 / t) • (S.realOperator t x - x)) +
        ((Real.exp (-(omega * t)) - 1) / t) • x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Ax - omega • x)) := by
    simpa only [one_smul, neg_smul, sub_eq_add_neg, neg_mul] using hshift
  refine hshift'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [S.expShift_realOperator_apply_of_nonneg omega t ht.le]
  module

/-- A vector in `D(A)` remains in the generator domain after exponentially shifting the
semigroup, and the new generator acts as `A - omega I` there. -/
private theorem subScalar_generator_le_generator_expShift
    (S : StronglyContinuousSemigroup X) (omega : ℝ) :
    LinearPMap.subScalar S.generator omega ≤ (S.expShift omega).generator := by
  have hmem : ∀ x, x ∈ (LinearPMap.subScalar S.generator omega).domain →
      x ∈ (S.expShift omega).generator.domain := by
    intro x hx
    have hxS : x ∈ S.domain := by simpa [S.generator_domain] using hx
    rw [(S.expShift omega).generator_domain, (S.expShift omega).mem_domain_iff_tendsto]
    exact ⟨_, tendsto_expShift_genQuot S omega (S.generator_tendsto ⟨x, hxS⟩)⟩
  refine ⟨hmem, ?_⟩
  intro x y hxy
  let y' : (S.expShift omega).generator.domain := ⟨x, hmem x x.property⟩
  have hy' : y' = y := Subtype.ext hxy
  rw [← hy']
  rw [LinearPMap.subScalar_apply]
  exact ((S.expShift omega).generator_eq_of_tendsto
    (by simpa [(S.expShift omega).generator_domain] using y'.property)
    (tendsto_expShift_genQuot S omega (S.generator_tendsto
      ⟨x, by simpa [S.generator_domain] using x.property⟩))).symm

/-- The generator of the exponentially shifted semigroup `exp (-omega t) S(t)` is
`A - omega I`, where `A` is the generator of `S`. -/
@[simp]
theorem generator_expShift (S : StronglyContinuousSemigroup X) (omega : ℝ) :
    (S.expShift omega).generator = LinearPMap.subScalar S.generator omega := by
  have hforward := subScalar_generator_le_generator_expShift S omega
  have hback := subScalar_generator_le_generator_expShift (S.expShift omega) (-omega)
  have hback' : (S.expShift omega).generator.domain ≤ S.generator.domain := by
    simpa using hback.1
  have hforward' : S.generator.domain ≤ (S.expShift omega).generator.domain := by
    rw [← LinearPMap.subScalar_domain S.generator omega]
    exact hforward.1
  have hdomain : (LinearPMap.subScalar S.generator omega).domain =
      (S.expShift omega).generator.domain := by
    rw [LinearPMap.subScalar_domain]
    exact le_antisymm hforward' hback'
  exact (LinearPMap.eq_of_le_of_domain_eq hforward hdomain).symm

end TauCeti.Semigroups.StronglyContinuousSemigroup

end
