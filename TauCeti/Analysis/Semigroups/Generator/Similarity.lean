/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generator.Basic

/-!
# Similar semigroups

Transporting a C₀-semigroup `S` on `X` along a continuous linear equivalence `e : X ≃L[ℝ] Y`
gives the C₀-semigroup `t ↦ e ∘ S t ∘ e⁻¹` on `Y`.  Its generator is the transported generator:
the domain is the image of `D(A)` under `e`, and the action is `e ∘ A ∘ e⁻¹`.

The first application is a commutation criterion.  A semigroup whose generator commutes with an
invertible operator `J` has `J ∘ S t ∘ J⁻¹` with the same generator, so by uniqueness it agrees
with `S`; this is how complex linearity of a semigroup is read off its generator.

## Main definitions and results

* `TauCeti.Semigroups.StronglyContinuousSemigroup.similar`: the transported semigroup.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.mem_similar_domain_iff`: `y` is in the
  transported generator domain iff `e⁻¹ y` is in the original one.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.similar_generator_apply`: the transported
  generator is `e ∘ A ∘ e⁻¹`.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section II.2.1.
-/

public section

noncomputable section

open scoped NNReal
open Filter

namespace TauCeti.Semigroups

namespace StronglyContinuousSemigroup

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- The C₀-semigroup `t ↦ e ∘ S t ∘ e⁻¹` on `Y` obtained by transporting `S` along the continuous
linear equivalence `e : X ≃L[ℝ] Y`. -/
def similar (S : StronglyContinuousSemigroup X) (e : X ≃L[ℝ] Y) :
    StronglyContinuousSemigroup Y where
  toFun t := (e : X →L[ℝ] Y).comp ((S t).comp (e.symm : Y →L[ℝ] X))
  map_zero' := by
    ext y
    simp
  map_add' s t := by
    ext y
    simp
  continuousAt_zero' y :=
    e.continuous.continuousAt.comp (S.continuousAt_zero (e.symm y))

/-- The operator of the transported semigroup at time `t` is the conjugate `e ∘ S t ∘ e.symm`. -/
theorem similar_apply (S : StronglyContinuousSemigroup X) (e : X ≃L[ℝ] Y) (t : ℝ≥0) :
    S.similar e t = (e : X →L[ℝ] Y).comp ((S t).comp (e.symm : Y →L[ℝ] X)) := by
  rw [similar]
  rfl

@[simp]
theorem similar_apply_apply (S : StronglyContinuousSemigroup X) (e : X ≃L[ℝ] Y) (t : ℝ≥0)
    (y : Y) : S.similar e t y = e (S t (e.symm y)) := by
  rw [similar_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe]

/-- The real-time operator of the transported semigroup is the conjugate
`e ∘ S.realOperator t ∘ e.symm`. -/
@[simp]
theorem similar_realOperator_apply (S : StronglyContinuousSemigroup X) (e : X ≃L[ℝ] Y) (t : ℝ)
    (y : Y) : (S.similar e).realOperator t y = e (S.realOperator t (e.symm y)) := by
  rw [realOperator_def, realOperator_def, similar_apply_apply]

/-- The generator difference quotient of the transported semigroup is the transported difference
quotient of `S`. -/
private theorem similar_genQuot_eq (S : StronglyContinuousSemigroup X) (e : X ≃L[ℝ] Y) (t : ℝ)
    (y : Y) : (1 / t) • ((S.similar e).realOperator t y - y) =
      e ((1 / t) • (S.realOperator t (e.symm y) - e.symm y)) := by
  rw [similar_realOperator_apply, e.map_smul, e.map_sub, e.apply_symm_apply]

/-- `y` lies in the generator domain of the transported semigroup iff `e⁻¹ y` lies in the
generator domain of `S`. -/
@[simp]
theorem mem_similar_domain_iff (S : StronglyContinuousSemigroup X) (e : X ≃L[ℝ] Y) (y : Y) :
    y ∈ (S.similar e).domain ↔ e.symm y ∈ S.domain := by
  rw [mem_domain_iff_tendsto, mem_domain_iff_tendsto]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨e.symm z, ?_⟩
    refine ((e.symm.continuous.tendsto z).comp hz).congr' (Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, similar_genQuot_eq, e.symm_apply_apply]
  · rintro ⟨z, hz⟩
    refine ⟨e z, ?_⟩
    refine ((e.continuous.tendsto z).comp hz).congr' (Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, similar_genQuot_eq]

/-- The generator of the transported semigroup is `e ∘ A ∘ e⁻¹`. -/
theorem similar_generator_apply (S : StronglyContinuousSemigroup X) (e : X ≃L[ℝ] Y) {y : Y}
    (hy : y ∈ (S.similar e).domain) :
    (S.similar e).generator ⟨y, by rw [(S.similar e).generator_domain]; exact hy⟩ =
      e (S.generator ⟨e.symm y, by
        rw [S.generator_domain]
        exact (S.mem_similar_domain_iff e y).mp hy⟩) := by
  apply (S.similar e).generator_eq_of_tendsto hy
  refine ((e.continuous.tendsto _).comp
    (S.generator_tendsto ⟨e.symm y, (S.mem_similar_domain_iff e y).mp hy⟩)).congr'
    (Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, similar_genQuot_eq]

end StronglyContinuousSemigroup

end TauCeti.Semigroups

end
