/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Basic

/-!
# Similar semigroups

Transporting a C₀-semigroup `S` on `X` along a continuous linear equivalence `e : X ≃L[ℝ] Y`
gives the C₀-semigroup `t ↦ e ∘ S t ∘ e⁻¹` on `Y`, whose operators are the conjugates
`e.conjContinuousAlgEquiv (S t)`.  Its generator is described in
`TauCeti.Analysis.Semigroups.Generator.Similarity`.

## Main definitions and results

* `TauCeti.Semigroups.StronglyContinuousSemigroup.similar`: the transported semigroup.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.similar_apply_apply` and
  `similar_realOperator_apply`: its operators act by `y ↦ e (S t (e⁻¹ y))`.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section II.2.1.
-/

public section

noncomputable section

open scoped NNReal

namespace TauCeti.Semigroups

namespace StronglyContinuousSemigroup

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- The C₀-semigroup `t ↦ e ∘ S t ∘ e⁻¹` on `Y` obtained by transporting `S` along the continuous
linear equivalence `e : X ≃L[ℝ] Y`. -/
def similar (S : StronglyContinuousSemigroup X) (e : X ≃L[ℝ] Y) :
    StronglyContinuousSemigroup Y where
  toFun t := e.conjContinuousAlgEquiv (S t)
  map_zero' := by
    rw [S.map_zero, ← ContinuousLinearMap.one_def, map_one, ContinuousLinearMap.one_def]
  map_add' s t := by
    rw [S.map_add, ← ContinuousLinearMap.mul_def, map_mul, ContinuousLinearMap.mul_def]
  continuousAt_zero' y :=
    e.continuous.continuousAt.comp (S.continuousAt_zero (e.symm y))

@[simp]
theorem similar_apply_apply (S : StronglyContinuousSemigroup X) (e : X ≃L[ℝ] Y) (t : ℝ≥0)
    (y : Y) : S.similar e t y = e (S t (e.symm y)) := by
  rw [similar]
  exact e.conjContinuousAlgEquiv_apply_apply (S t) y

/-- The real-time operator of the transported semigroup is the conjugate
`e ∘ S.realOperator t ∘ e.symm`. -/
@[simp]
theorem similar_realOperator_apply (S : StronglyContinuousSemigroup X) (e : X ≃L[ℝ] Y) (t : ℝ)
    (y : Y) : (S.similar e).realOperator t y = e (S.realOperator t (e.symm y)) := by
  rw [realOperator_def, realOperator_def, similar_apply_apply]

end StronglyContinuousSemigroup

end TauCeti.Semigroups

end
