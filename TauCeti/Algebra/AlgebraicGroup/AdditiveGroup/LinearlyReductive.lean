/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.LinearlyReductive

/-!
# The additive group is not linearly reductive

Over an algebraically closed field the additive group `𝔾ₐ` is smooth, of finite type, and all of
its points are unipotent, so a linearly reductive `𝔾ₐ` would be the trivial group by
`TauCeti.HopfAlgebra.counitBialgEquivOfSmoothOfIsLinearlyReductiveOfForallIsUnipotentPoint`. Its
coordinate algebra is a polynomial algebra, hence not the ground field, so `𝔾ₐ` is not linearly
reductive.

This is the worked example that gives the triviality theorem content: unipotent groups other than
the trivial one exist, so complete reducibility genuinely fails for them. It is also the promised
counterexample on the linear-reductivity side of Layer 6 of the ReductiveGroups roadmap, matching
the diagonalizable groups on the positive side.

## Main results

* `TauCeti.AdditiveGroup.not_isLinearlyReductive`: the coordinate algebra of `𝔾ₐ` over an
  algebraically closed field is not linearly reductive.
* `TauCeti.AdditiveGroup.not_linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra`: the same
  statement for the object property.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2 and §8.3.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
-/

public section

namespace TauCeti

namespace AdditiveGroup

universe u

/-- **The additive group is not linearly reductive.** Over an algebraically closed field its
coordinate algebra `k[x]` admits a finite-dimensional representation that is not completely
reducible, since otherwise every element of `k[x]` would be a scalar. -/
theorem not_isLinearlyReductive (k : Type u) [Field k] [IsAlgClosed k] :
    ¬ Coalgebra.IsLinearlyReductive.{u, u, u} k (SymmetricAlgebra k k) := by
  intro hlr
  have hx := HopfAlgebra.eq_counit_smul_one_of_isLinearlyReductive_of_forall_isUnipotentPoint
    k (SymmetricAlgebra k k) hlr (fun g ↦ isUnipotentPoint k g) (monomialBasis k 1)
  have hcounit :
      Coalgebra.counit (R := k) (A := SymmetricAlgebra k k) (monomialBasis k 1) = 0 := by
    rw [← coeff_zero_eq_counit, monomialBasis_apply, coeff_pow]
    norm_num
  rw [hcounit, zero_smul] at hx
  exact (monomialBasis k).ne_zero 1 hx

/-- The object-property form of `TauCeti.AdditiveGroup.not_isLinearlyReductive`. -/
theorem not_linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] [IsAlgClosed k] :
    ¬ linearlyReductiveCommHopfAlgProperty k (coordinateHopfAlgebra k) := fun h ↦
  not_isLinearlyReductive k
    ((linearlyReductiveCommHopfAlgProperty_iff k (coordinateHopfAlgebra k)).mp h)

end AdditiveGroup

end TauCeti
