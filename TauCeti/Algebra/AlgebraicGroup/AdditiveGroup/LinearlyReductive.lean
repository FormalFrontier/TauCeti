/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Unipotent
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.LinearlyReductive
import TauCeti.Algebra.Coalgebra.Basic

/-!
# The additive group is not linearly reductive

Over any field the additive group `𝔾ₐ` is unipotent in the strong sense that every nonzero
comodule over its coordinate algebra `k[x]` contains a nonzero fixed vector
(`TauCeti.AdditiveGroup.exists_ne_zero_coact_eq_tmul_one`, Kolchin's theorem for `𝔾ₐ`, which needs
neither algebraic closedness nor finite-dimensionality). That supply of fixed vectors is exactly
what `TauCeti.HopfAlgebra.comul_eq_tmul_one_of_isLinearlyReductive_of_forall_exists_fixed` asks
for, so a linearly reductive `𝔾ₐ` would have `Δ h = h ⊗ 1`, hence `h = ε(h) · 1`, for every `h`.
The coordinate algebra is a polynomial algebra and its coordinate `x` has counit `0`, so `𝔾ₐ` is
not linearly reductive over any field.

This is the worked example that gives the triviality theorem content: unipotent groups other than
the trivial one exist, so complete reducibility genuinely fails for them. It is also the promised
counterexample on the linear-reductivity side of Layer 6 of the ReductiveGroups roadmap, matching
the diagonalizable groups on the positive side.

## Main results

* `TauCeti.AdditiveGroup.not_isLinearlyReductive`: the coordinate algebra of `𝔾ₐ` over a field is
  not linearly reductive.
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

/-- **The additive group is not linearly reductive**, over any field: its coordinate algebra
`k[x]` admits a finite-dimensional representation that is not completely reducible, since
otherwise every element of `k[x]` would be a scalar. -/
theorem not_isLinearlyReductive (k : Type u) [Field k] :
    ¬ Coalgebra.IsLinearlyReductive.{u, u, u} k (SymmetricAlgebra k k) := by
  intro hlr
  have hcomul := HopfAlgebra.comul_eq_tmul_one_of_isLinearlyReductive_of_forall_exists_fixed
    k (SymmetricAlgebra k k) hlr
    (fun _ _ _ _ _ N hN ↦ by
      obtain ⟨w, hwN, hw0⟩ := Subcomodule.ne_bot_iff.mp hN
      obtain ⟨v, hv, hvc⟩ := exists_ne_zero_coact_eq_tmul_one (R := k) (V := N)
        (v := ⟨w, hwN⟩) fun hc ↦ hw0 (congrArg Subtype.val hc)
      exact ⟨v, v.2, fun hc ↦ hv (Subtype.ext hc), Subcomodule.coact_coe_eq_tmul_one N hvc⟩)
    (monomialBasis k 1)
  have hx := Coalgebra.eq_counit_smul_of_comul_eq_tmul hcomul
  have hcounit :
      Coalgebra.counit (R := k) (A := SymmetricAlgebra k k) (monomialBasis k 1) = 0 := by
    rw [← coeff_zero_eq_counit, monomialBasis_apply, coeff_pow]
    norm_num
  rw [hcounit, zero_smul] at hx
  exact (monomialBasis k).ne_zero 1 hx

/-- The object-property form of `TauCeti.AdditiveGroup.not_isLinearlyReductive`. -/
theorem not_linearlyReductiveCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    ¬ linearlyReductiveCommHopfAlgProperty k (coordinateHopfAlgebra k) := fun h ↦
  not_isLinearlyReductive k
    ((linearlyReductiveCommHopfAlgProperty_iff k (coordinateHopfAlgebra k)).mp h)

end AdditiveGroup

end TauCeti
