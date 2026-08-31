/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Maximal
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Product

/-!
# Maximal-dimensional solvable-radical candidates

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field. A
solvable-radical candidate is a connected normal smooth solvable closed subgroup. Such candidates
are closed under scheme-theoretic multiplication images, so the general maximal-dimension theorem
for product-closed families applies: a candidate of maximal Lie dimension contains every other
candidate.

## Main declaration

* `TauCeti.HopfIdeal.IsSolvableRadicalCandidate.le_of_finrank_maximal`: a
  maximal-dimensional solvable-radical candidate is the greatest candidate.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 5.a, 6.a, 10.a.
* A. Borel, *Linear Algebraic Groups*, Section 11.21.

The specialization follows the formal pattern of
`TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Maximal`, using the shared theorem in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Maximal`.

This is the maximal-dimension comparison used to construct the solvable radical in Layer 6,
"Reductive and semisimple groups", of the ReductiveGroups roadmap.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal.IsSolvableRadicalCandidate

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I J : HopfIdeal k H}

/-- A maximal-dimensional solvable-radical candidate is the greatest candidate.

The order on Hopf ideals reverses inclusion of represented closed subgroups: `I ≤ J` says
that the subgroup cut out by `I` contains the subgroup cut out by `J`. -/
theorem le_of_finrank_maximal
    (hI : IsSolvableRadicalCandidate H I)
    (hmax : ∀ K : HopfIdeal k H, IsSolvableRadicalCandidate H K →
      Module.finrank k
          (Derivation k (H ⧸ K.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ K.toIdeal) k)) ≤
        Module.finrank k
          (Derivation k (H ⧸ I.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)))
    (hJ : IsSolvableRadicalCandidate H J) : I ≤ J := by
  apply HopfIdeal.le_of_product_of_finrank_maximal
      (IsSolvableRadicalCandidate H)
      hI.isNormal
      (fun hK ↦
        geometricallyConnectedCommHopfAlgProperty.connectedSpace k _ hK.geometricallyConnected)
      (fun hK ↦ hK.smooth)
      (fun hK ↦ hI.productOfNormal hK)
      hI hmax hJ

end HopfIdeal.IsSolvableRadicalCandidate

end

end TauCeti
