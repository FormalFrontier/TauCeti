/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Maximal
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Product

/-!
# Maximal-dimensional unipotent-radical candidates

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field. The existing
maximal-dimension construction chooses a connected normal smooth unipotent closed subgroup `U`
whose Lie dimension is at least that of every other such subgroup. The existing product theorem
shows that the scheme-theoretic product `UV` is another candidate containing both `U` and `V`.

The general maximal-dimension theorem for product-closed families now applies: smoothness and
connectedness upgrade equality of tangent-space dimensions to `UV = U`. Consequently `U`
contains every candidate.

## Main declaration

* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.le_of_finrank_maximal`: a
  maximal-dimensional unipotent-radical candidate is the greatest candidate.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 5.a, 6.a, 10.a.
* A. Borel, *Linear Algebraic Groups*, Section 11.21.

This completes the maximal-dimension step in Layer 5, "The unipotent radical", of the
ReductiveGroups roadmap. The shared argument also supplies the corresponding comparison step
for the solvable radical in Layer 6.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal.IsUnipotentRadicalCandidate

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I J : HopfIdeal k H}

/-- A maximal-dimensional unipotent-radical candidate is the greatest candidate.

The order on Hopf ideals reverses inclusion of the represented closed subgroups: `I ≤ J` says
that the subgroup defined by `I` contains the subgroup defined by `J`. -/
theorem le_of_finrank_maximal
    (hI : IsUnipotentRadicalCandidate H I)
    (hmax : ∀ K : HopfIdeal k H, IsUnipotentRadicalCandidate H K →
      Module.finrank k
          (Derivation k (H ⧸ K.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ K.toIdeal) k)) ≤
        Module.finrank k
          (Derivation k (H ⧸ I.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)))
    (hJ : IsUnipotentRadicalCandidate H J) : I ≤ J := by
  apply HopfIdeal.le_of_product_of_finrank_maximal
      (IsUnipotentRadicalCandidate H)
      hI.isNormal
      (fun hK ↦
        geometricallyConnectedCommHopfAlgProperty.connectedSpace k _ hK.geometricallyConnected)
      (fun hK ↦
        ((smoothUnipotentCommHopfAlgProperty_iff k
          (FiniteTypeCommHopfAlgCat.quotient H _)).mp hK.smoothUnipotent).1)
      (fun hK ↦ hI.productOfNormal hK)
      hI hmax hJ

end HopfIdeal.IsUnipotentRadicalCandidate

end

end TauCeti
