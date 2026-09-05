/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Product.Properties
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.Dimension

/-!
# Maximal-dimensional families of closed subgroups

Let `H` be the coordinate Hopf algebra of a finite-type affine group over a field, and let
`P` be a family of smooth connected closed subgroups. Suppose a normal member `I` of `P` has
maximal Lie dimension and the scheme-theoretic product of `I` with each member of `P` remains in
`P`. Then `I` contains every other member.

Indeed, multiplying a maximal-dimensional member `I` by another member `J` gives a member that
contains `I`. Dimension maximality then makes the resulting closed immersion an equality, by the
comparison of `TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Smooth.Dimension`. Since the product also
contains `J`, the subgroup represented by `I` contains `J`.

This argument is independent of the additional property defining the family. It is used for the
unipotent radical and is also the dimension-comparison step in the construction of the solvable
radical.

## Main declaration

* `TauCeti.HopfIdeal.le_of_product_of_finrank_maximal`: a normal maximal-dimensional member of a
  family of smooth connected closed subgroups, closed under its products, is greatest.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42 and Sections 5.a, 6.a, 10.a.
* A. Borel, *Linear Algebraic Groups*, Section 11.21.

This supplies the shared maximal-dimension comparison used in Layers 5 and 6 of the
ReductiveGroups roadmap to construct the unipotent and solvable radicals.
-/

public section

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I J : HopfIdeal k H}

/-- A normal maximal-dimensional member of a family of smooth connected closed subgroups contains
every member when its product with each family member remains in the family.

The order on Hopf ideals reverses inclusion of represented closed subgroups, so the conclusion
`I ≤ J` says that the subgroup cut out by `I` contains the one cut out by `J`. -/
theorem le_of_product_of_finrank_maximal
    (P : HopfIdeal k H → Prop)
    (hI_normal : I.IsNormal)
    (connected : ∀ {K : HopfIdeal k H}, P K →
      ConnectedSpace (PrimeSpectrum (H ⧸ K.toIdeal)))
    (smooth : ∀ {K : HopfIdeal k H}, P K →
      Algebra.Smooth k (FiniteTypeCommHopfAlgCat.quotient H K))
    (product : ∀ {L : HopfIdeal k H}, P L →
      P (HopfIdeal.ker
        (CommHopfAlgCat.productMapOfNormal H.obj I L hI_normal).hom))
    (hI : P I)
    (hmax : ∀ K : HopfIdeal k H, P K →
      Module.finrank k
          (Derivation k (H ⧸ K.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ K.toIdeal) k)) ≤
        Module.finrank k
          (Derivation k (H ⧸ I.toIdeal)
            (Bialgebra.CounitAlgebra k (H ⧸ I.toIdeal) k)))
    (hJ : P J) : I ≤ J := by
  let K : HopfIdeal k H :=
    HopfIdeal.ker (CommHopfAlgCat.productMapOfNormal H.obj I J hI_normal).hom
  have hK : P K := product hJ
  have hKI : K ≤ I :=
    CommHopfAlgCat.ker_productMapOfNormal_le_left H.obj I J hI_normal
  have hKI_eq : K = I :=
    eq_of_le_of_finrank_quotientLie_le hKI
      ((smoothCommHopfAlgProperty_iff _).mpr (smooth hK)) (connected hK)
      ((smoothCommHopfAlgProperty_iff _).mpr (smooth hI)) (connected hI) (hmax K hK)
  rw [← hKI_eq]
  exact CommHopfAlgCat.ker_productMapOfNormal_le_right H.obj I J hI_normal

end HopfIdeal

end


end TauCeti
