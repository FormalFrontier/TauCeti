/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.Bialgebra.GroupLike.Map

/-!
# Closed subgroups of diagonalizable affine groups

A finite-type commutative Hopf algebra over a field is the coordinate algebra of a
diagonalizable group exactly when its group-like elements span it. This condition passes to a
Hopf quotient: the quotient morphism is surjective and sends every group-like element to a
group-like element, so the images of the original spanning family span the quotient.

Contravariantly, a Hopf ideal cuts out a closed subgroup of the represented affine group. Thus
the main result is the coordinate-algebra form of the fact that every closed subgroup of a
diagonalizable affine group is diagonalizable.

## Main declarations

* `TauCeti.DiagonalizableGroup.groupLikeSpannedProperty.of_surjective`: a surjective morphism of
  finite-type commutative Hopf algebras preserves the diagonalizable coordinate property.
* `TauCeti.DiagonalizableGroup.groupLikeSpannedProperty.quotient`: every Hopf quotient of a
  diagonalizable coordinate algebra is again diagonalizable.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.9.

This advances Layer 4, "Diagonalizable groups and groups of multiplicative type", of the
ReductiveGroups roadmap. It also supplies the closed-subgroup classification used in Layer 6 to
show that smooth unipotent closed subgroups of tori are trivial, on the way to proving that tori
are reductive.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace DiagonalizableGroup.groupLikeSpannedProperty

variable (k : Type u) [Field k]

/-- A surjective morphism of finite-type commutative Hopf algebras preserves spanning by
group-like elements. Contravariantly, this is closure of diagonalizable affine groups under
closed subgroups presented by a surjective coordinate morphism. -/
theorem of_surjective (H K : FiniteTypeCommHopfAlgCat.{u, u} k) (f : H ⟶ K)
    (hf : Function.Surjective (FiniteTypeCommHopfAlgCat.toBialgHom f))
    (hH : DiagonalizableGroup.groupLikeSpannedProperty k H) :
    DiagonalizableGroup.groupLikeSpannedProperty k K := by
  rw [DiagonalizableGroup.groupLikeSpannedProperty_iff] at hH ⊢
  exact GroupLike.groupLikeSetSpan_eq_top_of_surjective
    (FiniteTypeCommHopfAlgCat.toBialgHom f) hf hH

/-- Every Hopf quotient of a finite-type diagonalizable coordinate algebra is again a
diagonalizable coordinate algebra. Contravariantly, every closed subgroup cut out by a Hopf ideal
in a diagonalizable affine group is diagonalizable. -/
theorem quotient (H : FiniteTypeCommHopfAlgCat.{u, u} k) (I : HopfIdeal k H)
    (hH : DiagonalizableGroup.groupLikeSpannedProperty k H) :
    DiagonalizableGroup.groupLikeSpannedProperty k
      (FiniteTypeCommHopfAlgCat.quotient H I) := by
  apply of_surjective k H (FiniteTypeCommHopfAlgCat.quotient H I)
    (FiniteTypeCommHopfAlgCat.mkQuotient H I) _ hH
  exact CommHopfAlgCat.mkQuotient_surjective H.obj I

end DiagonalizableGroup.groupLikeSpannedProperty

end TauCeti
