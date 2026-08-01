/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.FiniteType
public import TauCeti.Algebra.HopfAlgebra.GroupLike.FiniteGeneration

import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation

/-!
# The essential image of diagonalizable coordinate Hopf algebras

Over a field `k`, a finite-type commutative Hopf algebra is the coordinate algebra of a
diagonalizable group exactly when its group-like elements span the whole carrier. This file
identifies that intrinsic object property with the essential image of
`DiagonalizableGroup.coordinateRingFunctor` and packages the resulting equivalence of categories.

The proof reconstructs a group-like-spanned Hopf algebra `H` from its group of group-like elements.
The canonical evaluation map `k[GroupLike k H] → H` is a bialgebra equivalence: spanning gives
surjectivity, while linear independence of group-like elements over a field gives injectivity.
Finite type then implies that `GroupLike k H` is finitely generated. Conversely, the standard
basis elements of every group algebra are group-like and span, and this property is invariant
under bialgebra equivalence.

All categories and carriers in the equivalence lie in the universe of `k`. Applying `Spec`, and
the resulting scheme-side anti-equivalence, are outside the scope of this file.

## Main declarations

* `TauCeti.DiagonalizableGroup.groupLikeSpannedProperty`: the intrinsic object property on
  finite-type commutative Hopf algebras.
* `TauCeti.DiagonalizableGroup.essImage_coordinateRingFunctor`: the essential image of the
  coordinate-ring functor is the group-like-spanned property.
* `TauCeti.DiagonalizableGroup.GroupLikeSpannedCommHopfAlgCat`: the corresponding full
  subcategory.
* `TauCeti.DiagonalizableGroup.coordinateRingEquivalence`: the equivalence from finitely generated
  commutative groups to group-like-spanned finite-type commutative Hopf algebras.
* `TauCeti.DiagonalizableGroup.coordinateRingEquivalence.functorCompιIso`: the forward functor of
  the equivalence recovers the coordinate-ring functor after inclusion.

## References

See Milne, *Algebraic Groups*, Proposition 4.23 and Definition 12.7 with Theorems 12.8--12.9.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace DiagonalizableGroup

variable (k : Type u) [Field k]

/-- The object property selecting finite-type commutative Hopf algebras whose group-like elements
span the whole carrier. -/
def groupLikeSpannedProperty :
    ObjectProperty (FiniteTypeCommHopfAlgCat.{u, u} k) :=
  fun H ↦ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ = ⊤

/-- Membership in the group-like-spanned object property. -/
@[simp]
theorem groupLikeSpannedProperty_iff (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    groupLikeSpannedProperty k H ↔
      Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ = ⊤ :=
  Iff.rfl

/-- The essential image of the finite-type diagonalizable coordinate-ring functor consists
exactly of the finite-type commutative Hopf algebras spanned by their group-like elements. -/
theorem essImage_coordinateRingFunctor :
    (coordinateRingFunctor k).essImage = groupLikeSpannedProperty k := by
  funext H
  apply propext
  constructor
  · rintro ⟨G, ⟨e⟩⟩
    let e' : ((coordinateRingFunctor k).obj G).obj ≅ H.obj :=
      (finiteTypeCommHopfAlgProperty k).ι.mapIso e
    apply (groupLikeSpannedProperty_iff k H).2
    exact (TauCeti.GroupLike.groupLikeSetSpan_eq_top_iff_of_bialgEquiv k
      ((coordinateRingFunctor k).obj G) H (_root_.CommHopfAlgCat.ofIso e')).mp
        (TauCeti.MonoidAlgebra.groupLikeSetSpan_eq_top k G)
  · intro hH
    have hH' := (groupLikeSpannedProperty_iff k H).1 hH
    letI : Group.FG (_root_.GroupLike k H) :=
      TauCeti.GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top k H
        (inferInstanceAs (Algebra.FiniteType k H)) hH'
    let G : FGCommGrpCat.{u} := FGCommGrpCat.of (_root_.GroupLike k H)
    have hspan :
        Submodule.span k
            (Set.range (_root_.GroupLike.val (R := k) (A := H))) = ⊤ :=
      (TauCeti.GroupLike.groupLikeSetSpan_eq_top_iff_span_eq_top k H).1 hH'
    let e : _root_.CommHopfAlgCat.of k (_root_.MonoidAlgebra k (_root_.GroupLike k H)) ≅
        H.obj :=
      _root_.CommHopfAlgCat.isoMk
          (TauCeti.GroupLike.evaluationBialgEquiv k H hspan) ≪≫
        _root_.CommHopfAlgCat.ofIsoSelf H.obj
    exact ⟨G, ⟨ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty k) e⟩⟩

/-- The property of being spanned by group-like elements is invariant under isomorphisms of
finite-type commutative Hopf algebras. -/
instance groupLikeSpannedProperty_isClosedUnderIsomorphisms :
    (groupLikeSpannedProperty k).IsClosedUnderIsomorphisms := by
  rw [← essImage_coordinateRingFunctor k]
  infer_instance

/-- The category of finite-type commutative Hopf algebras spanned by their group-like elements. -/
abbrev GroupLikeSpannedCommHopfAlgCat :=
  (groupLikeSpannedProperty k).FullSubcategory

/-- Finitely generated commutative groups are equivalent to finite-type commutative Hopf
algebras spanned by their group-like elements, via the group-algebra coordinate-ring functor. -/
noncomputable def coordinateRingEquivalence :
    FGCommGrpCat.{u} ≌ GroupLikeSpannedCommHopfAlgCat k :=
  (coordinateRingFunctor k).toEssImage.asEquivalence.trans
    (ObjectProperty.fullSubcategoryCongr (essImage_coordinateRingFunctor k))

/-- The forward functor of `coordinateRingEquivalence` is definitionally the composite of the
lift to the essential image and the property-change functor. This private isomorphism isolates
that representation boundary from the public compatibility proof. -/
private noncomputable def coordinateRingEquivalenceFunctorIso :
    (coordinateRingEquivalence k).functor ≅
      (coordinateRingFunctor k).toEssImage ⋙
        ObjectProperty.ιOfLE (essImage_coordinateRingFunctor k).le :=
  Iso.refl _

/-- The forward functor of `coordinateRingEquivalence`, followed by the inclusion into all
finite-type commutative Hopf algebras, is the coordinate-ring functor. -/
noncomputable def coordinateRingEquivalence.functorCompιIso :
    (coordinateRingEquivalence k).functor ⋙ (groupLikeSpannedProperty k).ι ≅
      coordinateRingFunctor k := by
  exact Functor.isoWhiskerRight (coordinateRingEquivalenceFunctorIso k)
      (groupLikeSpannedProperty k).ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (coordinateRingFunctor k).toEssImage
      (ObjectProperty.ιOfLECompιIso _) ≪≫
    (coordinateRingFunctor k).toEssImageCompι

end DiagonalizableGroup

end TauCeti
