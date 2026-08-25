/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.EssentialImage
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic

/-!
# The anti-equivalence for diagonalizable group schemes

Over a field `k`, a group scheme over `Spec k` is diagonalizable when it is isomorphic to the
spectrum of a finite-type commutative Hopf algebra whose group-like elements span its carrier.
This file identifies that property with the essential image of
`DiagonalizableGroup.schemeFunctor` and packages the resulting anti-equivalence from finitely
generated commutative groups.

The equivalence is contravariant: its source is `FGCommGrpCatᵒᵖ`. Its forward functor recovers
`DiagonalizableGroup.schemeFunctor` after inclusion into all group schemes. Bundled
diagonalizable group schemes automatically expose affineness and local finite type over `Spec k`.

All categories and carriers lie in the universe of `k`, as required by the current
`AlgebraicGeometry.hopfSpec` construction.

## Main declarations

* `TauCeti.DiagonalizableGroup.diagonalizableGroupSchemeProperty`: the coordinate-side object
  property on group schemes over `Spec k`.
* `TauCeti.DiagonalizableGroup.essImage_schemeFunctor`: this property is the essential image of
  the diagonalizable group-scheme functor.
* `TauCeti.DiagonalizableGroup.DiagonalizableGroupSchemeCat`: the corresponding full
  subcategory.
* `TauCeti.DiagonalizableGroup.schemeEquivalence`: the anti-equivalence from finitely generated
  commutative groups.
* `TauCeti.DiagonalizableGroup.schemeEquivalence.functorCompιIso`: the forward functor recovers
  `schemeFunctor` after inclusion.

## References

See Milne, *Algebraic Groups*, Definition 12.7 and Theorems 12.8--12.9.

The equivalence packaging follows
`TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence`, specifically
`commHopfAlgCatOpEquivAffineGroupSchemeCat` and
`commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso`.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

namespace DiagonalizableGroup

open AlgebraicGeometry Opposite

variable (k : Type u) [Field k]

/-- The property of group schemes over `Spec k` that are spectra of finite-type commutative Hopf
algebras spanned by their group-like elements. -/
def diagonalizableGroupSchemeProperty :
    ObjectProperty (Grp (Over (Spec (CommRingCat.of k)))) :=
  (groupLikeSpannedProperty k).op.map
    ((finiteTypeCommHopfAlgProperty k).ι.op ⋙
      AlgebraicGeometry.hopfSpec (CommRingCat.of k))

/-- A group scheme over `Spec k` is diagonalizable exactly when it is isomorphic to the spectrum
of a finite-type commutative Hopf algebra spanned by its group-like elements. -/
@[simp]
theorem diagonalizableGroupSchemeProperty_iff
    (G : Grp (Over (Spec (CommRingCat.of k)))) :
    diagonalizableGroupSchemeProperty k G ↔
      ∃ H : FiniteTypeCommHopfAlgCat.{u, u} k,
        groupLikeSpannedProperty k H ∧
          Nonempty
            ((AlgebraicGeometry.hopfSpec (CommRingCat.of k)).obj (op H.obj) ≅ G) := by
  constructor
  · rintro ⟨H, hH, e⟩
    exact ⟨H.unop, hH, e⟩
  · rintro ⟨H, hH, e⟩
    exact ⟨op H, hH, e⟩

/-- The diagonalizable group schemes are precisely the essential image of the existing
contravariant diagonalizable group-scheme functor. -/
theorem essImage_schemeFunctor :
    (schemeFunctor k).essImage = diagonalizableGroupSchemeProperty k := by
  ext G
  constructor
  · rintro ⟨M, ⟨e⟩⟩
    rw [diagonalizableGroupSchemeProperty_iff]
    refine ⟨(coordinateRingFunctor k).obj M.unop, ?_, ?_⟩
    · rw [← essImage_coordinateRingFunctor k]
      exact (coordinateRingFunctor k).obj_mem_essImage M.unop
    · exact ⟨(schemeFunctorIsoHopfSpec k).symm.app M ≪≫ e⟩
  · rw [diagonalizableGroupSchemeProperty_iff]
    rintro ⟨H, hH, ⟨e⟩⟩
    rw [← essImage_coordinateRingFunctor k] at hH
    obtain ⟨M, ⟨c⟩⟩ := hH
    refine ⟨op M, ⟨?_⟩⟩
    exact (schemeFunctorIsoHopfSpec k).app (op M) ≪≫
      ((AlgebraicGeometry.hopfSpec (CommRingCat.of k)).mapIso
        (((finiteTypeCommHopfAlgProperty k).ι.mapIso c).op.symm)).trans e

/-- The category of diagonalizable group schemes over `Spec k`. -/
abbrev DiagonalizableGroupSchemeCat :=
  (diagonalizableGroupSchemeProperty k).FullSubcategory

/-- A bundled diagonalizable group scheme is affine. -/
instance (G : DiagonalizableGroupSchemeCat k) : IsAffine G.obj.X.left := by
  have hG : (schemeFunctor k).essImage G.obj :=
    (essImage_schemeFunctor k).symm ▸ G.property
  obtain ⟨M, ⟨e⟩⟩ := hG
  apply (IsAffine.iff_of_isIso
    ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom).mp
  exact isAffine_schemeFunctor_obj k M

/-- The structural morphism of a bundled diagonalizable group scheme is locally of finite type. -/
instance (G : DiagonalizableGroupSchemeCat k) : LocallyOfFiniteType G.obj.X.hom := by
  have hG : (schemeFunctor k).essImage G.obj :=
    (essImage_schemeFunctor k).symm ▸ G.property
  obtain ⟨M, ⟨e⟩⟩ := hG
  -- Local finite type is stable under base change, hence invariant under isomorphisms. Install
  -- that consequence at the schemes' universe for the over-category transport lemma.
  let : MorphismProperty.RespectsIso
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  apply (MorphismProperty.over_iso_iff
    (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) ((Grp.forget _).mapIso e)).mp
  exact locallyOfFiniteType_schemeFunctor_obj k M

/-- Finitely generated commutative groups, with arrows reversed, are equivalent to
diagonalizable group schemes over `Spec k`. -/
noncomputable def schemeEquivalence :
    (FGCommGrpCat.{u})ᵒᵖ ≌ DiagonalizableGroupSchemeCat k :=
  (schemeFunctor k).toEssImage.asEquivalence.trans
    (ObjectProperty.fullSubcategoryCongr (essImage_schemeFunctor k))

/-- The forward functor of `schemeEquivalence` is definitionally the composite of the lift to
the essential image and the property-change functor. This private isomorphism isolates that
representation boundary from the public compatibility proof. -/
private noncomputable def schemeEquivalenceFunctorIso :
    (schemeEquivalence k).functor ≅
      (schemeFunctor k).toEssImage ⋙
        ObjectProperty.ιOfLE (essImage_schemeFunctor k).le :=
  Iso.refl _

/-- The forward functor of `schemeEquivalence`, followed by the inclusion into all group schemes,
is the existing diagonalizable group-scheme functor. -/
noncomputable def schemeEquivalence.functorCompιIso :
    (schemeEquivalence k).functor ⋙ (diagonalizableGroupSchemeProperty k).ι ≅
      schemeFunctor k := by
  exact Functor.isoWhiskerRight (schemeEquivalenceFunctorIso k)
      (diagonalizableGroupSchemeProperty k).ι ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (schemeFunctor k).toEssImage
      (ObjectProperty.ιOfLECompιIso _) ≪≫
    (schemeFunctor k).toEssImageCompι

end DiagonalizableGroup

end TauCeti
