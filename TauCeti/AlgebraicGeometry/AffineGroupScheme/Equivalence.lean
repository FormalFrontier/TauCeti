/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec

/-!
# Affine group schemes are anti-equivalent to commutative Hopf algebras

Over a commutative ring `S`, the contravariant functor `Spec` is an equivalence from the
opposite of the category of commutative `S`-Hopf algebras onto the category of affine
group schemes over `Spec S`. This is the assembled Layer 0 dictionary of the
reductive-groups roadmap.

Mathlib's `AlgebraicGeometry/Group/Affine.lean` provides the functor
(`AlgebraicGeometry.hopfSpec`), its full faithfulness, and the characterization of its
essential image as the affine group schemes (`AlgebraicGeometry.essImage_hopfSpec`);
this file composes them into the equivalence with the category
`TauCeti.AffineGroupSchemeCat` of the parent file.
-/

public section

namespace TauCeti

open CategoryTheory AlgebraicGeometry Opposite

universe u

/-- `Spec` as an anti-equivalence from commutative `S`-Hopf algebras onto affine group
schemes over `Spec S`. The underlying functor is Mathlib's `AlgebraicGeometry.hopfSpec`,
which is fully faithful with essential image the affine group schemes; the isomorphism
`commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso` records this on the level
of functors, and is the intended interface for computing with the equivalence. -/
noncomputable def commHopfAlgCatOpEquivAffineGroupSchemeCat (S : CommRingCat.{u}) :
    (CommHopfAlgCat S)ᵒᵖ ≌ AffineGroupSchemeCat S :=
  (hopfSpec S).toEssImage.asEquivalence.trans (ObjectProperty.fullSubcategoryCongr
      (funext fun G => propext (essImage_hopfSpec.trans (affineGroupSchemeProperty_iff G).symm)))

/-- The forward functor of `commHopfAlgCatOpEquivAffineGroupSchemeCat`, followed by the
inclusion of the full subcategory, is `hopfSpec`: the anti-equivalence really does act
by `Spec`. Consumers should transport along this isomorphism (and its `app` components
and naturality squares) rather than unfold the equivalence. -/
noncomputable def commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso (S : CommRingCat.{u}) :
    (commHopfAlgCatOpEquivAffineGroupSchemeCat S).functor ⋙
      (affineGroupSchemeProperty S).ι ≅ hopfSpec S := by
  -- The equivalence is built as `toEssImage.asEquivalence.trans (fullSubcategoryCongr _)`,
  -- so its forward functor is, by definition of `Equivalence.trans`, `asEquivalence`, and
  -- `fullSubcategoryCongr`, the composite `toEssImage ⋙ ιOfLE _`. This `change` performs
  -- that unavoidable reduction once, explicitly; the isomorphism is then assembled from
  -- the public whiskering API.
  change ((hopfSpec S).toEssImage ⋙
      ObjectProperty.ιOfLE fun G hG => (affineGroupSchemeProperty_iff G).mpr
        (essImage_hopfSpec.mp hG)) ⋙
      (affineGroupSchemeProperty S).ι ≅ hopfSpec S
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (hopfSpec S).toEssImage (ObjectProperty.ιOfLECompιIso _) ≪≫
    (hopfSpec S).toEssImageCompι

/-- To identify the inverse image of an isomorphism-invariant property of affine group schemes
under the Hopf-algebra/group-scheme anti-equivalence, it suffices to identify that property on
Hopf spectra. -/
theorem objectProperty_inverseImage_commHopfAlgCatOpEquiv
    (R : Type u) [CommRing R]
    (P : ObjectProperty (AffineGroupSchemeCat (CommRingCat.of R)))
    [P.IsClosedUnderIsomorphisms] (Q : ObjectProperty (CommHopfAlgCat.{u} R))
    (h : ∀ H, P ⟨(hopfSpec (CommRingCat.of R)).obj (op H), by
      rw [affineGroupSchemeProperty_iff, hopfSpec_obj_X_left]
      infer_instance⟩ ↔ Q H) :
    P.inverseImage
        (commHopfAlgCatOpEquivAffineGroupSchemeCat (CommRingCat.of R)).functor = Q.op := by
  ext H
  let G : AffineGroupSchemeCat (CommRingCat.of R) :=
    ⟨(hopfSpec (CommRingCat.of R)).obj H, by
      rw [affineGroupSchemeProperty_iff, hopfSpec_obj_X_left]
      infer_instance⟩
  let e : (commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of R)).functor.obj H ≅ G :=
    (affineGroupSchemeProperty (CommRingCat.of R)).ι.preimageIso
      ((commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
        (CommRingCat.of R)).app H)
  rw [ObjectProperty.prop_inverseImage_iff, ObjectProperty.op_iff]
  exact (P.prop_iff_of_iso e).trans (h H.unop)

end TauCeti
