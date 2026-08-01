/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Basic

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
  (hopfSpec S).toEssImage.asEquivalence.trans
    (ObjectProperty.fullSubcategoryCongr
      (funext fun G => propext (essImage_hopfSpec.trans (affineGroupSchemeProperty_iff G).symm)))

/-- The forward functor of `commHopfAlgCatOpEquivAffineGroupSchemeCat`, followed by the
inclusion of the full subcategory, is `hopfSpec`: the anti-equivalence really does act
by `Spec`. Consumers should transport along this isomorphism (and its `app` components
and naturality squares) rather than unfold the equivalence. -/
noncomputable def commHopfAlgCatOpEquivAffineGroupSchemeCat.functorCompιIso
    (S : CommRingCat.{u}) :
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

end TauCeti
