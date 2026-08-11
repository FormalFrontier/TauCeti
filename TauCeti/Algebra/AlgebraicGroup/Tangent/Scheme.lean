/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import TauCeti.AlgebraicGeometry.TangentSpace.Basic
public import TauCeti.RingTheory.Ideal.Cotangent.Localization

/-!
# The Zariski cotangent space at the identity of an affine group

For a commutative bialgebra `H` over a field `k`, the counit determines a `k`-rational point of
`Spec H`. Its prime ideal is the augmentation ideal `ker ε`. The stalk of `Spec H` at this point
is the localization of `H` at the augmentation ideal, so localization of cotangent spaces gives
a canonical equivalence

```text
ker(ε) / ker(ε)² ≃ₗ[k] 𝔪ₑ / 𝔪ₑ².
```

The left side is `Bialgebra.CotangentSpace k H`, whose `k`-dual is the Hopf-algebra model of
`Lie(G)`. The right side is the Zariski cotangent space of `Spec H` at the identity. This file
therefore synchronizes the coordinate and scheme tangent-space models needed by the smoothness
and dimension tools in Layer 2 of the ReductiveGroups roadmap.

## Main declarations

* `Bialgebra.augmentationPoint`: the point of `Spec H` cut out by the augmentation ideal.
* `Bialgebra.cotangentLinearEquivZariski`: the augmentation cotangent space is the Zariski
  cotangent space at the augmentation point.
* `Bialgebra.finrank_cotangentSpace_eq_finrank_zariskiCotangentSpace`: equality of their
  dimensions over the ground field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a.
-/

public section

open AlgebraicGeometry IsLocalRing

namespace TauCeti

namespace Bialgebra

universe u v

variable (k : Type u) [Field k]
variable (H : Type v) [CommRing H] [Bialgebra k H]

/-- The point of `Spec H` defined by the counit of a commutative bialgebra. Its prime ideal is the
augmentation ideal `ker ε`. For a Hopf algebra this is the identity point of the represented
affine group. -/
def augmentationPoint : Spec (CommRingCat.of H) :=
  ⟨AugmentationIdeal k H,
    (RingHom.ker_isMaximal_of_surjective (_root_.Bialgebra.counitAlgHom k H).toRingHom
      _root_.Bialgebra.counit_surjective).isPrime⟩

/-- The prime ideal of the augmentation point is the augmentation ideal. -/
@[simp]
theorem augmentationPoint_asIdeal :
    (augmentationPoint k H).asIdeal = AugmentationIdeal k H :=
  (rfl)

/-- The augmentation point is the pullback of the closed point of the ground field along the
counit. -/
theorem augmentationPoint_eq_comap_closedPoint :
    augmentationPoint k H =
      PrimeSpectrum.comap (_root_.Bialgebra.counitAlgHom k H).toRingHom (closedPoint k) := by
  apply PrimeSpectrum.ext
  rw [augmentationPoint_asIdeal, PrimeSpectrum.comap_asIdeal]
  rw [show (closedPoint k).asIdeal = maximalIdeal k from rfl,
    IsLocalRing.maximalIdeal_eq_bot]
  rfl

/-- The augmentation ideal of a bialgebra over a field is canonically maximal. -/
instance augmentationIdealIsMaximal : (AugmentationIdeal k H).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (_root_.Bialgebra.counitAlgHom k H).toRingHom
    _root_.Bialgebra.counit_surjective

/-- The stalk of `Spec H` at the augmentation point is an `H`-algebra through the germ map. -/
noncomputable instance augmentationStalkAlgebra :
    Algebra H ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H)) :=
  StructureSheaf.stalkAlgebra H (augmentationPoint k H)

/-- The stalk at the augmentation point is a `k`-algebra through `k → H`. -/
noncomputable instance augmentationStalkBaseAlgebra :
    Algebra k ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H)) :=
  Algebra.restrictScalars k H _

/-- Scalar extension from `k` through `H` to the stalk at the augmentation point is compatible. -/
instance augmentationStalkIsScalarTower :
    IsScalarTower k H ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H)) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The stalk at the augmentation point is the localization of `H` at its augmentation ideal. -/
instance augmentationStalkIsLocalization :
    IsLocalization.AtPrime
      ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H))
      (AugmentationIdeal k H) := by
  exact StructureSheaf.IsLocalization.to_stalk H (augmentationPoint k H)

/-- The augmentation cotangent space of a commutative bialgebra is canonically the Zariski
cotangent space of its affine spectrum at the augmentation point.

This is the cotangent form of the comparison between counit-valued derivations and the
scheme-theoretic tangent space at the identity. -/
noncomputable def cotangentLinearEquivZariski :
    CotangentSpace k H ≃ₗ[k]
      TauCeti.AlgebraicGeometry.ZariskiCotangentSpace
        (Spec (CommRingCat.of H)) (augmentationPoint k H) :=
  (Ideal.cotangentLocalizationEquiv
    (Rₚ := (Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H))
    (AugmentationIdeal k H)).restrictScalars k

/-- On an element of the augmentation ideal, the cotangent comparison is induced by the map from
the coordinate ring to its stalk at the augmentation point. -/
@[simp]
theorem cotangentLinearEquivZariski_toCotangent (a : AugmentationIdeal k H) :
    cotangentLinearEquivZariski k H
        ((AugmentationIdeal k H).toCotangent a) =
      (maximalIdeal
          ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H))).toCotangent
        ⟨algebraMap H
            ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H)) a,
          by
            rw [← Ideal.mem_under,
              IsLocalization.AtPrime.under_maximalIdeal
                ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H))
                (AugmentationIdeal k H)]
            exact a.2⟩ := by
  exact Ideal.cotangentLocalizationEquiv_toCotangent
    (Rₚ := (Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H))
    (AugmentationIdeal k H) a

/-- The augmentation cotangent space and the Zariski cotangent space at the augmentation point
have the same dimension over the ground field. -/
@[simp]
theorem finrank_cotangentSpace_eq_finrank_zariskiCotangentSpace :
    Module.finrank k (CotangentSpace k H) =
      Module.finrank k
        (TauCeti.AlgebraicGeometry.ZariskiCotangentSpace
          (Spec (CommRingCat.of H)) (augmentationPoint k H)) :=
  (cotangentLinearEquivZariski k H).finrank_eq

end Bialgebra

end TauCeti
