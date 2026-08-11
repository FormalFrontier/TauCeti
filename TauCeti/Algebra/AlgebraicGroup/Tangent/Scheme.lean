/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import TauCeti.AlgebraicGeometry.TangentSpace.Affine

/-!
# The Zariski cotangent space at the augmentation point

For a commutative bialgebra, specializing the generic augmented-algebra comparison from
`TauCeti.AlgebraicGeometry.TangentSpace.Affine` to the counit identifies the cotangent space at the
identity of the represented affine monoid with the corresponding Zariski cotangent space. With an
additional Hopf-algebra structure, its `k`-dual is the Hopf-algebra model of `Lie(G)` for the
represented affine group. This file therefore synchronizes the coordinate and scheme tangent-space
models needed by the smoothness and dimension tools in Layer 2 of the ReductiveGroups roadmap.

## Main declarations

* `Bialgebra.augmentationPoint`: the specialization to the counit of a bialgebra.
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
abbrev augmentationPoint : Spec (CommRingCat.of H) :=
  AlgHom.kernelPoint (_root_.Bialgebra.counitAlgHom k H)

/-- The prime ideal of the augmentation point is the augmentation ideal. -/
theorem augmentationPoint_asIdeal :
    (augmentationPoint k H).asIdeal = AugmentationIdeal k H :=
  AlgHom.kernelPoint_asIdeal (_root_.Bialgebra.counitAlgHom k H)

/-- The augmentation point is the pullback of the closed point of the ground field along the
counit. -/
theorem augmentationPoint_eq_comap_closedPoint :
    augmentationPoint k H =
      PrimeSpectrum.comap (_root_.Bialgebra.counitAlgHom k H : H →+* k) (closedPoint k) :=
  AlgHom.kernelPoint_eq_comap_closedPoint (_root_.Bialgebra.counitAlgHom k H)

/-- The ground field is canonically the residue field at the augmentation point. -/
noncomputable def augmentationResidueFieldRingEquiv :
    k ≃+* IsLocalRing.ResidueField
      ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H)) :=
  AlgHom.kernelResidueFieldRingEquiv (_root_.Bialgebra.counitAlgHom k H)

/-- The augmentation residue-field equivalence sends a ground-field element to the residue class
of its image in the stalk. -/
@[simp]
theorem augmentationResidueFieldRingEquiv_apply (r : k) :
    augmentationResidueFieldRingEquiv k H r =
      Ideal.Quotient.mk _
        (algebraMap H ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H))
          (algebraMap k H r)) :=
  AlgHom.kernelResidueFieldRingEquiv_apply (_root_.Bialgebra.counitAlgHom k H) r

/-- The augmentation cotangent space of a commutative bialgebra is canonically the Zariski
cotangent space of its affine spectrum at the augmentation point.

This is the cotangent form of the comparison between counit-valued derivations and the
scheme-theoretic tangent space at the identity. -/
noncomputable def cotangentLinearEquivZariski :
    CotangentSpace k H ≃ₗ[k]
      TauCeti.AlgebraicGeometry.ZariskiCotangentSpace
        (Spec (CommRingCat.of H)) (augmentationPoint k H) :=
  AlgHom.kernelCotangentLinearEquivZariski (_root_.Bialgebra.counitAlgHom k H)

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
            let _ : (AugmentationIdeal k H).IsMaximal :=
              AlgHom.kernelIsMaximal (_root_.Bialgebra.counitAlgHom k H)
            let _ : IsLocalization.AtPrime
                ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H))
                (AugmentationIdeal k H) :=
              AlgHom.kernelStalkIsLocalization (_root_.Bialgebra.counitAlgHom k H)
            rw [← Ideal.mem_under,
              IsLocalization.AtPrime.under_maximalIdeal
                ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H))
                (AugmentationIdeal k H)]
            exact a.2⟩ :=
  AlgHom.kernelCotangentLinearEquivZariski_toCotangent
    (_root_.Bialgebra.counitAlgHom k H) a

/-- The augmentation cotangent comparison intertwines the ground-field action with the native
residue-field action through `augmentationResidueFieldRingEquiv`. -/
@[simp]
theorem cotangentLinearEquivZariski_smul (r : k) (x : CotangentSpace k H) :
    r • cotangentLinearEquivZariski k H x =
      augmentationResidueFieldRingEquiv k H r • cotangentLinearEquivZariski k H x :=
  by
    unfold cotangentLinearEquivZariski augmentationResidueFieldRingEquiv
    exact AlgHom.kernelCotangentLinearEquivZariski_smul
      (_root_.Bialgebra.counitAlgHom k H) r x

/-- The augmentation cotangent space and the Zariski cotangent space at the augmentation point
have the same dimension over the ground field. -/
theorem finrank_cotangentSpace_eq_finrank_zariskiCotangentSpace :
    Module.finrank k (CotangentSpace k H) =
      Module.finrank k
        (TauCeti.AlgebraicGeometry.ZariskiCotangentSpace
          (Spec (CommRingCat.of H)) (augmentationPoint k H)) :=
  AlgHom.finrank_kernelCotangent_eq_finrank_zariskiCotangentSpace
    (_root_.Bialgebra.counitAlgHom k H)

end Bialgebra

end TauCeti
