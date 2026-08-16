/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import TauCeti.Algebra.Bialgebra.Augmentation
public import TauCeti.AlgebraicGeometry.TangentSpace.Affine

/-!
# The Zariski cotangent space at the augmentation point

For a commutative bialgebra, specializing the generic augmented-algebra comparison from
`TauCeti.AlgebraicGeometry.TangentSpace.Affine` to the counit identifies the cotangent space at the
identity of the represented affine monoid with the corresponding Zariski cotangent space. With an
additional Hopf-algebra structure, its `k`-dual is the Hopf-algebra model of `Lie(G)` for the
represented affine group.

## Main declarations

* `Bialgebra.cotangentLinearEquivZariski`: the augmentation cotangent space is the Zariski
  cotangent space at the augmentation point.
* `Bialgebra.finrank_cotangentSpace_eq_finrank_zariskiCotangentSpace`: equality of their
  dimensions over the ground field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a.
-/

public section

open AlgebraicGeometry IsLocalRing

namespace TauCeti.Bialgebra

universe u v

variable (k : Type u) [Field k]
variable (H : Type v) [CommRing H] [Bialgebra k H]

/-- The augmentation cotangent space of a commutative bialgebra is canonically the Zariski
cotangent space of its affine spectrum at the augmentation point. -/
noncomputable def cotangentLinearEquivZariski :
    CotangentSpace k H ≃ₗ[k]
      TauCeti.AlgebraicGeometry.ZariskiCotangentSpace
        (Spec (CommRingCat.of H)) (augmentationPoint k H) :=
  AlgHom.kernelCotangentLinearEquivZariski (_root_.Bialgebra.counitAlgHom k H)

/-- On an element of the augmentation ideal, the cotangent comparison is induced by the map from
the coordinate ring to its stalk at the augmentation point. -/
@[simp]
theorem cotangentLinearEquivZariski_toCotangent (a : AugmentationIdeal k H) :
    cotangentLinearEquivZariski k H ((AugmentationIdeal k H).toCotangent a) =
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

/-- The augmentation cotangent space and the Zariski cotangent space at the augmentation point
have the same dimension over the ground field. -/
theorem finrank_cotangentSpace_eq_finrank_zariskiCotangentSpace :
    Module.finrank k (CotangentSpace k H) =
      Module.finrank k
        (TauCeti.AlgebraicGeometry.ZariskiCotangentSpace
          (Spec (CommRingCat.of H)) (augmentationPoint k H)) :=
  AlgHom.finrank_kernelCotangent_eq_finrank_zariskiCotangentSpace
    (_root_.Bialgebra.counitAlgHom k H)

end TauCeti.Bialgebra
