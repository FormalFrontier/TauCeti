/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented

/-!
# Reduced deconcatenation is coassociative

`TauCeti.ReducedTensorWords.deconcatenation` cuts a nonempty tensor word at every nontrivial
position. This file proves that it is coassociative by including a reduced word into
`TauCeti.TensorWords`, using coassociativity of full deconcatenation there, and projecting every
tensor factor back to positive length. The two degenerate cuts contain an empty-word factor and
therefore vanish under the projection, leaving exactly reduced deconcatenation.

## Main results

* `TauCeti.ReducedTensorWords.deconcatenation_coassoc`: reduced deconcatenation is coassociative.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uM

namespace TauCeti

namespace ReducedTensorWords

variable (R : Type uR) {M : Type uM} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (M)

/-- Projecting all three factors after iterating full deconcatenation on the left recovers the
corresponding iteration of reduced deconcatenation. -/
private theorem map_reducedProjection_assoc_rTensor_deconcatenation (w : ReducedTensorWords R M) :
    TensorProduct.map (TensorWords.reducedProjection R M)
        (TensorProduct.map (TensorWords.reducedProjection R M)
          (TensorWords.reducedProjection R M))
        (TensorProduct.assoc R (TensorWords R M) (TensorWords R M) (TensorWords R M)
          (LinearMap.rTensor (TensorWords R M) (TensorWords.deconcatenation R M)
            (TensorWords.deconcatenation R M (TensorWords.reducedInclusion R M w)))) =
      TensorProduct.assoc R (ReducedTensorWords R M) (ReducedTensorWords R M)
        (ReducedTensorWords R M)
        (LinearMap.rTensor (ReducedTensorWords R M) (deconcatenation R M)
          (deconcatenation R M w)) := by
  rw [TensorWords.deconcatenation_comp_reducedInclusion_apply]
  simp only [map_add, TensorWords.deconcatenation_one,
    TensorProduct.map_map_assoc, TensorProduct.assoc_tmul, TensorProduct.map_tmul,
    TensorWords.reducedProjection_one, TensorWords.reducedProjection_reducedInclusion,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, zero_add, add_zero,
    TensorProduct.map_map,
    TensorWords.reducedProjection_comp_reducedInclusion,
    TensorWords.map_reducedProjection_comp_deconcatenation_comp_reducedInclusion,
    LinearMap.id_apply, LinearMap.id_comp, LinearMap.rTensor_def]

/-- Projecting all three factors after iterating full deconcatenation on the right recovers the
corresponding iteration of reduced deconcatenation. -/
private theorem map_reducedProjection_lTensor_deconcatenation (w : ReducedTensorWords R M) :
    TensorProduct.map (TensorWords.reducedProjection R M)
        (TensorProduct.map (TensorWords.reducedProjection R M)
          (TensorWords.reducedProjection R M))
        (LinearMap.lTensor (TensorWords R M) (TensorWords.deconcatenation R M)
          (TensorWords.deconcatenation R M (TensorWords.reducedInclusion R M w))) =
      LinearMap.lTensor (ReducedTensorWords R M) (deconcatenation R M)
        (deconcatenation R M w) := by
  rw [TensorWords.deconcatenation_comp_reducedInclusion_apply]
  simp only [map_add, TensorWords.deconcatenation_one,
    TensorProduct.map_tmul, TensorWords.reducedProjection_one,
    TensorWords.reducedProjection_reducedInclusion, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, zero_add, add_zero,
    TensorProduct.map_map, TensorWords.reducedProjection_comp_reducedInclusion,
    TensorWords.map_reducedProjection_comp_deconcatenation_comp_reducedInclusion,
    LinearMap.id_apply, LinearMap.id_comp, LinearMap.lTensor_def]

/-- Reduced deconcatenation is coassociative: cutting a reduced word twice gives the same sum of
three blocks whether the second cut is made in the left or right factor. -/
theorem deconcatenation_coassoc :
    (TensorProduct.assoc R (ReducedTensorWords R M) (ReducedTensorWords R M)
          (ReducedTensorWords R M)).toLinearMap ∘ₗ
        LinearMap.rTensor (ReducedTensorWords R M) (deconcatenation R M) ∘ₗ
          deconcatenation R M =
      LinearMap.lTensor (ReducedTensorWords R M) (deconcatenation R M) ∘ₗ
        deconcatenation R M := by
  apply LinearMap.ext
  intro w
  have h := LinearMap.congr_fun (TensorWords.deconcatenation_coassoc R M)
    (TensorWords.reducedInclusion R M w)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h ⊢
  calc
    _ = TensorProduct.map (TensorWords.reducedProjection R M)
          (TensorProduct.map (TensorWords.reducedProjection R M)
            (TensorWords.reducedProjection R M))
          (TensorProduct.assoc R (TensorWords R M) (TensorWords R M) (TensorWords R M)
            (LinearMap.rTensor (TensorWords R M) (TensorWords.deconcatenation R M)
              (TensorWords.deconcatenation R M (TensorWords.reducedInclusion R M w)))) :=
      (map_reducedProjection_assoc_rTensor_deconcatenation R M w).symm
    _ = TensorProduct.map (TensorWords.reducedProjection R M)
          (TensorProduct.map (TensorWords.reducedProjection R M)
            (TensorWords.reducedProjection R M))
          (LinearMap.lTensor (TensorWords R M) (TensorWords.deconcatenation R M)
            (TensorWords.deconcatenation R M (TensorWords.reducedInclusion R M w))) := congrArg _ h
    _ = _ := map_reducedProjection_lTensor_deconcatenation R M w

end ReducedTensorWords

end TauCeti
