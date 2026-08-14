/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AugmentationPoint.Basic
public import TauCeti.AlgebraicGeometry.TangentSpace.Basic
public import TauCeti.RingTheory.Ideal.Cotangent.Localization

/-!
# The Zariski cotangent space at an augmentation point

For an augmented commutative algebra `f : H →ₐ[k] k`, the augmentation determines a `k`-rational
point of `Spec H`. Its prime ideal is `ker f`. The stalk of `Spec H` at this point is the
localization of `H` at `ker f`, so localization of cotangent spaces gives a canonical equivalence

```text
ker(f) / ker(f)² ≃ₗ[k] 𝔪_f / 𝔪_f².
```

This file supplies the affine-scheme comparison used to identify the augmentation cotangent space
of a commutative bialgebra with the Zariski cotangent space at its augmentation point.

## Main declarations

* `AlgHom.kernelResidueFieldRingEquiv`: the canonical identification of its residue field with
  `k`.
* `AlgHom.kernelCotangentLinearEquivZariski`: the kernel cotangent space is the Zariski cotangent
  space at the augmentation point.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a.
-/

public section

open AlgebraicGeometry IsLocalRing

namespace TauCeti

namespace AlgHom

universe u v

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [Algebra k H]
variable (f : H →ₐ[k] k)

private theorem surjective : Function.Surjective (f : H →+* k) := fun r ↦
  ⟨algebraMap k H r, by simp⟩

/-- The kernel of an augmentation to a field is canonically maximal. -/
instance kernelIsMaximal : (RingHom.ker (f : H →+* k)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (f : H →+* k) (surjective f)

/-- The stalk at an augmentation point is an `H`-algebra through the germ map. -/
noncomputable instance kernelStalkAlgebra :
    Algebra H ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f)) :=
  StructureSheaf.stalkAlgebra H (kernelPoint f)

/-- The stalk at an augmentation point is a `k`-algebra through `k → H`. -/
noncomputable instance kernelStalkBaseAlgebra :
    Algebra k ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f)) :=
  Algebra.restrictScalars k H _

/-- Scalar extension from `k` through `H` to the stalk at an augmentation point is compatible. -/
instance kernelStalkIsScalarTower :
    IsScalarTower k H ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f)) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The stalk at an augmentation point is the localization of `H` at the augmentation kernel. -/
instance kernelStalkIsLocalization :
    IsLocalization.AtPrime
      ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f))
      (RingHom.ker (f : H →+* k)) := by
  unfold kernelStalkAlgebra
  -- `to_stalk` is stated using the point's `asIdeal`, while `AtPrime` unfolds to
  -- `IsLocalization` at the explicit prime complement; no public lemma bridges the wrappers.
  change @IsLocalization H _ (RingHom.ker (f : H →+* k)).primeCompl
    ((Spec.structureSheaf H).presheaf.stalk (kernelPoint f)) _
      (StructureSheaf.stalkAlgebra H (kernelPoint f))
  simpa only [kernelPoint_asIdeal] using
    (StructureSheaf.IsLocalization.to_stalk H (kernelPoint f))

/-- The ground field is canonically the residue field at an augmentation point. -/
noncomputable def kernelResidueFieldRingEquiv :
    k ≃+* IsLocalRing.ResidueField
      ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f)) :=
  (RingHom.quotientKerEquivOfSurjective (surjective f)).symm.trans
    (IsLocalization.AtPrime.equivQuotMaximalIdeal (RingHom.ker (f : H →+* k))
      ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f)))

/-- The residue-field equivalence agrees with the canonical algebra map from the ground field. -/
@[simp]
theorem kernelResidueFieldRingEquiv_apply (r : k) :
    kernelResidueFieldRingEquiv f r =
      algebraMap k
        (IsLocalRing.ResidueField
          ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f))) r := by
  -- `ResidueField` is definitionally the quotient by the maximal ideal, but this bridge is
  -- opaque to `RingEquiv.trans_apply` at its default transparency.
  change (IsLocalization.AtPrime.equivQuotMaximalIdeal (RingHom.ker (f : H →+* k))
      ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f)))
        ((RingHom.quotientKerEquivOfSurjective (surjective f)).symm r) = _
  have h : (RingHom.quotientKerEquivOfSurjective (surjective f)).symm r =
      Ideal.Quotient.mk (RingHom.ker (f : H →+* k)) (algebraMap k H r) := by
    simpa using RingHom.quotientKerEquivOfSurjective_symm_apply
      (f := (f : H →+* k)) (surjective f) (algebraMap k H r)
  rw [h,
    IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
  rw [← IsScalarTower.algebraMap_apply k H
      ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f)),
    IsScalarTower.algebraMap_apply k
      ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f))
      (IsLocalRing.ResidueField
        ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f))),
    IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_def]

/-- The cotangent space of an augmentation kernel is canonically the Zariski cotangent space of
the affine spectrum at the corresponding point.

This is the cotangent form of the comparison between augmentation-valued derivations and the
scheme-theoretic tangent space at the augmentation point. -/
noncomputable def kernelCotangentLinearEquivZariski :
    (RingHom.ker (f : H →+* k)).Cotangent ≃ₗ[k]
      TauCeti.AlgebraicGeometry.ZariskiCotangentSpace
        (Spec (CommRingCat.of H)) (kernelPoint f) :=
  (Ideal.cotangentLocalizationEquiv
    (Rₚ := (Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f))
    (RingHom.ker (f : H →+* k))).restrictScalars k

/-- On an element of the augmentation kernel, the cotangent comparison is induced by the map from
the coordinate ring to its stalk. -/
@[simp]
theorem kernelCotangentLinearEquivZariski_toCotangent (a : RingHom.ker (f : H →+* k)) :
    kernelCotangentLinearEquivZariski f
        ((RingHom.ker (f : H →+* k)).toCotangent a) =
      (maximalIdeal
          ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f))).toCotangent
        ⟨algebraMap H
            ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f)) a,
          by
            rw [← Ideal.mem_under,
              IsLocalization.AtPrime.under_maximalIdeal
                ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f))
                (RingHom.ker (f : H →+* k))]
            exact a.2⟩ := by
  exact Ideal.cotangentLocalizationEquiv_toCotangent
    (Rₚ := (Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f))
    (RingHom.ker (f : H →+* k)) a

/-- The cotangent comparison intertwines the ground-field action with the native residue-field
action through `kernelResidueFieldRingEquiv`. -/
@[simp]
theorem kernelCotangentLinearEquivZariski_smul (r : k)
    (x : (RingHom.ker (f : H →+* k)).Cotangent) :
    r • kernelCotangentLinearEquivZariski f x =
      kernelResidueFieldRingEquiv f r • kernelCotangentLinearEquivZariski f x := by
  rw [← (kernelCotangentLinearEquivZariski f).map_smul r x]
  -- Expose the restricted-scalar wrapper before applying the localization equivalence's
  -- native residue-field scalar formula.
  unfold kernelCotangentLinearEquivZariski
  rw [LinearEquiv.restrictScalars_apply, LinearEquiv.restrictScalars_apply]
  rw [← IsScalarTower.algebraMap_smul H r x,
    ← IsScalarTower.algebraMap_smul (H ⧸ RingHom.ker (f : H →+* k)) (algebraMap k H r) x,
    Ideal.Quotient.algebraMap_eq,
    Ideal.cotangentLocalizationEquiv_smul,
    IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk,
    kernelResidueFieldRingEquiv_apply]
  rw [← Ideal.Quotient.algebraMap_eq]
  exact (IsScalarTower.algebraMap_smul
    (IsLocalRing.ResidueField
      ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f)))
    (algebraMap H ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f))
      (algebraMap k H r))
    (kernelCotangentLinearEquivZariski f x)).symm

/-- The cotangent space of an augmentation kernel and the Zariski cotangent space at its point
have the same dimension over the ground field. -/
theorem finrank_kernelCotangent_eq_finrank_zariskiCotangentSpace :
    Module.finrank k (RingHom.ker (f : H →+* k)).Cotangent =
      Module.finrank k
        (TauCeti.AlgebraicGeometry.ZariskiCotangentSpace
          (Spec (CommRingCat.of H)) (kernelPoint f)) :=
  (kernelCotangentLinearEquivZariski f).finrank_eq

end AlgHom

end TauCeti
