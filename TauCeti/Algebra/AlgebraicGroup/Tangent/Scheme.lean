/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
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

For a commutative bialgebra, specializing `f` to the counit identifies the cotangent space at the
identity of the represented affine monoid with the corresponding Zariski cotangent space. With an
additional Hopf-algebra structure, its `k`-dual is the Hopf-algebra model of `Lie(G)` for the
represented affine group. This file therefore synchronizes the coordinate and scheme tangent-space
models needed by the smoothness and dimension tools in Layer 2 of the ReductiveGroups roadmap.

## Main declarations

* `AlgHom.kernelPoint`: the point of `Spec H` cut out by the kernel of an augmentation.
* `AlgHom.kernelResidueFieldRingEquiv`: the canonical identification of its residue field with
  `k`.
* `AlgHom.kernelCotangentLinearEquivZariski`: the kernel cotangent space is the Zariski cotangent
  space at the augmentation point.
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

namespace AlgHom

universe u v

variable {k : Type u} [Field k]
variable {H : Type v} [CommRing H] [Algebra k H]
variable (f : H →ₐ[k] k)

private theorem surjective : Function.Surjective (f : H →+* k) := fun r ↦
  ⟨algebraMap k H r, by simp⟩

/-- The point of `Spec H` defined by an augmentation `f : H →ₐ[k] k`. Its prime ideal is
`ker f`. -/
def kernelPoint : Spec (CommRingCat.of H) :=
  ⟨RingHom.ker (f : H →+* k),
    (RingHom.ker_isMaximal_of_surjective (f : H →+* k) (surjective f)).isPrime⟩

/-- The prime ideal of an augmentation point is the kernel of the augmentation. -/
@[simp]
theorem kernelPoint_asIdeal :
    (kernelPoint f).asIdeal = RingHom.ker (f : H →+* k) :=
  (rfl)

/-- The augmentation point is the pullback of the closed point of the ground field. -/
theorem kernelPoint_eq_comap_closedPoint :
    kernelPoint f = PrimeSpectrum.comap (f : H →+* k) (closedPoint k) := by
  apply PrimeSpectrum.ext
  rw [kernelPoint_asIdeal, PrimeSpectrum.comap_asIdeal]
  -- Mathlib has no public lemma for this bridge: `closedPoint` is definitionally the point
  -- whose ideal is the local ring's `maximalIdeal`.
  rw [show (closedPoint k).asIdeal = maximalIdeal k from rfl,
    IsLocalRing.maximalIdeal_eq_bot]
  rfl

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
  exact StructureSheaf.IsLocalization.to_stalk H (kernelPoint f)

/-- The ground field is canonically the residue field at an augmentation point. -/
noncomputable def kernelResidueFieldRingEquiv :
    k ≃+* IsLocalRing.ResidueField
      ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f)) :=
  (RingHom.quotientKerEquivOfSurjective (surjective f)).symm.trans
    (IsLocalization.AtPrime.equivQuotMaximalIdeal (RingHom.ker (f : H →+* k))
      ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f)))

/-- The residue-field equivalence sends a ground-field element to the residue class of its image
in the stalk. -/
@[simp]
theorem kernelResidueFieldRingEquiv_apply (r : k) :
    kernelResidueFieldRingEquiv f r =
      Ideal.Quotient.mk _
        (algebraMap H ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f))
          (algebraMap k H r)) := by
  -- Expose the composed ring equivalence so its two public representative lemmas apply.
  change (IsLocalization.AtPrime.equivQuotMaximalIdeal (RingHom.ker (f : H →+* k))
      ((Spec (CommRingCat.of H)).presheaf.stalk (kernelPoint f)))
        ((RingHom.quotientKerEquivOfSurjective (surjective f)).symm r) = _
  have h : (RingHom.quotientKerEquivOfSurjective (surjective f)).symm r =
      Ideal.Quotient.mk (RingHom.ker (f : H →+* k)) (algebraMap k H r) := by
    apply (RingHom.quotientKerEquivOfSurjective (surjective f)).injective
    rw [RingEquiv.apply_symm_apply, RingHom.quotientKerEquivOfSurjective_apply_mk]
    simp
  rw [h,
    IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]

/-- The cotangent space of an augmentation kernel is canonically the Zariski cotangent space of
the affine spectrum at the corresponding point.

This is the cotangent form of the comparison between augmentation-valued derivations and the
scheme-theoretic tangent space at the augmentation point. -/
@[expose] noncomputable def kernelCotangentLinearEquivZariski :
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
  -- `CotangentSpace` names the same quotient action through a dedicated module instance.
  unfold IsLocalRing.instModuleResidueFieldCotangentSpace
  rfl

/-- The cotangent space of an augmentation kernel and the Zariski cotangent space at its point
have the same dimension over the ground field. -/
@[simp]
theorem finrank_kernelCotangent_eq_finrank_zariskiCotangentSpace :
    Module.finrank k (RingHom.ker (f : H →+* k)).Cotangent =
      Module.finrank k
        (TauCeti.AlgebraicGeometry.ZariskiCotangentSpace
          (Spec (CommRingCat.of H)) (kernelPoint f)) :=
  (kernelCotangentLinearEquivZariski f).finrank_eq

end AlgHom

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
