/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Cotangent

/-!
# Cotangent spaces and localization at a maximal ideal

Let `p` be a maximal ideal of a commutative ring `R`, and let `Rₚ` be a localization of `R` at
`p`. The map from `R` to `Rₚ` identifies the cotangent space `p / p²` with the cotangent space
`pRₚ / (pRₚ)²` of the local ring `Rₚ`. This file constructs that identification and proves that
it is semilinear for the canonical equivalence between the two residue fields.

This is the localization bridge needed to compare the augmentation-ideal model of the tangent
space of an affine group with the Zariski tangent space of its spectrum at the identity. That
comparison is a prerequisite for the smoothness and dimension tools in Layer 2 of the
ReductiveGroups roadmap.

## Main declarations

* `Ideal.cotangentLocalizationEquiv`: localization at a maximal ideal preserves the cotangent
  space.
* `Ideal.cotangentLocalizationEquiv_smul`: the equivalence is semilinear for the canonical
  residue-field equivalence.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a.
-/

public section

open IsLocalRing

namespace Ideal

attribute [local instance] Ideal.Quotient.field

variable {R Rₚ : Type*} [CommRing R]
variable (p : Ideal R) [p.IsMaximal]
variable [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]

/-- The quotient-ring localization equivalence restricted to the cotangent ideals. -/
private noncomputable def cotangentLocalizationIdealEquiv :
    letI := IsLocalization.AtPrime.isLocalRing Rₚ p
    p.cotangentIdeal ≃ₗ[R] (maximalIdeal Rₚ).cotangentIdeal := by
  letI := IsLocalization.AtPrime.isLocalRing Rₚ p
  let e := (IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rₚ 2).toLinearEquiv
  exact e.ofSubmodules (p.cotangentIdeal.restrictScalars R)
    ((maximalIdeal Rₚ).cotangentIdeal.restrictScalars R) (by
    ext z
    rw [Submodule.mem_map_equiv]
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm z)
    rw [← e.apply_symm_apply z, e.symm_apply_apply, ← hx]
    -- `mem_map_equiv` leaves membership through `e`; expose its underlying quotient
    -- equivalence so that the public representative lemma can rewrite it.
    change (Ideal.Quotient.mk (p ^ 2) x ∈ p.cotangentIdeal) ↔
      (IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rₚ 2
        (Ideal.Quotient.mk (p ^ 2) x) ∈ (maximalIdeal Rₚ).cotangentIdeal)
    rw [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk,
      Ideal.mk_mem_cotangentIdeal, Ideal.mk_mem_cotangentIdeal,
      ← Ideal.mem_under, IsLocalization.AtPrime.under_maximalIdeal Rₚ p])

/-- The canonical linear equivalence `p / p² ≃ pRₚ / (pRₚ)²` induced by localization. -/
noncomputable def cotangentLocalizationEquiv :
    letI := IsLocalization.AtPrime.isLocalRing Rₚ p
    p.Cotangent ≃ₗ[R] (maximalIdeal Rₚ).Cotangent := by
  letI := IsLocalization.AtPrime.isLocalRing Rₚ p
  exact p.cotangentEquivIdeal |>.trans <|
    (cotangentLocalizationIdealEquiv p).trans <|
      (maximalIdeal Rₚ).cotangentEquivIdeal.symm.restrictScalars R

/-- On a class represented by `x ∈ p`, the cotangent localization equivalence is induced by the
ring localization map. -/
@[simp]
theorem cotangentLocalizationEquiv_toCotangent (x : p) :
    letI := IsLocalization.AtPrime.isLocalRing Rₚ p
    cotangentLocalizationEquiv p (p.toCotangent x) =
      (maximalIdeal Rₚ).toCotangent
        ⟨algebraMap R Rₚ x, by
          rw [← Ideal.mem_under, IsLocalization.AtPrime.under_maximalIdeal Rₚ p]
          exact x.2⟩ := by
  let _ := IsLocalization.AtPrime.isLocalRing Rₚ p
  rw [cotangentLocalizationEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply]
  apply (maximalIdeal Rₚ).cotangentEquivIdeal.injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  simp only [cotangentLocalizationIdealEquiv]
  -- The restricted `ofSubmodules` equivalence and `cotangentEquivIdeal` compute on their
  -- underlying quotient classes; expose those classes for the public representative lemma.
  change (IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rₚ 2)
      (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap R Rₚ x)
  exact IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk p Rₚ 2 x

/-- The cotangent localization equivalence is semilinear for the canonical equivalence between
the residue field `R / p` and the residue field of `Rₚ`. -/
@[simp]
theorem cotangentLocalizationEquiv_smul (r : R ⧸ p) (x : p.Cotangent) :
    letI := IsLocalization.AtPrime.isLocalRing Rₚ p
    cotangentLocalizationEquiv (Rₚ := Rₚ) p (r • x) =
      IsLocalization.AtPrime.equivQuotMaximalIdeal p Rₚ r •
        cotangentLocalizationEquiv (Rₚ := Rₚ) p x := by
  let _ := IsLocalization.AtPrime.isLocalRing Rₚ p
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
  rw [← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul,
    ← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
  rw [IsScalarTower.algebraMap_smul Rₚ]
  exact map_smul (cotangentLocalizationEquiv (Rₚ := Rₚ) p) r x

end Ideal
