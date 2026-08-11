/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import TauCeti.RingTheory.Ideal.Cotangent.Basic

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

* `Ideal.cotangentLocalizationMap`: the map on cotangent spaces induced by localization.
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
variable [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]

/-- The map `p / p² → pRₚ / (pRₚ)²` induced by localization at the maximal ideal `p`.

The target is written using the unique maximal ideal of the local ring `Rₚ`; this ideal is the
extension of `p` by `IsLocalization.AtPrime.map_eq_maximalIdeal`. -/
noncomputable def cotangentLocalizationMap :
    p.Cotangent →ₗ[R] (maximalIdeal Rₚ).Cotangent :=
  Ideal.mapCotangent p (maximalIdeal Rₚ) (Algebra.ofId R Rₚ) (by
    intro x hx
    rw [Ideal.mem_comap, Algebra.ofId_apply, ← Ideal.mem_under,
      IsLocalization.AtPrime.under_maximalIdeal Rₚ p]
    exact hx)

/-- The localization map on cotangent spaces sends the class of `x ∈ p` to the class of its
image in the maximal ideal of `Rₚ`. -/
@[simp]
theorem cotangentLocalizationMap_toCotangent (x : p) :
    cotangentLocalizationMap p (p.toCotangent x) =
      (maximalIdeal Rₚ).toCotangent
        ⟨algebraMap R Rₚ x, by
          rw [← Ideal.mem_under, IsLocalization.AtPrime.under_maximalIdeal Rₚ p]
          exact x.2⟩ :=
  Ideal.mapCotangent_toCotangent p (maximalIdeal Rₚ) (Algebra.ofId R Rₚ) _ x

/-- Localization at a maximal ideal identifies its cotangent space with the cotangent space of
the resulting local ring. -/
theorem cotangentLocalizationMap_bijective :
    Function.Bijective (cotangentLocalizationMap p :
      p.Cotangent → (maximalIdeal Rₚ).Cotangent) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨x, rfl⟩ := p.toCotangent_surjective x
    simp only [cotangentLocalizationMap_toCotangent, Ideal.toCotangent_eq_zero] at hx ⊢
    rw [← Ideal.mem_under, IsLocalization.AtPrime.under_maximalIdeal_pow p Rₚ 2] at hx
    exact hx
  · intro y
    obtain ⟨y, rfl⟩ := (maximalIdeal Rₚ).toCotangent_surjective y
    obtain ⟨x, s, hxs⟩ := IsLocalization.exists_mk'_eq p.primeCompl y.1
    have hx : x ∈ p := by
      rw [← IsLocalization.AtPrime.mk'_mem_maximal_iff Rₚ p x s, hxs]
      exact y.2
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
      ((Ideal.Quotient.mk p (s : R))⁻¹)
    refine ⟨p.toCotangent ⟨r * x, p.mul_mem_left r hx⟩, ?_⟩
    rw [cotangentLocalizationMap_toCotangent, Ideal.toCotangent_eq]
    rw [← hxs]
    apply (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units Rₚ s)).mp
    rw [mul_sub, ← map_mul, mul_comm (algebraMap R Rₚ (s : R)),
      IsLocalization.mk'_spec, ← map_sub]
    rw [← Ideal.mem_under, IsLocalization.AtPrime.under_maximalIdeal_pow p Rₚ 2]
    have hs0 : Ideal.Quotient.mk p (s : R) ≠ 0 := by
      intro hs
      rw [Ideal.Quotient.eq_zero_iff_mem] at hs
      exact Ideal.mem_primeCompl_iff.mp s.2 hs
    have hsr : (s : R) * r - 1 ∈ p := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hr,
        mul_inv_cancel₀ hs0]
      simp
    convert Ideal.mul_mem_mul hsr hx using 1 <;> ring

/-- The canonical linear equivalence `p / p² ≃ pRₚ / (pRₚ)²` induced by localization. -/
noncomputable def cotangentLocalizationEquiv :
    p.Cotangent ≃ₗ[R] (maximalIdeal Rₚ).Cotangent :=
  LinearEquiv.ofBijective (cotangentLocalizationMap p)
    (cotangentLocalizationMap_bijective p)

/-- On a class represented by `x ∈ p`, the cotangent localization equivalence is induced by the
ring localization map. -/
@[simp]
theorem cotangentLocalizationEquiv_toCotangent (x : p) :
    cotangentLocalizationEquiv p (p.toCotangent x) =
      (maximalIdeal Rₚ).toCotangent
        ⟨algebraMap R Rₚ x, by
          rw [← Ideal.mem_under, IsLocalization.AtPrime.under_maximalIdeal Rₚ p]
          exact x.2⟩ :=
  cotangentLocalizationMap_toCotangent p x

/-- The cotangent localization equivalence is semilinear for the canonical equivalence between
the residue field `R / p` and the residue field of `Rₚ`. -/
theorem cotangentLocalizationEquiv_smul (r : R ⧸ p) (x : p.Cotangent) :
    cotangentLocalizationEquiv (Rₚ := Rₚ) p (r • x) =
      IsLocalization.AtPrime.equivQuotMaximalIdeal p Rₚ r •
        cotangentLocalizationEquiv (Rₚ := Rₚ) p x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
  -- Expose the quotient-module scalar actions on both sides; their public API has no
  -- rewriting lemma from a quotient representative to the underlying ring action.
  change cotangentLocalizationEquiv (Rₚ := Rₚ) p (r • x) =
    algebraMap R Rₚ r • cotangentLocalizationEquiv (Rₚ := Rₚ) p x
  rw [IsScalarTower.algebraMap_smul Rₚ]
  exact map_smul (cotangentLocalizationEquiv (Rₚ := Rₚ) p) r x

end Ideal
