/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Degree

/-!
# Relative degrees of effective Weil divisors

This file records the positivity properties of the residue-field-weighted degree of a
scheme-theoretic Weil divisor. Relative degree is always nonnegative on effective divisors. If
the residue-field extensions at the divisor's support are finite, their weights are strictly
positive, so an effective divisor has degree zero exactly when it is zero.

For an isomorphism of schemes every residue degree is one. In that case relative degree reduces
to the ordinary, unweighted degree; the identity morphism is the principal example.

These results supply the positivity and normalization API for the degree in
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, “Degree”. They reuse the general weighted
degree theory for `WeilDivisor` and Mathlib's definition of scheme-theoretic residue degree; no
external formalization is copied.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X Y : Scheme.{u}}

noncomputable section

/-- Relative degree is weighted degree for the residue-degree weight function. -/
lemma relativeDegree_eq_weightedDegree (f : X ⟶ Y) (D : SchemeWeilDivisor X) :
    relativeDegree f D =
      WeilDivisor.weightedDegree
        (fun x : CodimensionOnePoint X ↦ (f.residueDegree x : ℤ)) D := by
  rw [relativeDegree_apply, WeilDivisor.weightedDegree_apply]

/-- The relative degree of an effective Weil divisor is nonnegative. -/
lemma IsEffective.relativeDegree_nonneg {D : SchemeWeilDivisor X}
    (hD : WeilDivisor.IsEffective D) (f : X ⟶ Y) :
    0 ≤ relativeDegree f D := by
  rw [relativeDegree_eq_weightedDegree]
  exact hD.weightedDegree_nonneg fun x ↦ Nat.cast_nonneg _

/-- If the residue-field extension is finite at every point in the support, an effective
divisor has relative degree zero exactly when it is zero. -/
lemma IsEffective.relativeDegree_eq_zero_iff_of_finite_on_support
    {D : SchemeWeilDivisor X} (hD : WeilDivisor.IsEffective D) (f : X ⟶ Y)
    (hf : ∀ x ∈ D.support, (f.residueFieldMap x).hom.Finite) :
    relativeDegree f D = 0 ↔ D = 0 := by
  rw [relativeDegree_eq_weightedDegree]
  apply hD.weightedDegree_eq_zero_iff_of_pos_on_support
  intro x hx
  exact_mod_cast (residueDegree_pos_iff f x).mpr (hf x hx)

/-- If every residue-field extension is finite, an effective divisor has relative degree zero
exactly when it is zero. -/
lemma IsEffective.relativeDegree_eq_zero_iff_of_finite
    {D : SchemeWeilDivisor X} (hD : WeilDivisor.IsEffective D) (f : X ⟶ Y)
    (hf : ∀ x, (f.residueFieldMap x).hom.Finite) :
    relativeDegree f D = 0 ↔ D = 0 :=
  IsEffective.relativeDegree_eq_zero_iff_of_finite_on_support hD f fun x _ ↦ hf x

/-- A nonzero effective divisor has positive relative degree when the residue-field extensions
at its support are finite. -/
lemma IsEffective.relativeDegree_pos_of_finite_on_support_of_ne_zero
    {D : SchemeWeilDivisor X} (hD : WeilDivisor.IsEffective D) (f : X ⟶ Y)
    (hf : ∀ x ∈ D.support, (f.residueFieldMap x).hom.Finite) (hD0 : D ≠ 0) :
    0 < relativeDegree f D := by
  exact lt_of_le_of_ne (IsEffective.relativeDegree_nonneg hD f) fun h ↦
    hD0 ((IsEffective.relativeDegree_eq_zero_iff_of_finite_on_support hD f hf).mp h.symm)

/-- Along an isomorphism, relative degree is the ordinary unweighted degree. -/
@[simp]
lemma relativeDegree_eq_degree_of_isIso (f : X ⟶ Y) [IsIso f]
    (D : SchemeWeilDivisor X) :
    relativeDegree f D = WeilDivisor.degree D := by
  rw [relativeDegree_eq_weightedDegree]
  simpa only [residueDegree_eq_one_of_isIso, Nat.cast_one] using
    WeilDivisor.weightedDegree_one_eq_degree D

end

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
