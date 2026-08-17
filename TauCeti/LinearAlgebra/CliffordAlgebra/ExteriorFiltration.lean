/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import TauCeti.LinearAlgebra.CliffordAlgebra.Filtration

/-!
# The zero-form Clifford filtration

When the quadratic form is zero, its Clifford algebra is the exterior algebra. This file identifies
the Clifford degree filtration with the sum of exterior degrees up to the same bound, then uses the
exterior algebra's internal grading to identify each successive filtration quotient with the
corresponding exterior power.

This is the zero-form side of the Layer 0 `filtrationGradedEquiv` target in the
[spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/Suggested.lean#L62-L68).
The generic change-of-form transport belongs in `TauCeti.LinearAlgebra.CliffordAlgebra.Filtration`.

## Main results

* `CliffordAlgebra.exteriorPower_succ_disjoint_zero_form_filtration`: degree `k + 1` is
  disjoint from the lower zero-form filtration.
* `CliffordAlgebra.zeroFormFiltrationQuotientEquivExteriorPower`: the successive
  zero-form filtration quotient is the degree `k + 1` exterior power.

## References

* [Clifford algebras, Pin and Spin, and spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md),
  Layer 0, "The degree filtration".
-/

public section

open CliffordAlgebra
open scoped DirectSum

universe u v

namespace CliffordAlgebra

open TauCeti

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The degree `k + 1` exterior power is disjoint from the lower zero-form filtration. -/
theorem exteriorPower_succ_disjoint_zero_form_filtration (k : ℕ) :
    Disjoint (⋀[R]^(k + 1) M) (filtration (0 : QuadraticForm R M) k) := by
  rw [filtration_eq_iSup_pow (0 : QuadraticForm R M) k]
  rw [iSup_subtype]
  have hind : iSupIndep (fun i : ℕ => ⋀[R]^i M) :=
    (DirectSum.Decomposition.isInternal (fun i : ℕ => ⋀[R]^i M)).submodule_iSupIndep
  simpa only [Set.mem_Iic] using hind.disjoint_biSup (by simp : k + 1 ∉ Set.Iic k)

private noncomputable def quotientSupEquiv {X : Type*} [AddCommGroup X] [Module R X]
    (p p' : Submodule R X) (h : Disjoint p p') :
    (↥(p ⊔ p') ⧸ Submodule.comap (p ⊔ p').subtype p') ≃ₗ[R] p := by
  have hp : Submodule.comap p.subtype p' = ⊥ := Submodule.disjoint_iff_comap_eq_bot.mp h
  have hp0 : Submodule.comap p.subtype p ⊓ Submodule.comap p.subtype p' = ⊥ := by
    simpa only [Submodule.comap_subtype_self, top_inf_eq] using hp
  simpa only [Submodule.comap_subtype_self, top_inf_eq, hp] using
    (LinearMap.quotientInfEquivSupQuotient p p').symm.trans (Submodule.quotEquivOfEqBot _ hp0)

private theorem quotientSupEquiv_symm_apply {X : Type*} [AddCommGroup X] [Module R X]
    (p p' : Submodule R X) (h : Disjoint p p') (x : p) :
    (quotientSupEquiv p p' h).symm x =
      Submodule.Quotient.mk (Submodule.inclusion le_sup_left x) := by
  rw [quotientSupEquiv, LinearEquiv.trans_symm]
  simp only [LinearEquiv.trans_apply, Submodule.quotEquivOfEqBot_symm_apply]
  exact LinearMap.quotientInfEquivSupQuotient_apply_mk p p' x

private noncomputable def quotientEquivOfEqSup {X : Type*} [AddCommGroup X] [Module R X]
    (F p p' : Submodule R X) (hF : F = p ⊔ p') (h : Disjoint p p') :
    (F ⧸ Submodule.comap F.subtype p') ≃ₗ[R] p := by
  subst F
  exact quotientSupEquiv p p' h

private theorem quotientEquivOfEqSup_symm_apply {X : Type*} [AddCommGroup X] [Module R X]
    (F p p' : Submodule R X) (hF : F = p ⊔ p') (h : Disjoint p p') (x : p) :
    (quotientEquivOfEqSup F p p' hF h).symm x =
      Submodule.Quotient.mk ⟨x, by
        rw [hF]
        exact Submodule.mem_sup_left x.property⟩ := by
  subst F
  exact quotientSupEquiv_symm_apply p p' h x

private theorem zero_form_filtration_succ_eq_exteriorPower_sup (k : ℕ) :
    filtration (0 : QuadraticForm R M) (k + 1) =
      ⋀[R]^(k + 1) M ⊔ filtration (0 : QuadraticForm R M) k := by
  rw [filtration_succ_eq_sup, sup_comm]

/-- The successive zero-form Clifford filtration quotient is the degree `k + 1` exterior power. -/
noncomputable def zeroFormFiltrationQuotientEquivExteriorPower (k : ℕ) :
    FiltrationGradedPiece (0 : QuadraticForm R M) (k + 1) ≃ₗ[R] ⋀[R]^(k + 1) M :=
  (Submodule.quotEquivOfEq _ _
    (filtrationPreviousRestricted_succ (0 : QuadraticForm R M) k)).trans
    (quotientEquivOfEqSup _ _ _ (zero_form_filtration_succ_eq_exteriorPower_sup k)
      (exteriorPower_succ_disjoint_zero_form_filtration k))

/-- The inverse quotient equivalence sends a degree `k + 1` exterior element to its canonical
quotient class. -/
@[simp]
theorem zeroFormFiltrationQuotientEquivExteriorPower_symm_apply (k : ℕ)
    (x : ⋀[R]^(k + 1) M) :
    (zeroFormFiltrationQuotientEquivExteriorPower k).symm x =
      Submodule.Quotient.mk
        ⟨x, ι_range_pow_le_filtration (0 : QuadraticForm R M) (k + 1) x.property⟩ := by
  rw [zeroFormFiltrationQuotientEquivExteriorPower, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, quotientEquivOfEqSup_symm_apply]
  apply (Submodule.quotEquivOfEq _ _
    (filtrationPreviousRestricted_succ (0 : QuadraticForm R M) k)).injective
  rw [LinearEquiv.apply_symm_apply, Submodule.quotEquivOfEq_mk]

/-- The quotient equivalence sends the canonical class of a degree `k + 1` exterior element to
that element. -/
@[simp]
theorem zeroFormFiltrationQuotientEquivExteriorPower_apply (k : ℕ)
    (x : ⋀[R]^(k + 1) M) :
    zeroFormFiltrationQuotientEquivExteriorPower k
      (Submodule.Quotient.mk
        ⟨x, ι_range_pow_le_filtration (0 : QuadraticForm R M) (k + 1) x.property⟩) = x := by
  rw [← zeroFormFiltrationQuotientEquivExteriorPower_symm_apply k x,
    LinearEquiv.apply_symm_apply]

end CliffordAlgebra
