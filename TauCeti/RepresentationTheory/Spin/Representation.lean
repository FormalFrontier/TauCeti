/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.CliffordAction
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
public import Mathlib.RepresentationTheory.Basic

import TauCeti.LinearAlgebra.ExteriorAlgebra.End

/-!
# The Spin-group representation on the exterior model

This file restricts the Fock action of a Clifford algebra to its Spin group and proves, when the
first isotropic summand is finite free, that the underlying Clifford action generates every
endomorphism of the exterior model.

## Main definitions and results

* `TauCeti.spinRep` and `TauCeti.pinRep` are the representations of `spinGroup Q` and `pinGroup Q`
  on the exterior model.
* `TauCeti.spinAction_surjective` identifies the Fock action as onto the full endomorphism algebra
  when the first isotropic summand is finite free.

## References

* [Spin representations roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SpinRepresentations/README.md)
-/

public section

namespace TauCeti

universe u v

variable {K : Type u} [CommRing K]
variable {V : Type v} [AddCommGroup V] [Module K V]

/-- The representation of the Spin group obtained by restricting its Clifford-algebra action on
the exterior algebra of the first isotropic summand. -/
noncomputable def spinRep (Q : QuadraticForm K V) (P : SpinPolarizationData Q) :
    Representation K (spinGroup Q) (ExteriorAlgebra K P.W) :=
  (spinAction Q P).toRingHom.toMonoidHom.comp
    ((Units.coeHom (CliffordAlgebra Q)).comp spinGroup.toUnits)

/-- A Spin-group element acts through its underlying Clifford-algebra element. -/
@[simp]
theorem spinRep_apply (Q : QuadraticForm K V) (P : SpinPolarizationData Q) (g : spinGroup Q) :
    spinRep Q P g = spinAction Q P g := by
  simp [spinRep]

/-- The representation of the Pin group obtained by restricting its Clifford-algebra action on
the exterior algebra of the first isotropic summand. -/
noncomputable def pinRep (Q : QuadraticForm K V) (P : SpinPolarizationData Q) :
    Representation K (pinGroup Q) (ExteriorAlgebra K P.W) :=
  (spinAction Q P).toRingHom.toMonoidHom.comp
    ((Units.coeHom (CliffordAlgebra Q)).comp pinGroup.toUnits)

/-- A Pin-group element acts through its underlying Clifford-algebra element. -/
@[simp]
theorem pinRep_apply (Q : QuadraticForm K V) (P : SpinPolarizationData Q) (g : pinGroup Q) :
    pinRep Q P g = spinAction Q P g := by
  simp [pinRep]

/-- When the first isotropic summand is finite free, the Fock action of a Clifford algebra on its
exterior model is onto the full endomorphism algebra. -/
theorem spinAction_surjective {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
    [Module.Free K P.W] [Module.Finite K P.W] :
    Function.Surjective (spinAction Q P) := by
  rw [← AlgHom.range_eq_top]
  apply top_unique
  rw [← ExteriorAlgebra.creation_contraction_adjoin_eq_top (K := K) (W := P.W)]
  apply Algebra.adjoin_le
  rintro f (⟨x, rfl⟩ | ⟨d, rfl⟩)
  · apply (spinAction Q P).mem_range.mpr
    refine ⟨CliffordAlgebra.ι Q (x : V), ?_⟩
    apply LinearMap.ext
    intro s
    exact spinAction_ι_wedge P x s
  · obtain ⟨y, rfl⟩ := P.pairingEquiv.surjective d
    apply (spinAction Q P).mem_range.mpr
    refine ⟨CliffordAlgebra.ι Q (y : V), ?_⟩
    apply LinearMap.ext
    intro s
    exact spinAction_ι_contract P y s

end TauCeti
