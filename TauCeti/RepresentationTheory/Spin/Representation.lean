/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.CliffordAction
public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
public import Mathlib.RepresentationTheory.Basic

import TauCeti.LinearAlgebra.ExteriorAlgebra.End

/-!
# The Spin-group representation on the exterior model

This file restricts the Fock action of a Clifford algebra to its Spin group and to its even
subalgebra, and proves, when the first isotropic summand is finite free, that the underlying
Clifford action generates every endomorphism of the exterior model.

The Spin group lies inside the even subalgebra (`spinGroup.mem_even`), so the Spin representation
factors through the even Clifford action `TauCeti.evenSpinAction` along the inclusion
`TauCeti.spinGroupToEven`. How much of the endomorphism algebra that restricted action reaches is
exactly what distinguishes the two parities of the ambient dimension: in *positive* even dimension
it splits off the two half-spin blocks, while in odd dimension it is still everything. Dimension
zero is the degenerate exception to the even description, `W` being `⊥` there, so that `S = K` is
one-dimensional, the odd block is zero and the even action is again onto.

## Main definitions and results

* `TauCeti.spinRep` and `TauCeti.pinRep` are the representations of `spinGroup Q` and `pinGroup Q`
  on the exterior model.
* `TauCeti.spinGroupToEven` is the inclusion of the Spin group into the even Clifford subalgebra
  and `TauCeti.evenSpinAction` is the Fock action restricted to that subalgebra, through which the
  Spin representation factors by `TauCeti.evenSpinAction_apply` and
  `TauCeti.coe_spinGroupToEven_apply`.
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

/-- **The inclusion of the Spin group into the even Clifford subalgebra**, the Spin group
consisting of even elements by `spinGroup.mem_even`. -/
def spinGroupToEven (Q : QuadraticForm K V) : spinGroup Q →* CliffordAlgebra.even Q :=
  Submonoid.inclusion fun _ hx => spinGroup.mem_even hx

/-- A Spin-group element sits in the even subalgebra as itself. -/
@[simp]
theorem coe_spinGroupToEven_apply (Q : QuadraticForm K V) (g : spinGroup Q) :
    (spinGroupToEven Q g : CliffordAlgebra Q) = g :=
  (rfl)

/-- **The action of the even Clifford subalgebra on the spinor module** `S = ⋀·W`, the Fock action
restricted along the inclusion of `CliffordAlgebra.even Q`.

This is the algebra through which the Spin representation acts, `spinGroup Q` being contained in
the even subalgebra; the half-spin actions of `TauCeti.spinPlusAction` and
`TauCeti.spinMinusAction` are its two blocks in even dimension. -/
noncomputable def evenSpinAction (Q : QuadraticForm K V) (P : SpinPolarizationData Q) :
    CliffordAlgebra.even Q →ₐ[K] Module.End K (ExteriorAlgebra K P.W) :=
  (spinAction Q P).comp (CliffordAlgebra.even Q).val

/-- An even Clifford element acts on the spinor module by the Fock action. -/
@[simp]
theorem evenSpinAction_apply (Q : QuadraticForm K V) (P : SpinPolarizationData Q)
    (x : CliffordAlgebra.even Q) : evenSpinAction Q P x = spinAction Q P x :=
  (rfl)

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
