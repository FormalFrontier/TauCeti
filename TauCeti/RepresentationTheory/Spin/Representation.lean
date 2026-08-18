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
import Mathlib.RingTheory.SimpleModule.Basic

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
* `TauCeti.eq_bot_or_eq_top_of_spinAction_invariant` says that the exterior model is a simple
  Clifford module when the base ring is a field.

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

section Field

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

/-- **The spinor module is a simple Clifford module.** A submodule of `S = ⋀·W` carried into
itself by the Fock action of every Clifford element is `⊥` or `⊤`: this is the irreducibility of
the spinor representation of `CliffordAlgebra Q`.

It is *not* irreducibility of the spin representation of the group. The spin group is much smaller
than the Clifford algebra, and in even dimension the half-spin summands `TauCeti.spinPlus` and
`TauCeti.spinMinus` are invariant under `TauCeti.spinRep`, so `S` splits as a representation of the
group as soon as both summands are nonzero. What fails for them here is the invariance hypothesis:
an odd Clifford element exchanges the two summands. -/
theorem eq_bot_or_eq_top_of_spinAction_invariant [Module.Finite K P.W]
    {N : Submodule K (ExteriorAlgebra K P.W)}
    (hN : ∀ x : CliffordAlgebra Q, N.map (spinAction Q P x) ≤ N) : N = ⊥ ∨ N = ⊤ := by
  let N' : Submodule (Module.End K (ExteriorAlgebra K P.W)) (ExteriorAlgebra K P.W) :=
    { carrier := N
      zero_mem' := N.zero_mem
      add_mem' := N.add_mem
      smul_mem' := by
        intro f s hs
        obtain ⟨x, rfl⟩ := spinAction_surjective P f
        exact hN x (Submodule.mem_map.mpr ⟨s, hs, rfl⟩) }
  rcases IsSimpleOrder.eq_bot_or_eq_top N' with h | h
  · apply Or.inl
    apply SetLike.ext'
    change (N' : Set (ExteriorAlgebra K P.W)) =
      ↑(⊥ : Submodule (Module.End K (ExteriorAlgebra K P.W)) (ExteriorAlgebra K P.W))
    exact congrArg (fun M : Submodule (Module.End K (ExteriorAlgebra K P.W))
      (ExteriorAlgebra K P.W) ↦ (M : Set (ExteriorAlgebra K P.W))) h
  · apply Or.inr
    apply SetLike.ext'
    change (N' : Set (ExteriorAlgebra K P.W)) =
      ↑(⊤ : Submodule (Module.End K (ExteriorAlgebra K P.W)) (ExteriorAlgebra K P.W))
    exact congrArg (fun M : Submodule (Module.End K (ExteriorAlgebra K P.W))
      (ExteriorAlgebra K P.W) ↦ (M : Set (ExteriorAlgebra K P.W))) h

end Field

end TauCeti
