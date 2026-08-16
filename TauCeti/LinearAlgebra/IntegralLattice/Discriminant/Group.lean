/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import TauCeti.LinearAlgebra.IntegralLattice.Dual.Basic
import TauCeti.LinearAlgebra.IntegralLattice.Dual.Finiteness

/-!
# Discriminant groups of integral lattices

For a nondegenerate integral lattice `L`, its discriminant group is the finite quotient

```text
A_L = Lᵛ / L.
```

Both lattices in this expression are submodules of the same rational ambient vector space.  To
form the quotient, `carrierInDual` realizes `L.carrier` as a submodule of the subtype
`L.dualCarrier`.  The quotient is defined without a nondegeneracy hypothesis, while its finiteness
uses nondegeneracy through the fact that the dual carrier is a full lattice of the same rank.

An isometry of integral lattices restricts to an equivalence of dual carriers and hence induces an
equivalence of discriminant groups.  The construction respects identity, inverse, and composition.

## Main declarations

* `TauCeti.IntegralLattice.carrierInDual`: the original carrier inside its dual carrier.
* `TauCeti.IntegralLattice.DiscriminantGroup`: the quotient `Lᵛ / L`.
* `TauCeti.IntegralLattice.instFiniteDiscriminantGroup`: finiteness in the nondegenerate case.
* `TauCeti.IntegralLattice.finite_discriminantGroup_iff_nondegenerate`: finiteness holds exactly
  in the nondegenerate case.
* `TauCeti.IntegralLattice.Isometry.discriminantGroupEquiv`: the induced equivalence of
  discriminant groups.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md` (Layer 2).
* `TauCetiRoadmap/IntegralLattices/Suggested.lean`.
-/

public section

open Module

namespace TauCeti

universe u v w

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- The original carrier, regarded as a submodule of the subtype `L.dualCarrier`. -/
def carrierInDual (L : IntegralLattice V) : Submodule ℤ L.dualCarrier :=
  L.carrier.submoduleOf L.dualCarrier

/-- Membership in `carrierInDual` is membership of the underlying ambient vector in the original
carrier. -/
@[simp]
theorem mem_carrierInDual_iff (L : IntegralLattice V) (x : L.dualCarrier) :
    x ∈ L.carrierInDual ↔ (x : V) ∈ L.carrier := Iff.rfl

/-- The embedded carrier is the inverse image of the ambient carrier under the dual-carrier
inclusion. -/
theorem carrierInDual_eq_comap_subtype (L : IntegralLattice V) :
    L.carrierInDual = L.carrier.comap L.dualCarrier.subtype := by
  ext x
  exact L.mem_carrierInDual_iff x

/-- Mapping the embedded carrier back into the ambient space recovers the original carrier. -/
@[simp]
theorem map_carrierInDual_subtype (L : IntegralLattice V) :
    L.carrierInDual.map L.dualCarrier.subtype = L.carrier := by
  rw [L.carrierInDual_eq_comap_subtype, Submodule.map_comap_subtype,
    inf_of_le_right L.le_dualCarrier]

/-- The copy of the carrier inside the dual carrier has the same rank as the carrier. -/
theorem finrank_carrierInDual (L : IntegralLattice V) :
    Module.finrank ℤ L.carrierInDual = Module.finrank ℤ L :=
  (Submodule.submoduleOfEquivOfLe L.le_dualCarrier).finrank_eq

/-- The discriminant group `A_L = Lᵛ / L`, as an actual quotient of the dual-carrier subtype by
the inverse image of the original carrier. -/
abbrev DiscriminantGroup (L : IntegralLattice V) : Type u :=
  L.dualCarrier ⧸ L.carrierInDual

/-- A representative defines the zero discriminant class exactly when its ambient vector belongs
to the original carrier. -/
theorem discriminantGroup_mk_eq_zero_iff (L : IntegralLattice V) (x : L.dualCarrier) :
    (Submodule.Quotient.mk x : L.DiscriminantGroup) = 0 ↔ (x : V) ∈ L.carrier := by
  rw [Submodule.Quotient.mk_eq_zero, L.mem_carrierInDual_iff]

/-- Two representatives define the same discriminant class exactly when their difference belongs
to the original carrier. -/
@[simp]
theorem discriminantGroup_mk_eq_iff (L : IntegralLattice V) (x y : L.dualCarrier) :
    (Submodule.Quotient.mk x : L.DiscriminantGroup) = Submodule.Quotient.mk y ↔
      ((x - y : L.dualCarrier) : V) ∈ L.carrier := by
  rw [Submodule.Quotient.eq, L.mem_carrierInDual_iff]

/-- The discriminant group of a nondegenerate integral lattice is finite. -/
noncomputable instance instFiniteDiscriminantGroup (L : IntegralLattice V) [L.IsNondegenerate] :
    Finite L.DiscriminantGroup := by
  apply Submodule.finiteQuotientOfFreeOfRankEq L.carrierInDual
  rw [L.finrank_carrierInDual, L.finrank_carrier, L.finrank_dualCarrier]

/-- The discriminant group is finite exactly when the lattice form is nondegenerate. -/
theorem finite_discriminantGroup_iff_nondegenerate (L : IntegralLattice V) :
    Finite L.DiscriminantGroup ↔ L.form.Nondegenerate := by
  constructor
  · intro hfinite
    let : Finite L.DiscriminantGroup := hfinite
    let : Module.Finite ℤ L.carrierInDual :=
      Module.Finite.equiv (Submodule.submoduleOfEquivOfLe L.le_dualCarrier).symm
    let : Module.Finite ℤ L.dualCarrier :=
      Module.Finite.of_submodule_quotient L.carrierInDual
    exact L.nondegenerate_of_moduleFinite_dualCarrier
  · intro hnondegenerate
    let : L.IsNondegenerate := ⟨hnondegenerate⟩
    infer_instance

namespace Isometry

variable {W : Type v} {U : Type w}
variable [AddCommGroup W] [Module ℚ W]
variable [AddCommGroup U] [Module ℚ U]
variable {L : IntegralLattice V} {M : IntegralLattice W} {N : IntegralLattice U}

/-- The dual-carrier equivalence maps the embedded original carrier onto the embedded target
carrier. -/
theorem map_carrierInDual (e : Isometry L M) :
    L.carrierInDual.map e.dualCarrierEquiv.toLinearMap = M.carrierInDual := by
  ext y
  rw [Submodule.mem_map_equiv]
  rw [L.mem_carrierInDual_iff, M.mem_carrierInDual_iff,
    ← e.dualCarrierEquiv_symm, coe_dualCarrierEquiv_apply]
  exact e.symm.apply_mem_carrier_iff y

/-- An integral-lattice isometry induces a linear equivalence of discriminant groups. -/
def discriminantGroupEquiv (e : Isometry L M) :
    L.DiscriminantGroup ≃ₗ[ℤ] M.DiscriminantGroup :=
  Submodule.Quotient.equiv L.carrierInDual M.carrierInDual e.dualCarrierEquiv
    e.map_carrierInDual

/-- The induced discriminant-group equivalence maps the class of a representative to the class of
its image. -/
@[simp]
theorem discriminantGroupEquiv_mk (e : Isometry L M) (x : L.dualCarrier) :
    e.discriminantGroupEquiv (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e.dualCarrierEquiv x) := by
  simp [discriminantGroupEquiv]

/-- The identity isometry induces the identity equivalence of discriminant groups. -/
@[simp]
theorem discriminantGroupEquiv_refl (L : IntegralLattice V) :
    (Isometry.refl L).discriminantGroupEquiv = LinearEquiv.refl ℤ L.DiscriminantGroup := by
  unfold discriminantGroupEquiv
  simp only [dualCarrierEquiv_refl]
  rw [Submodule.Quotient.equiv_refl]
  ext x
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp

/-- The equivalence induced by an inverse isometry is the inverse of the induced equivalence. -/
@[simp]
theorem discriminantGroupEquiv_symm (e : Isometry L M) :
    e.symm.discriminantGroupEquiv = e.discriminantGroupEquiv.symm := by
  simp only [discriminantGroupEquiv, Submodule.Quotient.equiv_symm,
    dualCarrierEquiv_symm]

/-- The inverse induced discriminant-group equivalence maps a representative through the inverse
dual-carrier equivalence. -/
@[simp]
theorem discriminantGroupEquiv_symm_mk (e : Isometry L M) (y : M.dualCarrier) :
    e.discriminantGroupEquiv.symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (e.symm.dualCarrierEquiv y) := by
  rw [← e.discriminantGroupEquiv_symm, discriminantGroupEquiv_mk]

/-- The equivalence induced by a composite isometry is the composite of the induced
equivalences. -/
@[simp]
theorem discriminantGroupEquiv_trans (e : Isometry L M) (f : Isometry M N) :
    (e.trans f).discriminantGroupEquiv =
      e.discriminantGroupEquiv.trans f.discriminantGroupEquiv := by
  unfold discriminantGroupEquiv
  simp only [dualCarrierEquiv_trans]
  exact Submodule.Quotient.equiv_trans L.carrierInDual M.carrierInDual N.carrierInDual
    e.dualCarrierEquiv f.dualCarrierEquiv e.map_carrierInDual f.map_carrierInDual
      (by simpa only [dualCarrierEquiv_trans] using (e.trans f).map_carrierInDual)

end Isometry

end IntegralLattice

end TauCeti
