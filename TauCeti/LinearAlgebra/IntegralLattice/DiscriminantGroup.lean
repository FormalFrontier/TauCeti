/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import TauCeti.LinearAlgebra.IntegralLattice.Dual
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry
import all TauCeti.LinearAlgebra.IntegralLattice.Basic

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
* `TauCeti.IntegralLattice.discriminantGroupMk`: the quotient map.
* `TauCeti.IntegralLattice.instFiniteDiscriminantGroup`: finiteness in the nondegenerate case.
* `TauCeti.IntegralLattice.Isometry.dualCarrierEquiv`: transport of dual carriers by an isometry.
* `TauCeti.IntegralLattice.Isometry.discriminantGroupEquiv`: the induced equivalence of
  discriminant groups.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md` (Layer 2).
-/

public section

open Module

namespace TauCeti

universe u v w

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- The canonical inclusion of an integral lattice carrier into its dual carrier. -/
def carrierToDual (L : IntegralLattice V) : L →ₗ[ℤ] L.dualCarrier :=
  Submodule.inclusion L.le_dualCarrier

/-- The inclusion into the dual carrier does not change the underlying ambient vector. -/
@[simp]
theorem coe_carrierToDual (L : IntegralLattice V) (x : L) :
    (L.carrierToDual x : V) = x := by
  simp [carrierToDual]

/-- The canonical inclusion of the carrier into its dual is injective. -/
theorem carrierToDual_injective (L : IntegralLattice V) :
    Function.Injective L.carrierToDual :=
  Submodule.inclusion_injective L.le_dualCarrier

/-- The original carrier, regarded as a submodule of the subtype `L.dualCarrier`. -/
def carrierInDual (L : IntegralLattice V) : Submodule ℤ L.dualCarrier :=
  L.carrier.comap L.dualCarrier.subtype

/-- Membership in `carrierInDual` is membership of the underlying ambient vector in the original
carrier. -/
@[simp]
theorem mem_carrierInDual_iff (L : IntegralLattice V) (x : L.dualCarrier) :
    x ∈ L.carrierInDual ↔ (x : V) ∈ L.carrier :=
  Iff.rfl

/-- The carrier inside the dual is the range of the canonical inclusion. -/
theorem carrierInDual_eq_range (L : IntegralLattice V) :
    L.carrierInDual = LinearMap.range L.carrierToDual := by
  ext x
  constructor
  · intro hx
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext rfl
  · rintro ⟨x, rfl⟩
    exact x.2

/-- The copy of the carrier inside the dual carrier has the same rank as the carrier. -/
theorem finrank_carrierInDual (L : IntegralLattice V) :
    Module.finrank ℤ L.carrierInDual = Module.finrank ℤ L := by
  rw [L.carrierInDual_eq_range, LinearMap.finrank_range_of_inj L.carrierToDual_injective]

/-- The discriminant group `A_L = Lᵛ / L`, as an actual quotient of the dual-carrier subtype by
the inverse image of the original carrier. -/
abbrev DiscriminantGroup (L : IntegralLattice V) : Type u :=
  L.dualCarrier ⧸ L.carrierInDual

/-- The canonical map from the dual carrier to the discriminant group. -/
def discriminantGroupMk (L : IntegralLattice V) :
    L.dualCarrier →ₗ[ℤ] L.DiscriminantGroup :=
  L.carrierInDual.mkQ

/-- The discriminant-group quotient map sends a dual vector to its quotient class. -/
@[simp]
theorem discriminantGroupMk_apply (L : IntegralLattice V) (x : L.dualCarrier) :
    L.discriminantGroupMk x = Submodule.Quotient.mk x := by
  simp [discriminantGroupMk]

/-- Every discriminant-group class has a representative in the dual carrier. -/
theorem discriminantGroupMk_surjective (L : IntegralLattice V) :
    Function.Surjective L.discriminantGroupMk :=
  Submodule.mkQ_surjective L.carrierInDual

/-- The kernel of the discriminant-group quotient map is the original carrier inside the dual. -/
@[simp]
theorem ker_discriminantGroupMk (L : IntegralLattice V) :
    LinearMap.ker L.discriminantGroupMk = L.carrierInDual :=
  Submodule.ker_mkQ L.carrierInDual

/-- A representative defines the zero discriminant class exactly when its ambient vector belongs
to the original carrier. -/
theorem discriminantGroupMk_eq_zero_iff (L : IntegralLattice V) (x : L.dualCarrier) :
    L.discriminantGroupMk x = 0 ↔ (x : V) ∈ L.carrier := by
  rw [discriminantGroupMk_apply, Submodule.Quotient.mk_eq_zero,
    L.mem_carrierInDual_iff]

/-- Two representatives define the same discriminant class exactly when their difference belongs
to the original carrier. -/
theorem discriminantGroupMk_eq_iff (L : IntegralLattice V) (x y : L.dualCarrier) :
    L.discriminantGroupMk x = L.discriminantGroupMk y ↔
      ((x - y : L.dualCarrier) : V) ∈ L.carrier := by
  rw [discriminantGroupMk_apply, discriminantGroupMk_apply, Submodule.Quotient.eq,
    L.mem_carrierInDual_iff]

/-- Eliminate a discriminant-group class by choosing a representative in the dual carrier. -/
@[elab_as_elim]
theorem DiscriminantGroup.induction_on (L : IntegralLattice V)
    {P : L.DiscriminantGroup → Prop} (a : L.DiscriminantGroup)
    (h : ∀ x : L.dualCarrier, P (L.discriminantGroupMk x)) : P a := by
  induction a using Submodule.Quotient.induction_on with
  | _ x => exact h x

/-- The discriminant group of a nondegenerate integral lattice is finite. -/
noncomputable instance instFiniteDiscriminantGroup (L : IntegralLattice V) [L.IsNondegenerate] :
    Finite L.DiscriminantGroup := by
  apply Submodule.finiteQuotientOfFreeOfRankEq L.carrierInDual
  rw [L.finrank_carrierInDual, L.finrank_carrier, L.finrank_dualCarrier]

namespace Isometry

variable {W : Type v} {U : Type w}
variable [AddCommGroup W] [Module ℚ W]
variable [AddCommGroup U] [Module ℚ U]
variable {L : IntegralLattice V} {M : IntegralLattice W} {N : IntegralLattice U}

/-- An isometry carries an ambient vector into the target dual carrier exactly when the original
vector belongs to the source dual carrier. -/
theorem apply_mem_dualCarrier_iff (e : Isometry L M) (x : V) :
    e x ∈ M.dualCarrier ↔ x ∈ L.dualCarrier := by
  constructor
  · intro hx y hy
    have hxy := hx (e y) ((e.apply_mem_carrier_iff y).2 hy)
    rw [e.map_app x y] at hxy
    exact hxy
  · intro hx y hy
    have hxy := hx (e.symm y) ((e.symm.apply_mem_carrier_iff y).2 hy)
    rw [← e.map_app x (e.symm y), e.apply_symm_apply] at hxy
    exact hxy

/-- An isometry restricts to an integral linear equivalence of dual carriers. -/
def dualCarrierEquiv (e : Isometry L M) : L.dualCarrier ≃ₗ[ℤ] M.dualCarrier :=
  ((e : V ≃ₗ[ℚ] W).restrictScalars ℤ).ofSubmodules L.dualCarrier M.dualCarrier (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (e.apply_mem_dualCarrier_iff x).2 hx
    · intro y hy
      refine ⟨e.symm y, (e.symm.apply_mem_dualCarrier_iff y).2 hy, e.apply_symm_apply y⟩)

/-- The dual-carrier equivalence acts by the underlying ambient isometry. -/
@[simp]
theorem coe_dualCarrierEquiv_apply (e : Isometry L M) (x : L.dualCarrier) :
    (e.dualCarrierEquiv x : W) = e (x : V) := by
  simp [dualCarrierEquiv]

/-- The inverse dual-carrier equivalence is induced by the inverse isometry. -/
@[simp]
theorem dualCarrierEquiv_symm (e : Isometry L M) :
    e.dualCarrierEquiv.symm = e.symm.dualCarrierEquiv := by
  ext x
  simp only [dualCarrierEquiv, LinearEquiv.ofSubmodules_symm_apply,
    LinearEquiv.ofSubmodules_apply]
  change (e : V ≃ₗ[ℚ] W).symm (x : W) = e.symm (x : W)
  rw [e.coe_symm]

/-- The dual-carrier equivalence maps the embedded original carrier onto the embedded target
carrier. -/
theorem map_carrierInDual (e : Isometry L M) :
    L.carrierInDual.map e.dualCarrierEquiv.toLinearMap = M.carrierInDual := by
  ext y
  rw [Submodule.mem_map_equiv]
  change (e.dualCarrierEquiv.symm y : V) ∈ L.carrier ↔ (y : W) ∈ M.carrier
  rw [e.dualCarrierEquiv_symm]
  change e.symm (y : W) ∈ L.carrier ↔ (y : W) ∈ M.carrier
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
  ext x
  induction x using DiscriminantGroup.induction_on L with
  | _ x =>
      simp only [LinearEquiv.refl_apply, discriminantGroupMk_apply]
      rw [discriminantGroupEquiv_mk]
      congr 1
      apply Subtype.ext
      simp

/-- The equivalence induced by an inverse isometry is the inverse of the induced equivalence. -/
@[simp]
theorem discriminantGroupEquiv_symm (e : Isometry L M) :
    e.symm.discriminantGroupEquiv = e.discriminantGroupEquiv.symm := by
  ext x
  induction x using DiscriminantGroup.induction_on M with
  | _ x =>
      change e.symm.discriminantGroupEquiv (M.discriminantGroupMk x) =
        e.discriminantGroupEquiv.symm (M.discriminantGroupMk x)
      simp only [discriminantGroupMk_apply]
      apply e.discriminantGroupEquiv.injective
      rw [discriminantGroupEquiv_mk, discriminantGroupEquiv_mk,
        LinearEquiv.apply_symm_apply]
      congr 1
      apply Subtype.ext
      simp

/-- The equivalence induced by a composite isometry is the composite of the induced
equivalences. -/
@[simp]
theorem discriminantGroupEquiv_trans (e : Isometry L M) (f : Isometry M N) :
    (e.trans f).discriminantGroupEquiv =
      e.discriminantGroupEquiv.trans f.discriminantGroupEquiv := by
  ext x
  induction x using DiscriminantGroup.induction_on L with
  | _ x =>
      simp only [discriminantGroupMk_apply]
      rw [LinearEquiv.trans_apply, discriminantGroupEquiv_mk, discriminantGroupEquiv_mk,
        discriminantGroupEquiv_mk]
      congr 1
      apply Subtype.ext
      rw [coe_dualCarrierEquiv_apply, coe_dualCarrierEquiv_apply,
        coe_dualCarrierEquiv_apply, trans_apply]

end Isometry

end IntegralLattice

end TauCeti
