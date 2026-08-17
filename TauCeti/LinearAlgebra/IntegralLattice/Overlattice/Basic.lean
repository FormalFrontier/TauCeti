/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Module.Submodule.Quotient
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Group

/-!
# Intermediate carriers of integral lattices

Let `L` be an integral lattice. An intermediate carrier is a `ℤ`-submodule `M` of the ambient
rational vector space satisfying

```text
L ≤ M ≤ Lᵛ.
```

This file proves the underlying correspondence in the theory of overlattices: intermediate
carriers are order-isomorphic to additive subgroups of the discriminant group `A_L = Lᵛ / L`.
The forward map sends `M` to its image in `A_L`, and the inverse sends a subgroup `H` to its
literal inverse image in `Lᵛ`. The characteristic membership lemmas state both constructions on
representatives. Every intermediate carrier is also proved to be a full `ℤ`-lattice in the common
rational ambient space when `L` is nondegenerate. The correspondence and its membership, inverse,
and order lemmas do not require nondegeneracy; only this fullness result does.

Integrality and evenness of an intermediate carrier are deliberately not assumed here. Later
files restrict this correspondence to bilinear- and quadratic-isotropic subgroups, respectively.

## Main declarations

* `TauCeti.IntegralLattice.IntermediateCarrier`: the interval of carriers between `L` and `Lᵛ`.
* `TauCeti.IntegralLattice.intermediateCarrierOrderIsoDiscriminantSubgroup`: the order
  isomorphism with subgroups of `A_L`.
* `TauCeti.IntegralLattice.discriminantSubgroup`: the image of an
  intermediate carrier in `A_L`.
* `TauCeti.IntegralLattice.intermediateCarrierOfDiscriminantSubgroup`: the inverse-image carrier
  attached to a subgroup of `A_L`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 4.
* `TauCetiRoadmap/IntegralLattices/Suggested.lean` (`intermediateOrderIsoSubgroup`).
-/

public section

open Module

namespace TauCeti

universe u

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- The type of `ℤ`-submodules lying between an integral lattice and its dual carrier. -/
abbrev IntermediateCarrier (L : IntegralLattice V) :=
  Set.Icc L.carrier L.dualCarrier

variable (L : IntegralLattice V)

/-- **The intermediate-carrier correspondence.** Intermediate carriers `L ≤ M ≤ Lᵛ` are
order-isomorphic to additive subgroups of the discriminant group `A_L = Lᵛ / L`.

The construction is the composite of Mathlib's correspondence theorem for quotient modules and
its order isomorphism between submodules of a subtype and ambient submodules below that subtype:
`Submodule.comapMkQRelIso`, `Submodule.mapIic`, and `AddSubgroup.toIntSubmodule`. -/
def intermediateCarrierOrderIsoDiscriminantSubgroup :
    L.IntermediateCarrier ≃o AddSubgroup L.DiscriminantGroup :=
  (TauCeti.Submodule.iccOrderIsoQuotientOfMapEq L.carrierInDual
    L.map_carrierInDual_subtype).trans
    AddSubgroup.toIntSubmodule.symm

/-- The subgroup `M / L` of the discriminant group attached to an intermediate carrier
`L ≤ M ≤ Lᵛ`. -/
def discriminantSubgroup (M : L.IntermediateCarrier) : AddSubgroup L.DiscriminantGroup :=
  L.intermediateCarrierOrderIsoDiscriminantSubgroup M

/-- Evaluating the intermediate-carrier order isomorphism is the named discriminant-subgroup
construction. -/
@[simp]
theorem intermediateCarrierOrderIsoDiscriminantSubgroup_apply (M : L.IntermediateCarrier) :
    L.intermediateCarrierOrderIsoDiscriminantSubgroup M = L.discriminantSubgroup M :=
  (rfl)

/-- A dual-carrier representative belongs to `M / L` exactly when its underlying ambient vector
belongs to `M`. -/
@[simp]
theorem mk_mem_discriminantSubgroup_iff (M : L.IntermediateCarrier)
    (x : L.dualCarrier) :
    Submodule.Quotient.mk x ∈ L.discriminantSubgroup M ↔
      (x : V) ∈ M.1 := by
  simpa only [discriminantSubgroup, intermediateCarrierOrderIsoDiscriminantSubgroup,
    OrderIso.trans_apply, AddSubgroup.toIntSubmodule_symm, Submodule.mem_toAddSubgroup] using
      TauCeti.Submodule.mk_mem_iccOrderIsoQuotientOfMapEq_iff L.carrierInDual
        L.map_carrierInDual_subtype M x

/-- The intermediate carrier obtained as the inverse image in `Lᵛ` of a subgroup of the
discriminant group. -/
def intermediateCarrierOfDiscriminantSubgroup (H : AddSubgroup L.DiscriminantGroup) :
    L.IntermediateCarrier :=
  L.intermediateCarrierOrderIsoDiscriminantSubgroup.symm H

/-- Evaluating the inverse intermediate-carrier order isomorphism is the named inverse-image
construction. -/
@[simp]
theorem intermediateCarrierOrderIsoDiscriminantSubgroup_symm_apply
    (H : AddSubgroup L.DiscriminantGroup) :
    L.intermediateCarrierOrderIsoDiscriminantSubgroup.symm H =
      L.intermediateCarrierOfDiscriminantSubgroup H :=
  (rfl)

/-- The carrier attached to `H ≤ A_L` is its literal inverse image in the dual carrier:
`x ∈ L_H` exactly when `x ∈ Lᵛ` and the class of `x` belongs to `H`. -/
@[simp]
theorem mem_intermediateCarrierOfDiscriminantSubgroup_iff
    (H : AddSubgroup L.DiscriminantGroup) (x : V) :
    x ∈ (L.intermediateCarrierOfDiscriminantSubgroup H).1 ↔
      ∃ hx : x ∈ L.dualCarrier, Submodule.Quotient.mk (⟨x, hx⟩ : L.dualCarrier) ∈ H := by
  let M := L.intermediateCarrierOfDiscriminantSubgroup H
  have hMH : L.discriminantSubgroup M = H :=
    L.intermediateCarrierOrderIsoDiscriminantSubgroup.apply_symm_apply H
  constructor
  · intro hx
    have hxdual : x ∈ L.dualCarrier := M.2.2 hx
    refine ⟨hxdual, ?_⟩
    rw [← hMH, L.mk_mem_discriminantSubgroup_iff]
    exact hx
  · rintro ⟨hxdual, hxH⟩
    rw [← hMH, L.mk_mem_discriminantSubgroup_iff] at hxH
    exact hxH

/-- The inverse image of the bottom discriminant subgroup is the original carrier. -/
@[simp]
theorem intermediateCarrierOfDiscriminantSubgroup_bot :
    (L.intermediateCarrierOfDiscriminantSubgroup ⊥).1 = L.carrier := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxdual, hxzero⟩ :=
      (L.mem_intermediateCarrierOfDiscriminantSubgroup_iff ⊥ x).mp hx
    exact (L.discriminantGroup_mk_eq_zero_iff ⟨x, hxdual⟩).mp
      (AddSubgroup.mem_bot.mp hxzero)
  · intro hx
    refine (L.mem_intermediateCarrierOfDiscriminantSubgroup_iff ⊥ x).mpr
      ⟨L.le_dualCarrier hx, ?_⟩
    exact AddSubgroup.mem_bot.mpr
      ((L.discriminantGroup_mk_eq_zero_iff ⟨x, L.le_dualCarrier hx⟩).mpr hx)

/-- The inverse image of the top discriminant subgroup is the dual carrier. -/
@[simp]
theorem intermediateCarrierOfDiscriminantSubgroup_top :
    (L.intermediateCarrierOfDiscriminantSubgroup ⊤).1 = L.dualCarrier := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxdual, _⟩ :=
      (L.mem_intermediateCarrierOfDiscriminantSubgroup_iff ⊤ x).mp hx
    exact hxdual
  · intro hx
    exact (L.mem_intermediateCarrierOfDiscriminantSubgroup_iff ⊤ x).mpr
      ⟨hx, AddSubgroup.mem_top _⟩

/-- Passing from a subgroup of `A_L` to its inverse-image carrier and back recovers the subgroup. -/
@[simp]
theorem discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup
    (H : AddSubgroup L.DiscriminantGroup) :
    L.discriminantSubgroup (L.intermediateCarrierOfDiscriminantSubgroup H) = H :=
  L.intermediateCarrierOrderIsoDiscriminantSubgroup.apply_symm_apply H

/-- Passing from an intermediate carrier to its discriminant subgroup and back recovers the
carrier. -/
@[simp]
theorem intermediateCarrierOfDiscriminantSubgroup_discriminantSubgroup
    (M : L.IntermediateCarrier) :
    L.intermediateCarrierOfDiscriminantSubgroup
      (L.discriminantSubgroup M) = M :=
  L.intermediateCarrierOrderIsoDiscriminantSubgroup.symm_apply_apply M

/-- The discriminant subgroup of the original carrier is bottom. -/
@[simp]
theorem discriminantSubgroup_bot :
    L.discriminantSubgroup
      (⟨L.carrier, le_rfl, L.le_dualCarrier⟩ : L.IntermediateCarrier) = ⊥ := by
  have hcarrier : (⟨L.carrier, le_rfl, L.le_dualCarrier⟩ : L.IntermediateCarrier) =
      L.intermediateCarrierOfDiscriminantSubgroup ⊥ :=
    Subtype.ext L.intermediateCarrierOfDiscriminantSubgroup_bot.symm
  rw [hcarrier]
  exact L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup ⊥

/-- The discriminant subgroup of the dual carrier is top. -/
@[simp]
theorem discriminantSubgroup_top :
    L.discriminantSubgroup
      (⟨L.dualCarrier, L.le_dualCarrier, le_rfl⟩ : L.IntermediateCarrier) = ⊤ := by
  have hdual : (⟨L.dualCarrier, L.le_dualCarrier, le_rfl⟩ : L.IntermediateCarrier) =
      L.intermediateCarrierOfDiscriminantSubgroup ⊤ :=
    Subtype.ext L.intermediateCarrierOfDiscriminantSubgroup_top.symm
  rw [hdual]
  exact L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup ⊤

/-- Containment of intermediate carriers is detected by containment of their discriminant
subgroups. -/
@[simp]
theorem discriminantSubgroup_le_discriminantSubgroup_iff
    (M N : L.IntermediateCarrier) :
    L.discriminantSubgroup M ≤ L.discriminantSubgroup N ↔ M ≤ N :=
  L.intermediateCarrierOrderIsoDiscriminantSubgroup.le_iff_le

/-- Containment of subgroups of the discriminant group is detected by containment of their
inverse-image carriers. -/
@[simp]
theorem intermediateCarrierOfDiscriminantSubgroup_le_iff
    (H K : AddSubgroup L.DiscriminantGroup) :
    L.intermediateCarrierOfDiscriminantSubgroup H ≤
        L.intermediateCarrierOfDiscriminantSubgroup K ↔ H ≤ K :=
  L.intermediateCarrierOrderIsoDiscriminantSubgroup.symm.le_iff_le

variable [L.IsNondegenerate]

/-- Every intermediate carrier of a nondegenerate integral lattice is a full `ℤ`-lattice in the
same rational ambient space. -/
instance instIsLatticeIntermediateCarrier (M : L.IntermediateCarrier) : M.1.IsLattice ℚ := by
  apply Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ M.2.1
  exact isNoetherian_submodule.mp (isNoetherian_of_le M.2.2) M.1 le_rfl

end IntegralLattice

end TauCeti
