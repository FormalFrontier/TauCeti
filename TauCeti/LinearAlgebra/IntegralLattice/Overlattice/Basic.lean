/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Order.LatticeIntervals
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
The forward map sends `M` to its image `M / L` in `A_L`, and the inverse sends a subgroup
`H ≤ A_L` to its literal inverse image in `Lᵛ`, written `L_H` below. The characteristic
membership lemmas state both constructions on representatives. The interval of intermediate
carriers is a bounded order, with `⊥` the carrier of `L` and `⊤` its dual carrier. Every
intermediate carrier is also proved to be a full `ℤ`-lattice in the common rational ambient space
when `L` is nondegenerate. The correspondence and its membership, inverse, and order lemmas do not
require nondegeneracy; only this fullness result does, and even it is unconditional for `⊥`, which
is the carrier of `L` itself.

Integrality and evenness of an intermediate carrier are deliberately not assumed here; the
restrictions of the correspondence they cut out live in
`TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic`.

## Main declarations

* `TauCeti.IntegralLattice.IntermediateCarrier`: the interval of carriers between `L` and `Lᵛ`.
* `TauCeti.IntegralLattice.intermediateCarrierOrderIsoDiscriminantSubgroup`: the order
  isomorphism with subgroups of `A_L`.
* `TauCeti.IntegralLattice.discriminantSubgroup`: the image `M / L` of an
  intermediate carrier in `A_L`.
* `TauCeti.IntegralLattice.intermediateCarrierOfDiscriminantSubgroup`: the inverse-image carrier
  `L_H` attached to a subgroup `H` of `A_L`.

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

/-- The endpoints of the intermediate-carrier interval are ordered, so `L.IntermediateCarrier` is
a bounded order with `⊥` the carrier of `L` and `⊤` its dual carrier. -/
instance instFactCarrierLeDualCarrier (L : IntegralLattice V) :
    Fact (L.carrier ≤ L.dualCarrier) :=
  ⟨L.le_dualCarrier⟩

variable (L : IntegralLattice V)

/-- **The intermediate-carrier correspondence.** Intermediate carriers `L ≤ M ≤ Lᵛ` are
order-isomorphic to additive subgroups of the discriminant group `A_L = Lᵛ / L`.

The construction is the composite of Mathlib's correspondence theorem for quotient modules and
its order isomorphism between submodules of a subtype and ambient submodules below that subtype:
`Submodule.comapMkQRelIso`, `Submodule.mapIic`, and `AddSubgroup.toIntSubmodule`. -/
def intermediateCarrierOrderIsoDiscriminantSubgroup :
    L.IntermediateCarrier ≃o AddSubgroup L.DiscriminantGroup :=
  (TauCeti.iccOrderIsoQuotientOfMapEq L.carrierInDual
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

/-- The intermediate-carrier correspondence is the generic interval/quotient correspondence for
the embedded carrier, read as an additive subgroup. -/
private theorem intermediateCarrierOrderIsoDiscriminantSubgroup_eq_toAddSubgroup
    (M : L.IntermediateCarrier) :
    L.intermediateCarrierOrderIsoDiscriminantSubgroup M =
      (TauCeti.iccOrderIsoQuotientOfMapEq L.carrierInDual
        L.map_carrierInDual_subtype M).toAddSubgroup := by
  rw [intermediateCarrierOrderIsoDiscriminantSubgroup, OrderIso.trans_apply,
    AddSubgroup.toIntSubmodule_symm]

/-- A dual-carrier representative belongs to `M / L` exactly when its underlying ambient vector
belongs to `M`. -/
@[simp]
theorem mk_mem_discriminantSubgroup_iff (M : L.IntermediateCarrier)
    (x : L.dualCarrier) :
    Submodule.Quotient.mk x ∈ L.discriminantSubgroup M ↔
      (x : V) ∈ M.1 := by
  rw [← L.intermediateCarrierOrderIsoDiscriminantSubgroup_apply,
    L.intermediateCarrierOrderIsoDiscriminantSubgroup_eq_toAddSubgroup,
    Submodule.mem_toAddSubgroup]
  exact TauCeti.mk_mem_iccOrderIsoQuotientOfMapEq_iff _ _ M x

/-- The intermediate carrier `L_H` obtained as the inverse image in `Lᵛ` of a subgroup of the
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

/-- A dual-carrier representative belongs to `L_H` exactly when its class belongs to `H`. -/
@[simp]
theorem coe_mem_intermediateCarrierOfDiscriminantSubgroup_iff
    (H : AddSubgroup L.DiscriminantGroup) (x : L.dualCarrier) :
    (x : V) ∈ (L.intermediateCarrierOfDiscriminantSubgroup H).1 ↔
      Submodule.Quotient.mk x ∈ H := by
  have hMH : L.discriminantSubgroup (L.intermediateCarrierOfDiscriminantSubgroup H) = H :=
    L.intermediateCarrierOrderIsoDiscriminantSubgroup.apply_symm_apply H
  conv_rhs => rw [← hMH]
  exact (L.mk_mem_discriminantSubgroup_iff _ x).symm

/-- The carrier attached to `H ≤ A_L` is its literal inverse image in the dual carrier:
an ambient vector lies in `L_H` exactly when it lies in `Lᵛ` and its class belongs to `H`. -/
theorem mem_intermediateCarrierOfDiscriminantSubgroup_iff
    (H : AddSubgroup L.DiscriminantGroup) (x : V) :
    x ∈ (L.intermediateCarrierOfDiscriminantSubgroup H).1 ↔
      ∃ hx : x ∈ L.dualCarrier, Submodule.Quotient.mk (⟨x, hx⟩ : L.dualCarrier) ∈ H := by
  constructor
  · intro hx
    have hxdual : x ∈ L.dualCarrier :=
      (L.intermediateCarrierOfDiscriminantSubgroup H).2.2 hx
    exact ⟨hxdual,
      (L.coe_mem_intermediateCarrierOfDiscriminantSubgroup_iff H ⟨x, hxdual⟩).mp hx⟩
  · rintro ⟨hxdual, hxH⟩
    exact (L.coe_mem_intermediateCarrierOfDiscriminantSubgroup_iff H ⟨x, hxdual⟩).mpr hxH

/-- The inverse image of the bottom discriminant subgroup is the bottom intermediate carrier. -/
@[simp]
theorem intermediateCarrierOfDiscriminantSubgroup_bot :
    L.intermediateCarrierOfDiscriminantSubgroup ⊥ = ⊥ :=
  L.intermediateCarrierOrderIsoDiscriminantSubgroup.symm.map_bot

/-- The inverse image of the top discriminant subgroup is the top intermediate carrier. -/
@[simp]
theorem intermediateCarrierOfDiscriminantSubgroup_top :
    L.intermediateCarrierOfDiscriminantSubgroup ⊤ = ⊤ :=
  L.intermediateCarrierOrderIsoDiscriminantSubgroup.symm.map_top

/-- The inverse image of the bottom discriminant subgroup is the original carrier. -/
theorem coe_intermediateCarrierOfDiscriminantSubgroup_bot :
    (L.intermediateCarrierOfDiscriminantSubgroup ⊥).1 = L.carrier := by
  rw [L.intermediateCarrierOfDiscriminantSubgroup_bot]
  exact Set.Icc.coe_bot L.carrier L.dualCarrier

/-- The inverse image of the top discriminant subgroup is the dual carrier. -/
theorem coe_intermediateCarrierOfDiscriminantSubgroup_top :
    (L.intermediateCarrierOfDiscriminantSubgroup ⊤).1 = L.dualCarrier := by
  rw [L.intermediateCarrierOfDiscriminantSubgroup_top]
  exact Set.Icc.coe_top L.carrier L.dualCarrier

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

/-- The discriminant subgroup of the bottom intermediate carrier, the carrier of `L` itself, is
bottom. -/
@[simp]
theorem discriminantSubgroup_bot : L.discriminantSubgroup ⊥ = ⊥ :=
  (L.intermediateCarrierOrderIsoDiscriminantSubgroup_apply ⊥).symm.trans
    L.intermediateCarrierOrderIsoDiscriminantSubgroup.map_bot

/-- The discriminant subgroup of the top intermediate carrier, the dual carrier, is top. -/
@[simp]
theorem discriminantSubgroup_top : L.discriminantSubgroup ⊤ = ⊤ :=
  (L.intermediateCarrierOrderIsoDiscriminantSubgroup_apply ⊤).symm.trans
    L.intermediateCarrierOrderIsoDiscriminantSubgroup.map_top

/-- Containment of intermediate carriers is detected by containment of their discriminant
subgroups. -/
@[simp]
theorem discriminantSubgroup_le_iff (M N : L.IntermediateCarrier) :
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

/-- The bottom intermediate carrier is the carrier of `L` itself, hence a full `ℤ`-lattice in the
ambient rational space. No nondegeneracy is required. -/
instance instIsLatticeBotIntermediateCarrier : (⊥ : L.IntermediateCarrier).1.IsLattice ℚ := by
  rw [Set.Icc.coe_bot]
  infer_instance

variable [L.IsNondegenerate]

/-- Every intermediate carrier of a nondegenerate integral lattice is a full `ℤ`-lattice in the
same rational ambient space. -/
instance instIsLatticeIntermediateCarrier (M : L.IntermediateCarrier) : M.1.IsLattice ℚ := by
  apply Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ M.2.1
  exact isNoetherian_submodule.mp (isNoetherian_of_le M.2.2) M.1 le_rfl

end IntegralLattice

end TauCeti
