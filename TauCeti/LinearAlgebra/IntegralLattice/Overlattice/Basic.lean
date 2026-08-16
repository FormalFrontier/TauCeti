/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.DiscriminantGroup

/-!
# Intermediate carriers of integral lattices

Let `L` be a nondegenerate integral lattice. An intermediate carrier is a `ℤ`-submodule `M` of
the ambient rational vector space satisfying

```text
L ≤ M ≤ Lᵛ.
```

This file proves the underlying correspondence in the theory of overlattices: intermediate
carriers are order-isomorphic to additive subgroups of the discriminant group `A_L = Lᵛ / L`.
The forward map sends `M` to its image in `A_L`, and the inverse sends a subgroup `H` to its
literal inverse image in `Lᵛ`. The characteristic membership lemmas state both constructions on
representatives. Every intermediate carrier is also proved to be a full `ℤ`-lattice in the common
rational ambient space.

Integrality and evenness of an intermediate carrier are deliberately not assumed here. Later
files restrict this correspondence to bilinear- and quadratic-isotropic subgroups, respectively.

## Main declarations

* `TauCeti.IntegralLattice.IntermediateCarrier`: the interval of carriers between `L` and `Lᵛ`.
* `TauCeti.IntegralLattice.intermediateCarrierDiscriminantSubgroupOrderIso`: the order
  isomorphism with subgroups of `A_L`.
* `TauCeti.IntegralLattice.IntermediateCarrier.discriminantSubgroup`: the image of an
  intermediate carrier in `A_L`.
* `TauCeti.IntegralLattice.intermediateCarrierOfDiscriminantSubgroup`: the inverse-image carrier
  attached to a subgroup of `A_L`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 4.
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

/-- Submodules of `Lᵛ` containing the embedded copy of `L` are the same as ambient submodules
lying between `L` and `Lᵛ`. -/
private def intermediateCarrierSubmoduleOrderIso :
    Set.Ici L.carrierInDual ≃o L.IntermediateCarrier := by
  let e := L.dualCarrier.mapIic
  have he : (e L.carrierInDual : Submodule ℤ V) = L.carrier := by
    have hcarrierInDual :
        L.carrierInDual = L.carrier.comap L.dualCarrier.subtype := by
      ext x
      exact L.mem_carrierInDual_iff x
    change L.carrierInDual.map L.dualCarrier.subtype = L.carrier
    rw [hcarrierInDual, Submodule.map_comap_subtype, inf_of_le_right L.le_dualCarrier]
  refine (e.Ici L.carrierInDual).trans
    { toFun := fun N ↦ ⟨N.1.1, he ▸ N.2, N.1.2⟩
      invFun := fun M ↦ ⟨⟨M.1, M.2.2⟩, by
        change (e L.carrierInDual : Submodule ℤ V) ≤ M.1
        rw [he]
        exact M.2.1⟩
      left_inv := fun N ↦ by rfl
      right_inv := fun M ↦ by rfl
      map_rel_iff' := Iff.rfl }

/-- **The intermediate-carrier correspondence.** Intermediate carriers `L ≤ M ≤ Lᵛ` are
order-isomorphic to additive subgroups of the discriminant group `A_L = Lᵛ / L`.

The construction is the composite of Mathlib's correspondence theorem for quotient modules and
its order isomorphism between submodules of a subtype and ambient submodules below that subtype. -/
def intermediateCarrierDiscriminantSubgroupOrderIso :
    L.IntermediateCarrier ≃o AddSubgroup L.DiscriminantGroup :=
  (intermediateCarrierSubmoduleOrderIso L).symm |>.trans
    (Submodule.comapMkQRelIso L.carrierInDual).symm |>.trans
      AddSubgroup.toIntSubmodule.symm

namespace IntermediateCarrier

/-- The subgroup `M / L` of the discriminant group attached to an intermediate carrier
`L ≤ M ≤ Lᵛ`. -/
def discriminantSubgroup (M : L.IntermediateCarrier) : AddSubgroup L.DiscriminantGroup :=
  L.intermediateCarrierDiscriminantSubgroupOrderIso M

/-- A dual-carrier representative belongs to `M / L` exactly when its underlying ambient vector
belongs to `M`. -/
@[simp]
theorem quotientMk_mem_discriminantSubgroup_iff (M : L.IntermediateCarrier)
    (x : L.dualCarrier) :
    Submodule.Quotient.mk x ∈ IntermediateCarrier.discriminantSubgroup L M ↔
      (x : V) ∈ M.1 := by
  change Submodule.Quotient.mk x ∈
      (AddSubgroup.toIntSubmodule.symm
        ((Submodule.comapMkQRelIso L.carrierInDual).symm
          ((intermediateCarrierSubmoduleOrderIso L).symm M))).toIntSubmodule ↔ _
  rw [AddSubgroup.toIntSubmodule.apply_symm_apply]
  let N : Set.Ici L.carrierInDual := (intermediateCarrierSubmoduleOrderIso L).symm M
  let Q : Submodule ℤ L.DiscriminantGroup :=
    (Submodule.comapMkQRelIso L.carrierInDual).symm N
  have hcomap : Q.comap L.carrierInDual.mkQ = N.1 := congrArg Subtype.val
    ((Submodule.comapMkQRelIso L.carrierInDual).apply_symm_apply N)
  change x ∈ Q.comap L.carrierInDual.mkQ ↔ _
  rw [hcomap]
  change x ∈ M.1.comap L.dualCarrier.subtype ↔ _
  rfl

end IntermediateCarrier

/-- The intermediate carrier obtained as the inverse image in `Lᵛ` of a subgroup of the
discriminant group. -/
def intermediateCarrierOfDiscriminantSubgroup (H : AddSubgroup L.DiscriminantGroup) :
    L.IntermediateCarrier :=
  L.intermediateCarrierDiscriminantSubgroupOrderIso.symm H

/-- The carrier attached to `H ≤ A_L` is its literal inverse image in the dual carrier:
`x ∈ L_H` exactly when `x ∈ Lᵛ` and the class of `x` belongs to `H`. -/
@[simp]
theorem mem_intermediateCarrierOfDiscriminantSubgroup_iff
    (H : AddSubgroup L.DiscriminantGroup) (x : V) :
    x ∈ (L.intermediateCarrierOfDiscriminantSubgroup H).1 ↔
      ∃ hx : x ∈ L.dualCarrier, Submodule.Quotient.mk (⟨x, hx⟩ : L.dualCarrier) ∈ H := by
  let M := L.intermediateCarrierOfDiscriminantSubgroup H
  have hMH : IntermediateCarrier.discriminantSubgroup L M = H :=
    L.intermediateCarrierDiscriminantSubgroupOrderIso.apply_symm_apply H
  constructor
  · intro hx
    have hxdual : x ∈ L.dualCarrier := M.2.2 hx
    refine ⟨hxdual, ?_⟩
    rw [← hMH, IntermediateCarrier.quotientMk_mem_discriminantSubgroup_iff L]
    exact hx
  · rintro ⟨hxdual, hxH⟩
    rw [← hMH, IntermediateCarrier.quotientMk_mem_discriminantSubgroup_iff L] at hxH
    exact hxH

/-- Passing from a subgroup of `A_L` to its inverse-image carrier and back recovers the subgroup. -/
@[simp]
theorem discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup
    (H : AddSubgroup L.DiscriminantGroup) :
    IntermediateCarrier.discriminantSubgroup L
      (L.intermediateCarrierOfDiscriminantSubgroup H) = H :=
  L.intermediateCarrierDiscriminantSubgroupOrderIso.apply_symm_apply H

/-- Passing from an intermediate carrier to its discriminant subgroup and back recovers the
carrier. -/
@[simp]
theorem intermediateCarrierOfDiscriminantSubgroup_discriminantSubgroup
    (M : L.IntermediateCarrier) :
    L.intermediateCarrierOfDiscriminantSubgroup
      (IntermediateCarrier.discriminantSubgroup L M) = M :=
  L.intermediateCarrierDiscriminantSubgroupOrderIso.symm_apply_apply M

/-- Containment of intermediate carriers is detected by containment of their discriminant
subgroups. -/
@[simp]
theorem discriminantSubgroup_le_discriminantSubgroup_iff
    (M N : L.IntermediateCarrier) :
    IntermediateCarrier.discriminantSubgroup L M ≤
      IntermediateCarrier.discriminantSubgroup L N ↔ M ≤ N :=
  L.intermediateCarrierDiscriminantSubgroupOrderIso.le_iff_le

/-- Containment of subgroups of the discriminant group is detected by containment of their
inverse-image carriers. -/
@[simp]
theorem intermediateCarrierOfDiscriminantSubgroup_le_iff
    (H K : AddSubgroup L.DiscriminantGroup) :
    L.intermediateCarrierOfDiscriminantSubgroup H ≤
        L.intermediateCarrierOfDiscriminantSubgroup K ↔ H ≤ K :=
  L.intermediateCarrierDiscriminantSubgroupOrderIso.symm.le_iff_le

variable [L.IsNondegenerate]

/-- Every intermediate carrier is a full `ℤ`-lattice in the same rational ambient space.
Finite generation follows because it is a submodule of the full dual lattice, while spanning
follows because it contains `L`. -/
instance instIsLatticeIntermediateCarrier (M : L.IntermediateCarrier) : M.1.IsLattice ℚ := by
  apply Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ M.2.1
  exact isNoetherian_submodule.mp (isNoetherian_of_le M.2.2) M.1 le_rfl

end IntegralLattice

end TauCeti
