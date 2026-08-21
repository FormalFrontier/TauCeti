/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.IntegralLattice.Dual.Finiteness

public import TauCeti.LinearAlgebra.IntegralLattice.Index
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular

/-!
# The index and the discriminant of an overlattice

Let `L` be an integral lattice and let `L ≤ M ≤ Lᵛ` be an intermediate carrier. This file
computes the two numerical invariants of the gluing correspondence:

```text
[M : L] = #(M / L) = |M / L ≤ A_L|,      disc(M) · [M : L]² = disc(L)  (for `M` integral).
```

The first equality is the index in the group-theoretic sense and holds for every intermediate
carrier. The second needs `M` to be integral, so that `M` is itself an integral lattice and has a
discriminant of its own; it says that enlarging a lattice by a subgroup of its discriminant group
divides the discriminant by the square of the order of that subgroup. By the correspondence of
`TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic`, integrality of the carrier glued
along a subgroup `H` of `A_L` is the vanishing of the discriminant pairing on `H`, that is the
isotropy of `H` when `L` is nondegenerate. So this is the numerical half of Nikulin's gluing
theory: an even lattice glued along an isotropic subgroup `H` has discriminant `disc(L) / |H|²`,
and is unimodular exactly when `|H|² = disc(L)`.

The scaling law itself is not proved here: it is the general statement
`TauCeti.IntegralLattice.discriminant_eq_mul_relIndex_sq` about an arbitrary pair of nested
integral lattices sharing their ambient rational form, from
`TauCeti.LinearAlgebra.IntegralLattice.Index`. What this file supplies is the identification of
the index of an intermediate carrier with the order of the subgroup it cuts out in `A_L`.

The earlier overlattice theory packages a full integral intermediate carrier as an integral
lattice in its own right through `IntermediateCarrier.IsIntegral.toIntegralLattice`, which keeps
the ambient form and therefore preserves nondegeneracy; evenness of the carrier makes it an even
lattice.

## Main definitions

* `TauCeti.IntegralLattice.IntermediateCarrier.relIndex`: the relative index of two intermediate
  carriers `M N`, that is the index of `M ⊓ N` in `N`; it is `[N : M]` when `M ≤ N`.
* `TauCeti.IntegralLattice.IntermediateCarrier.index`: the index `[M : L]`.

## Main results

* `TauCeti.IntegralLattice.IntermediateCarrier.index_eq_natCard_discriminantSubgroup`: the index
  of an intermediate carrier is the order of the subgroup it cuts out in `A_L`.
* `TauCeti.IntegralLattice.IntermediateCarrier.index_intermediateCarrierOfDiscriminantSubgroup`:
  `[L_H : L] = |H|`.
* `TauCeti.IntegralLattice.IntermediateCarrier.relIndex_mul_relIndex`: multiplicativity of the
  index along a chain of intermediate carriers.
* `TauCeti.IntegralLattice.IntermediateCarrier.relIndex_eq_relIndex_discriminantSubgroup`: relative
  index is preserved by the intermediate-carrier/discriminant-subgroup correspondence.
* `TauCeti.IntegralLattice.IntermediateCarrier.relIndex_intermediateCarrierOfDiscriminantSubgroup`:
  the relative index of two glued carriers is the relative index of the two subgroups.
* `TauCeti.IntegralLattice.IntermediateCarrier.IsIntegral.discriminant_mul_index_sq` and
  `TauCeti.IntegralLattice.IntermediateCarrier.IsIntegral.discriminant_mul_natCard_sq`:
  `disc(M) · [M : L]² = disc(L)` for an integral carrier `M`, and its form
  `disc(L_H) · |H|² = disc(L)` when the carrier glued along `H` is integral.
* `IntermediateCarrier.IsIntegral.isUnimodular_iff_natCard_sq_eq_discriminant`:
  the integral overlattice glued along `H` is unimodular exactly when `|H|² = disc(L)`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 4.
-/

public section

namespace TauCeti

universe u

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

namespace IntermediateCarrier

variable {L : IntegralLattice V}

/-! ## The index of an intermediate carrier -/

/-- The relative index of two intermediate carriers `M N`: the index of `M ⊓ N` in `N`, that is
the order of the quotient group `N / (M ⊓ N)`. When `M ≤ N` this is the index `[N : M]`, the
order of `N / M`. -/
noncomputable def relIndex (M N : L.IntermediateCarrier) : ℕ :=
  M.1.toAddSubgroup.relIndex N.1.toAddSubgroup

/-- The index `[M : L]` of the lattice in an intermediate carrier, that is the order of the
quotient group `M / L`. -/
noncomputable def index (M : L.IntermediateCarrier) : ℕ :=
  relIndex ⊥ M

/-- The relative index of intermediate carriers is their relative index as additive subgroups. -/
theorem relIndex_def (M N : L.IntermediateCarrier) :
    relIndex M N = M.1.toAddSubgroup.relIndex N.1.toAddSubgroup := (rfl)

/-- The index of an intermediate carrier is its carrier's relative index over the original
lattice. -/
theorem index_def (M : L.IntermediateCarrier) :
    index M = L.carrier.toAddSubgroup.relIndex M.1.toAddSubgroup := (rfl)

/-- Relative index from the lattice itself is the index of an intermediate carrier. -/
@[simp]
theorem relIndex_bot_left (M : L.IntermediateCarrier) : relIndex ⊥ M = index M := (rfl)

/-- The relative index of two intermediate carriers `M N` is the order of the quotient
`N / (M ⊓ N)`; when `M ≤ N` this is the order of `N / M`. -/
theorem relIndex_eq_natCard_quotient (M N : L.IntermediateCarrier) :
    relIndex M N = Nat.card (↥N.1 ⧸ M.1.submoduleOf N.1) := by
  rw [relIndex_def, AddSubgroup.relIndex, AddSubgroup.index_eq_card]
  exact Nat.card_congr (AddSubgroup.quotientEquivOfEq
    (Submodule.toAddSubgroup_submoduleOf M.1 N.1).symm)

/-- The index of an intermediate carrier is the order of the quotient module `M / L`. -/
theorem index_eq_natCard_quotient (M : L.IntermediateCarrier) :
    index M = Nat.card (↥M.1 ⧸ L.carrier.submoduleOf M.1) := by
  simpa using relIndex_eq_natCard_quotient (⊥ : L.IntermediateCarrier) M

/-- The relative index of an intermediate carrier in itself is one. -/
@[simp]
theorem relIndex_self (M : L.IntermediateCarrier) : relIndex M M = 1 := by
  rw [relIndex_def, AddSubgroup.relIndex_self]

/-- **The index is multiplicative in towers of intermediate carriers.** -/
theorem relIndex_mul_relIndex {M N P : L.IntermediateCarrier} (hMN : M ≤ N) (hNP : N ≤ P) :
    relIndex M N * relIndex N P = relIndex M P := by
  rw [relIndex_def, relIndex_def, relIndex_def]
  exact AddSubgroup.relIndex_mul_relIndex _ _ _
    ((Submodule.toAddSubgroup_le _ _).mpr (Subtype.coe_le_coe.mpr hMN))
    ((Submodule.toAddSubgroup_le _ _).mpr (Subtype.coe_le_coe.mpr hNP))

/-- The index of the smaller member of a chain times the relative index is the larger index. -/
theorem index_mul_relIndex {M N : L.IntermediateCarrier} (h : M ≤ N) :
    index M * relIndex M N = index N :=
  relIndex_mul_relIndex bot_le h

/-- The lattice itself has index one. -/
@[simp]
theorem index_bot : index (⊥ : L.IntermediateCarrier) = 1 := by
  calc
    index (⊥ : L.IntermediateCarrier) = relIndex ⊥ ⊥ := (relIndex_bot_left ⊥).symm
    _ = 1 := relIndex_self ⊥

/-- The carrier glued along `H`, pulled back to the dual carrier, is the inverse image of `H`
under the quotient map. -/
private theorem comap_subtype_intermediateCarrierOfDiscriminantSubgroup
    (H : AddSubgroup L.DiscriminantGroup) :
    (L.intermediateCarrierOfDiscriminantSubgroup H).1.toAddSubgroup.comap
        L.dualCarrier.subtype.toAddMonoidHom = H.comap L.carrierInDual.mkQ.toAddMonoidHom := by
  ext x
  simp [L.coe_mem_intermediateCarrierOfDiscriminantSubgroup_iff H x]

/-- The dual carrier is the range of its own inclusion, read as a subgroup of the ambient
space. -/
private theorem range_dualCarrier_subtype :
    L.dualCarrier.subtype.toAddMonoidHom.range = L.dualCarrier.toAddSubgroup := by
  ext x
  simp

/-- **The relative index of two glued intermediate carriers is the relative index of the two
subgroups of the discriminant group.** Both sides are read off the same quotient of the dual
carrier, so no finiteness and no containment of `H` in `K` is needed. -/
@[simp]
theorem relIndex_intermediateCarrierOfDiscriminantSubgroup
    (H K : AddSubgroup L.DiscriminantGroup) :
    relIndex (L.intermediateCarrierOfDiscriminantSubgroup H)
      (L.intermediateCarrierOfDiscriminantSubgroup K) = H.relIndex K := by
  have hmap : ((L.intermediateCarrierOfDiscriminantSubgroup K).1.toAddSubgroup.comap
      L.dualCarrier.subtype.toAddMonoidHom).map L.dualCarrier.subtype.toAddMonoidHom =
      (L.intermediateCarrierOfDiscriminantSubgroup K).1.toAddSubgroup :=
    AddSubgroup.map_comap_eq_self (by
      rw [range_dualCarrier_subtype]
      exact (Submodule.toAddSubgroup_le _ _).mpr
        (L.intermediateCarrierOfDiscriminantSubgroup K).2.2)
  rw [relIndex_def, ← hmap, ← AddSubgroup.relIndex_comap,
    comap_subtype_intermediateCarrierOfDiscriminantSubgroup,
    comap_subtype_intermediateCarrierOfDiscriminantSubgroup, AddSubgroup.relIndex_comap,
    AddSubgroup.map_comap_eq_self_of_surjective L.carrierInDual.mkQ_surjective]

/-- The relative index of two intermediate carriers is the relative index of their corresponding
subgroups of the discriminant group. -/
theorem relIndex_eq_relIndex_discriminantSubgroup (M N : L.IntermediateCarrier) :
    relIndex M N = (L.discriminantSubgroup M).relIndex (L.discriminantSubgroup N) := by
  calc
    relIndex M N =
        relIndex
          (L.intermediateCarrierOfDiscriminantSubgroup (L.discriminantSubgroup M))
          (L.intermediateCarrierOfDiscriminantSubgroup (L.discriminantSubgroup N)) := by
            rw [L.intermediateCarrierOfDiscriminantSubgroup_discriminantSubgroup,
              L.intermediateCarrierOfDiscriminantSubgroup_discriminantSubgroup]
    _ = (L.discriminantSubgroup M).relIndex (L.discriminantSubgroup N) :=
      relIndex_intermediateCarrierOfDiscriminantSubgroup _ _

/-- **The index of an intermediate carrier is the order of the subgroup it cuts out in the
discriminant group.** -/
theorem index_eq_natCard_discriminantSubgroup (M : L.IntermediateCarrier) :
    index M = Nat.card (L.discriminantSubgroup M) := by
  calc
    index M = relIndex ⊥ M := (relIndex_bot_left M).symm
    _ = (L.discriminantSubgroup ⊥).relIndex (L.discriminantSubgroup M) :=
      relIndex_eq_relIndex_discriminantSubgroup ⊥ M
    _ = Nat.card (L.discriminantSubgroup M) := by
      rw [L.discriminantSubgroup_bot, AddSubgroup.relIndex_bot_left]

/-- **The index of the overlattice attached to a subgroup of the discriminant group is the order
of that subgroup.** -/
@[simp]
theorem index_intermediateCarrierOfDiscriminantSubgroup (H : AddSubgroup L.DiscriminantGroup) :
    index (L.intermediateCarrierOfDiscriminantSubgroup H) = Nat.card H := by
  rw [index_eq_natCard_discriminantSubgroup,
    L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup]

/-- An intermediate carrier has index one exactly when it is the lattice itself. -/
@[simp]
theorem index_eq_one_iff (M : L.IntermediateCarrier) : index M = 1 ↔ M = ⊥ := by
  rw [index_eq_natCard_discriminantSubgroup, AddSubgroup.card_eq_one,
    ← L.discriminantSubgroup_bot, ← L.intermediateCarrierOrderIsoDiscriminantSubgroup_apply,
    ← L.intermediateCarrierOrderIsoDiscriminantSubgroup_apply]
  exact L.intermediateCarrierOrderIsoDiscriminantSubgroup.injective.eq_iff

section IsNondegenerate

variable [L.IsNondegenerate]

/-- The index of the dual carrier is the discriminant of the lattice. -/
@[simp]
theorem index_top : index (⊤ : L.IntermediateCarrier) = L.discriminant := by
  rw [index_eq_natCard_discriminantSubgroup, L.discriminantSubgroup_top, AddSubgroup.card_top,
    L.natCard_discriminantGroup]

end IsNondegenerate

/-- The index of a full intermediate carrier is positive. -/
theorem index_pos (M : L.IntermediateCarrier) [M.1.IsLattice ℚ] : 0 < index M := by
  rw [index_eq_natCard_quotient]
  let _ : Finite (↑M.1 ⧸ L.carrier.submoduleOf M.1) :=
    Submodule.finiteQuotientOfFreeOfRankEq _ <| by
      rw [(Submodule.submoduleOfEquivOfLe M.2.1).finrank_eq,
        Submodule.IsLattice.finrank_eq_finrank L.carrier,
        Submodule.IsLattice.finrank_eq_finrank M.1]
  exact Nat.card_pos

section IsLattice

variable {M : L.IntermediateCarrier} [M.1.IsLattice ℚ]

private theorem carrier_relIndex_toIntegralLattice_eq_index (hM : IsIntegral M) :
    L.carrier.toAddSubgroup.relIndex hM.toIntegralLattice.carrier.toAddSubgroup = index M := by
  rw [index_def, hM.toIntegralLattice_carrier]

/-- **The signed determinant of an integral overlattice scales by the square of the index.** -/
theorem IsIntegral.determinant_mul_index_sq (hM : IsIntegral M) :
    hM.toIntegralLattice.determinant * (index M : ℤ) ^ 2 = L.determinant := by
  rw [← carrier_relIndex_toIntegralLattice_eq_index hM]
  exact (L.determinant_eq_mul_relIndex_sq hM.toIntegralLattice
    (by rw [hM.toIntegralLattice_form])
    (by rw [hM.toIntegralLattice_carrier]; exact M.2.1)).symm

/-- **The discriminant of an integral overlattice scales by the square of the index:**
`disc(M) · [M : L]² = disc(L)`. -/
theorem IsIntegral.discriminant_mul_index_sq (hM : IsIntegral M) :
    hM.toIntegralLattice.discriminant * index M ^ 2 = L.discriminant := by
  rw [← carrier_relIndex_toIntegralLattice_eq_index hM]
  exact (L.discriminant_eq_mul_relIndex_sq hM.toIntegralLattice
    (by rw [hM.toIntegralLattice_form])
    (by rw [hM.toIntegralLattice_carrier]; exact M.2.1)).symm

/-- The square of the index of an integral overlattice divides the discriminant. -/
theorem IsIntegral.index_sq_dvd_discriminant (hM : IsIntegral M) :
    index M ^ 2 ∣ L.discriminant :=
  Dvd.intro_left _ hM.discriminant_mul_index_sq

/-- The discriminant of an integral overlattice is the exact quotient `disc(L) / [M : L]²`. -/
theorem IsIntegral.discriminant_eq_discriminant_div_index_sq (hM : IsIntegral M) :
    hM.toIntegralLattice.discriminant = L.discriminant / index M ^ 2 := by
  rw [← hM.discriminant_mul_index_sq, Nat.mul_div_cancel _ (pow_pos (index_pos M) 2)]

/-- **An integral overlattice is unimodular exactly when the square of its index exhausts the
discriminant of the lattice.** -/
theorem IsIntegral.isUnimodular_iff_index_sq_eq_discriminant (hM : IsIntegral M) :
    hM.toIntegralLattice.IsUnimodular ↔ index M ^ 2 = L.discriminant := by
  constructor
  · intro h
    have hdual : hM.toIntegralLattice.dualCarrier.IsLattice ℚ := by
      rw [← hM.toIntegralLattice.isUnimodular_def.mp h]
      infer_instance
    let _ : L.IsNondegenerate := ⟨by
      rw [← hM.toIntegralLattice_form]
      exact (hM.toIntegralLattice.isLattice_dualCarrier_iff_nondegenerate).mp hdual⟩
    rw [hM.toIntegralLattice.isUnimodular_iff_discriminant_eq_one] at h
    rw [← hM.discriminant_mul_index_sq, h, one_mul]
  · intro h
    have hdisc : 0 < L.discriminant := h ▸ pow_pos (index_pos M) 2
    let _ : L.IsNondegenerate := ⟨L.discriminant_pos_iff.mp hdisc⟩
    rw [hM.toIntegralLattice.isUnimodular_iff_discriminant_eq_one]
    apply Nat.eq_of_mul_eq_mul_right (pow_pos (index_pos M) 2)
    rw [hM.discriminant_mul_index_sq, one_mul, h]

/-- **The discriminant of the integral overlattice glued along a subgroup of the discriminant
group:** `disc(L_H) · |H|² = disc(L)`. -/
theorem IsIntegral.discriminant_mul_natCard_sq {H : AddSubgroup L.DiscriminantGroup}
    [(L.intermediateCarrierOfDiscriminantSubgroup H).1.IsLattice ℚ]
    (hH : IsIntegral (L.intermediateCarrierOfDiscriminantSubgroup H)) :
    hH.toIntegralLattice.discriminant * Nat.card H ^ 2 = L.discriminant := by
  rw [← index_intermediateCarrierOfDiscriminantSubgroup H]
  exact hH.discriminant_mul_index_sq

/-- **The overlattice glued along a subgroup of the discriminant group is unimodular exactly when
the square of the order of that subgroup is the discriminant.** -/
theorem IsIntegral.isUnimodular_iff_natCard_sq_eq_discriminant
    {H : AddSubgroup L.DiscriminantGroup}
    [(L.intermediateCarrierOfDiscriminantSubgroup H).1.IsLattice ℚ]
    (hH : IsIntegral (L.intermediateCarrierOfDiscriminantSubgroup H)) :
    hH.toIntegralLattice.IsUnimodular ↔ Nat.card H ^ 2 = L.discriminant := by
  rw [hH.isUnimodular_iff_index_sq_eq_discriminant,
    index_intermediateCarrierOfDiscriminantSubgroup H]

end IsLattice

end IntermediateCarrier

end IntegralLattice

end TauCeti
