/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Cardinality
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular

/-!
# The index and the discriminant of an overlattice

Let `L` be an integral lattice and let `L ≤ M ≤ Lᵛ` be an intermediate carrier. This file
computes the two numerical invariants of the gluing correspondence:

```text
[M : L] = #(M / L) = |M / L ≤ A_L|,      disc(M) · [M : L]² = disc(L).
```

The first equality is the index in the group-theoretic sense, and the second says that enlarging
a lattice by a subgroup of its discriminant group divides the discriminant by the square of the
order of that subgroup. Together with the correspondence of
`TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Isotropic` this is the numerical half of
Nikulin's gluing theory: an even lattice glued along a subgroup `H` of `A_L` has discriminant
`disc(L) / |H|²`, and is unimodular exactly when `|H|² = disc(L)`.

The determinant statement is proved once, and in the generality it deserves: whenever two
integral lattices share their ambient rational form and one carrier lies inside the other, their
signed determinants differ by the square of the index. Extending carrier bases of the two
lattices to bases of the ambient rational space, the index is the absolute determinant of the
change-of-basis matrix by `AddSubgroup.relIndex_eq_abs_det`, while the Gram determinants differ
by the square of that same determinant because a bilinear form's matrix transforms by
congruence.

An integral intermediate carrier is packaged as an integral lattice in its own right through
`IntermediateCarrier.IsIntegral.toIntegralLattice`, which keeps the ambient form and therefore
keeps nondegeneracy; evenness of the carrier makes it an even lattice.

## Main definitions

* `TauCeti.IntegralLattice.IntermediateCarrier.relIndex`: the relative index `[N : M]` of two
  intermediate carriers.
* `TauCeti.IntegralLattice.IntermediateCarrier.index`: the index `[M : L]`.
* `TauCeti.IntegralLattice.IntermediateCarrier.IsIntegral.toIntegralLattice`: an integral
  intermediate carrier, as an integral lattice for the same ambient form.

## Main results

* `TauCeti.IntegralLattice.determinant_eq_mul_relIndex_sq` and
  `TauCeti.IntegralLattice.discriminant_eq_mul_relIndex_sq`: the determinant and the discriminant
  of a full sublattice scale by the square of the index.
* `TauCeti.IntegralLattice.IntermediateCarrier.index_eq_natCard_discriminantSubgroup`: the index
  of an intermediate carrier is the order of the subgroup it cuts out in `A_L`.
* `TauCeti.IntegralLattice.IntermediateCarrier.index_intermediateCarrierOfDiscriminantSubgroup`:
  `[L_H : L] = |H|`.
* `TauCeti.IntegralLattice.IntermediateCarrier.relIndex_mul_relIndex` and
  `TauCeti.IntegralLattice.IntermediateCarrier.natCard_mul_relIndex`: multiplicativity of the
  index along a chain of intermediate carriers, and along the corresponding chain of subgroups.
* `TauCeti.IntegralLattice.IntermediateCarrier.IsIntegral.discriminant_mul_sq_index` and
  `TauCeti.IntegralLattice.IntermediateCarrier.IsIntegral.discriminant_mul_sq_natCard`:
  `disc(M) · [M : L]² = disc(L)`, and its form `disc(L_H) · |H|² = disc(L)`.
* `TauCeti.IntegralLattice.IntermediateCarrier.IsIntegral.isUnimodular_iff_sq_natCard`: the
  overlattice glued along `H` is unimodular exactly when `|H|² = disc(L)`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 4.
-/

public section

open Matrix Module

namespace TauCeti

universe u v

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-! ## The determinant of a full sublattice -/

/-- A carrier basis of an integral lattice generates the carrier as an additive subgroup of the
ambient rational vector space. -/
theorem carrier_toAddSubgroup_eq_closure_range (L : IntegralLattice V) {ι : Type v}
    (b : Basis ι ℤ L) :
    L.carrier.toAddSubgroup = AddSubgroup.closure (Set.range (b.extendOfIsLattice ℚ)) := by
  apply AddSubgroup.toIntSubmodule.injective
  rw [AddSubgroup.toIntSubmodule_closure, TauCeti.Basis.span_range_extendOfIsLattice,
    Submodule.toIntSubmodule_toAddSubgroup, Submodule.restrictScalars_self]

open Classical in
/-- **The signed determinant of a full sublattice scales by the square of the index.** If two
integral lattices share their ambient rational form and one carrier lies inside the other, the
smaller determinant is the larger one times the square of the index. -/
theorem determinant_eq_mul_relIndex_sq (L M : IntegralLattice V) (hform : L.form = M.form)
    (hle : L.carrier ≤ M.carrier) :
    L.determinant =
      M.determinant * (L.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup : ℤ) ^ 2 := by
  classical
  let bM : Basis (Module.Free.ChooseBasisIndex ℤ M) ℤ M := Module.Free.chooseBasis ℤ M
  let eM := bM.extendOfIsLattice ℚ
  let σ := (Module.Free.chooseBasis ℤ L).extendOfIsLattice ℚ |>.indexEquiv eM
  let bL : Basis (Module.Free.ChooseBasisIndex ℤ M) ℤ L :=
    (Module.Free.chooseBasis ℤ L).reindex σ
  let eL := bL.extendOfIsLattice ℚ
  have hidx : ((L.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup : ℕ) : ℚ)
      = |eM.det eL| :=
    AddSubgroup.relIndex_eq_abs_det _ _ hle eL eM
      (L.carrier_toAddSubgroup_eq_closure_range bL) (M.carrier_toAddSubgroup_eq_closure_range bM)
  have hmat : (eM.toMatrix eL)ᵀ * LinearMap.BilinForm.toMatrix eM L.form * eM.toMatrix eL
      = LinearMap.BilinForm.toMatrix eL L.form :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := eM) eL L.form
  have hdetL : (L.determinant : ℚ) = Matrix.det (LinearMap.BilinForm.toMatrix eL L.form) := by
    rw [L.determinant_eq_gramDet bL, L.intCast_gramDet bL]
  have hdetM : (M.determinant : ℚ) = Matrix.det (LinearMap.BilinForm.toMatrix eM L.form) := by
    rw [M.determinant_eq_gramDet bM, M.intCast_gramDet bM, hform]
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hdetL, ← hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← hdetM,
    ← Basis.det_apply, hidx]
  ring_nf
  rw [sq_abs]
  ring

/-- **The discriminant of a full sublattice scales by the square of the index.** -/
theorem discriminant_eq_mul_relIndex_sq (L M : IntegralLattice V) (hform : L.form = M.form)
    (hle : L.carrier ≤ M.carrier) :
    L.discriminant =
      M.discriminant * (L.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup) ^ 2 := by
  rw [discriminant_def, discriminant_def, L.determinant_eq_mul_relIndex_sq M hform hle,
    Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]

namespace IntermediateCarrier

variable {L : IntegralLattice V}

/-! ## The index of an intermediate carrier -/

/-- The relative index `[N : M]` of two intermediate carriers, that is the order of the
quotient group `N / M`. -/
@[expose]
noncomputable def relIndex (M N : L.IntermediateCarrier) : ℕ :=
  M.1.toAddSubgroup.relIndex N.1.toAddSubgroup

/-- The index `[M : L]` of the lattice in an intermediate carrier, that is the order of the
quotient group `M / L`. -/
@[expose]
noncomputable def index (M : L.IntermediateCarrier) : ℕ :=
  relIndex ⊥ M

/-- The relative index of two intermediate carriers is the order of the quotient module. -/
theorem relIndex_eq_natCard_quotient (M N : L.IntermediateCarrier) :
    relIndex M N = Nat.card (↥N.1 ⧸ M.1.submoduleOf N.1) := rfl

/-- The index of an intermediate carrier is the order of the quotient module `M / L`. -/
theorem index_eq_natCard_quotient (M : L.IntermediateCarrier) :
    index M = Nat.card (↥M.1 ⧸ L.carrier.submoduleOf M.1) := rfl

/-- The index is the relative index over the bottom intermediate carrier. -/
theorem index_eq_relIndex_bot (M : L.IntermediateCarrier) : index M = relIndex ⊥ M := rfl

/-- **The index is multiplicative in towers of intermediate carriers.** -/
theorem relIndex_mul_relIndex {M N P : L.IntermediateCarrier} (hMN : M ≤ N) (hNP : N ≤ P) :
    relIndex M N * relIndex N P = relIndex M P :=
  AddSubgroup.relIndex_mul_relIndex _ _ _ hMN hNP

/-- The index of the smaller member of a chain times the relative index is the larger index. -/
theorem index_mul_relIndex {M N : L.IntermediateCarrier} (h : M ≤ N) :
    index M * relIndex M N = index N :=
  relIndex_mul_relIndex bot_le h

/-- The lattice itself has index one. -/
@[simp]
theorem index_bot : index (⊥ : L.IntermediateCarrier) = 1 := by
  rw [index, relIndex, AddSubgroup.relIndex_self]

/-- The linear map sending a vector of an intermediate carrier to its discriminant class. -/
private noncomputable def toDiscriminantGroup (M : L.IntermediateCarrier) :
    ↥M.1 →ₗ[ℤ] L.DiscriminantGroup :=
  L.carrierInDual.mkQ ∘ₗ Submodule.inclusion M.2.2

private theorem toDiscriminantGroup_apply (M : L.IntermediateCarrier) (x : ↥M.1) :
    toDiscriminantGroup M x = Submodule.Quotient.mk ⟨(x : V), M.2.2 x.2⟩ := rfl

private theorem ker_toDiscriminantGroup (M : L.IntermediateCarrier) :
    LinearMap.ker (toDiscriminantGroup M) = L.carrier.submoduleOf M.1 := by
  ext x
  rw [LinearMap.mem_ker, toDiscriminantGroup_apply, L.discriminantGroup_mk_eq_zero_iff,
    Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]

private theorem coe_range_toDiscriminantGroup (M : L.IntermediateCarrier) :
    (LinearMap.range (toDiscriminantGroup M) : Set L.DiscriminantGroup) =
      (L.discriminantSubgroup M : Set L.DiscriminantGroup) := by
  ext z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
    rw [SetLike.mem_coe, SetLike.mem_coe, LinearMap.mem_range,
      L.mk_mem_discriminantSubgroup_iff]
    constructor
    · rintro ⟨y, hy⟩
      rw [toDiscriminantGroup_apply] at hy
      have hmem := (Submodule.Quotient.eq _).mp hy
      rw [L.mem_carrierInDual_iff] at hmem
      have hcoe : ((⟨(y : V), M.2.2 y.2⟩ - x : L.dualCarrier) : V) = (y : V) - (x : V) := rfl
      rw [hcoe] at hmem
      have hx : (x : V) = (y : V) - ((y : V) - (x : V)) := by abel
      rw [hx]
      exact sub_mem y.2 (M.2.1 hmem)
    · intro hx
      exact ⟨⟨(x : V), hx⟩, rfl⟩

/-- **The index of an intermediate carrier is the order of the subgroup it cuts out in the
discriminant group.** -/
theorem index_eq_natCard_discriminantSubgroup (M : L.IntermediateCarrier) :
    index M = Nat.card (L.discriminantSubgroup M) := by
  rw [index_eq_natCard_quotient, ← ker_toDiscriminantGroup M]
  exact Nat.card_congr ((toDiscriminantGroup M).quotKerEquivRange.toEquiv.trans
    (Equiv.setCongr (coe_range_toDiscriminantGroup M)))

/-- **The index of the overlattice attached to a subgroup of the discriminant group is the order
of that subgroup.** -/
@[simp]
theorem index_intermediateCarrierOfDiscriminantSubgroup (H : AddSubgroup L.DiscriminantGroup) :
    index (L.intermediateCarrierOfDiscriminantSubgroup H) = Nat.card H := by
  rw [index_eq_natCard_discriminantSubgroup,
    L.discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup]

/-- An intermediate carrier has index one exactly when it is the lattice itself. -/
theorem index_eq_one_iff (M : L.IntermediateCarrier) : index M = 1 ↔ M = ⊥ := by
  rw [index_eq_natCard_discriminantSubgroup, AddSubgroup.card_eq_one,
    ← L.discriminantSubgroup_bot, ← L.intermediateCarrierOrderIsoDiscriminantSubgroup_apply,
    ← L.intermediateCarrierOrderIsoDiscriminantSubgroup_apply]
  exact L.intermediateCarrierOrderIsoDiscriminantSubgroup.injective.eq_iff

/-- Multiplicativity of the index along a chain of subgroups of the discriminant group. -/
theorem natCard_mul_relIndex {H K : AddSubgroup L.DiscriminantGroup} (h : H ≤ K) :
    Nat.card H * relIndex (L.intermediateCarrierOfDiscriminantSubgroup H)
        (L.intermediateCarrierOfDiscriminantSubgroup K) = Nat.card K := by
  rw [← index_intermediateCarrierOfDiscriminantSubgroup H,
    ← index_intermediateCarrierOfDiscriminantSubgroup K]
  exact index_mul_relIndex ((L.intermediateCarrierOfDiscriminantSubgroup_le_iff H K).mpr h)

section IsNondegenerate

variable [L.IsNondegenerate]

/-- An integral intermediate carrier is itself an integral lattice, for the same ambient
rational form. -/
@[expose]
def IsIntegral.toIntegralLattice {M : L.IntermediateCarrier} (hM : IsIntegral M) :
    IntegralLattice V where
  carrier := M.1
  form := L.form
  isLattice := inferInstance
  isSymm := L.isSymm
  le_dual _ hx := L.form.mem_dualSubmodule.mpr fun _ hy ↦ isIntegral_def.mp hM _ hx _ hy

/-- The carrier of the integral lattice attached to an integral intermediate carrier. -/
@[simp]
theorem IsIntegral.carrier_toIntegralLattice {M : L.IntermediateCarrier} (hM : IsIntegral M) :
    hM.toIntegralLattice.carrier = M.1 := rfl

/-- The integral lattice attached to an integral intermediate carrier keeps the ambient form. -/
@[simp]
theorem IsIntegral.form_toIntegralLattice {M : L.IntermediateCarrier} (hM : IsIntegral M) :
    hM.toIntegralLattice.form = L.form := rfl

/-- An overlattice of a nondegenerate integral lattice is nondegenerate: it carries the same
ambient form. -/
instance IsIntegral.instIsNondegenerate {M : L.IntermediateCarrier} (hM : IsIntegral M) :
    hM.toIntegralLattice.IsNondegenerate :=
  ⟨L.form_nondegenerate⟩

/-- Regarding the lattice itself as an intermediate carrier returns the lattice. -/
@[simp]
theorem IsIntegral.toIntegralLattice_bot (hM : IsIntegral (⊥ : L.IntermediateCarrier)) :
    hM.toIntegralLattice = L :=
  IntegralLattice.ext rfl rfl

/-- An even intermediate carrier is an even integral lattice. -/
theorem IsEven.isEven_toIntegralLattice {M : L.IntermediateCarrier} (hM : IsEven M) :
    hM.isIntegral.toIntegralLattice.IsEven := by
  rw [isEven_iff_forall_norm]
  intro x
  obtain ⟨n, hn⟩ := isEven_def.mp hM (x : V) x.2
  exact ⟨n, by rw [norm_apply, IsIntegral.form_toIntegralLattice, ← norm_apply]; exact hn⟩

/-- The index of the dual carrier is the discriminant of the lattice. -/
@[simp]
theorem index_top : index (⊤ : L.IntermediateCarrier) = L.discriminant := by
  rw [index_eq_natCard_discriminantSubgroup, L.discriminantSubgroup_top, AddSubgroup.card_top,
    L.natCard_discriminantGroup]

/-- The index of an intermediate carrier of a nondegenerate lattice is positive. -/
theorem index_pos (M : L.IntermediateCarrier) : 0 < index M := by
  rw [index_eq_natCard_discriminantSubgroup]
  exact Nat.card_pos

/-- **The signed determinant of an integral overlattice scales by the square of the index.** -/
theorem IsIntegral.determinant_mul_sq_index {M : L.IntermediateCarrier} (hM : IsIntegral M) :
    hM.toIntegralLattice.determinant * (index M : ℤ) ^ 2 = L.determinant :=
  (L.determinant_eq_mul_relIndex_sq hM.toIntegralLattice rfl M.2.1).symm

/-- **The discriminant of an integral overlattice scales by the square of the index:**
`disc(M) · [M : L]² = disc(L)`. -/
theorem IsIntegral.discriminant_mul_sq_index {M : L.IntermediateCarrier} (hM : IsIntegral M) :
    hM.toIntegralLattice.discriminant * index M ^ 2 = L.discriminant :=
  (L.discriminant_eq_mul_relIndex_sq hM.toIntegralLattice rfl M.2.1).symm

/-- The square of the index of an integral overlattice divides the discriminant. -/
theorem IsIntegral.sq_index_dvd_discriminant {M : L.IntermediateCarrier} (hM : IsIntegral M) :
    index M ^ 2 ∣ L.discriminant :=
  Dvd.intro_left _ hM.discriminant_mul_sq_index

/-- The discriminant of an integral overlattice is the exact quotient `disc(L) / [M : L]²`. -/
theorem IsIntegral.discriminant_eq_div {M : L.IntermediateCarrier} (hM : IsIntegral M) :
    hM.toIntegralLattice.discriminant = L.discriminant / index M ^ 2 := by
  rw [← hM.discriminant_mul_sq_index, Nat.mul_div_cancel _ (pow_pos (index_pos M) 2)]

/-- **An integral overlattice is unimodular exactly when the square of its index exhausts the
discriminant of the lattice.** -/
theorem IsIntegral.isUnimodular_iff {M : L.IntermediateCarrier} (hM : IsIntegral M) :
    hM.toIntegralLattice.IsUnimodular ↔ index M ^ 2 = L.discriminant := by
  rw [isUnimodular_iff_discriminant_eq_one, ← hM.discriminant_mul_sq_index]
  refine ⟨fun h ↦ by rw [h, one_mul], fun h ↦ ?_⟩
  exact (Nat.eq_of_mul_eq_mul_right (pow_pos (index_pos M) 2) (by rw [one_mul]; exact h)).symm

/-- **The discriminant of the integral overlattice glued along a subgroup of the discriminant
group:** `disc(L_H) · |H|² = disc(L)`. -/
theorem IsIntegral.discriminant_mul_sq_natCard {H : AddSubgroup L.DiscriminantGroup}
    (hH : IsIntegral (L.intermediateCarrierOfDiscriminantSubgroup H)) :
    hH.toIntegralLattice.discriminant * Nat.card H ^ 2 = L.discriminant := by
  rw [← index_intermediateCarrierOfDiscriminantSubgroup H]
  exact hH.discriminant_mul_sq_index

/-- **The overlattice glued along a subgroup of the discriminant group is unimodular exactly when
the square of the order of that subgroup is the discriminant.** -/
theorem IsIntegral.isUnimodular_iff_sq_natCard {H : AddSubgroup L.DiscriminantGroup}
    (hH : IsIntegral (L.intermediateCarrierOfDiscriminantSubgroup H)) :
    hH.toIntegralLattice.IsUnimodular ↔ Nat.card H ^ 2 = L.discriminant := by
  rw [hH.isUnimodular_iff, index_intermediateCarrierOfDiscriminantSubgroup H]

end IsNondegenerate

end IntermediateCarrier

end IntegralLattice

end TauCeti
