/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import TauCeti.LinearAlgebra.IntegralLattice.DiscriminantGroup
public import TauCeti.LinearAlgebra.IntegralLattice.Gram
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry

/-!
# Unimodular integral lattices

An integral lattice is unimodular when its carrier is equal to its dual carrier.  For a
nondegenerate lattice this file identifies that condition with each of the standard criteria: the
discriminant group is trivial, its cardinality is one, the Gram determinant is a unit, the
discriminant is one, and the restricted integral pairing is a linear equivalence.

The cardinality of the discriminant group is also computed as the absolute value of the Gram
determinant.  The proof uses Mathlib's determinant/index formula for a full-rank submodule rather
than reproving Smith normal form.

## Main declarations

* `TauCeti.IntegralLattice.IsUnimodular`: equality of the carrier and dual carrier.
* `TauCeti.IntegralLattice.natCard_discriminantGroup`: the formula
  `#A_L = |det Gram(L)|`.
* `TauCeti.IntegralLattice.isUnimodular_iff_subsingleton_discriminantGroup`: the quotient
  criterion.
* `TauCeti.IntegralLattice.isUnimodular_iff_integralForm_bijective`: the perfect-pairing
  criterion.
* `TauCeti.IntegralLattice.isUnimodular_iff_discriminant_eq_one`: the determinant criterion.
* `TauCeti.IntegralLattice.integralPairingEquiv`: the restricted pairing as a linear equivalence.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layers 1 and 2.
-/

public section

open Module

namespace TauCeti

universe u v

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- An integral lattice is unimodular when it is equal to its dual lattice inside the common
rational ambient space. -/
def IsUnimodular (L : IntegralLattice V) : Prop :=
  L.carrier = L.dualCarrier

/-- Unimodularity unfolded as equality with the dual carrier. -/
@[simp]
theorem isUnimodular_def (L : IntegralLattice V) :
    L.IsUnimodular ↔ L.carrier = L.dualCarrier :=
  Iff.rfl

/-- Unimodularity is equivalent to every vector in the dual carrier already belonging to the
original carrier. -/
theorem isUnimodular_iff_dualCarrier_le (L : IntegralLattice V) :
    L.IsUnimodular ↔ L.dualCarrier ≤ L.carrier := by
  rw [L.isUnimodular_def]
  exact ⟨fun h ↦ h.symm.le, fun h ↦ le_antisymm L.le_dualCarrier h⟩

/-- Unimodularity is equivalent to the embedded carrier filling the dual carrier. -/
theorem isUnimodular_iff_carrierInDual_eq_top (L : IntegralLattice V) :
    L.IsUnimodular ↔ L.carrierInDual = ⊤ := by
  rw [L.isUnimodular_iff_dualCarrier_le, L.carrierInDual_eq_comap_subtype,
    Submodule.comap_subtype_eq_top]

/-- Unimodularity is equivalent to triviality of the discriminant group. -/
theorem isUnimodular_iff_subsingleton_discriminantGroup (L : IntegralLattice V) :
    L.IsUnimodular ↔ Subsingleton L.DiscriminantGroup := by
  exact L.isUnimodular_iff_carrierInDual_eq_top.trans
    Submodule.Quotient.subsingleton_iff.symm

/-- Unimodularity is equivalent to the discriminant group having one element. -/
theorem isUnimodular_iff_natCard_discriminantGroup_eq_one (L : IntegralLattice V) :
    L.IsUnimodular ↔ Nat.card L.DiscriminantGroup = 1 := by
  rw [L.isUnimodular_iff_subsingleton_discriminantGroup, Nat.card_eq_one_iff_unique]
  exact ⟨fun h ↦ ⟨h, ⟨0⟩⟩, fun h ↦ h.1⟩

namespace Isometry

variable {W : Type v} [AddCommGroup W] [Module ℚ W]
variable {L : IntegralLattice V} {M : IntegralLattice W}

/-- Unimodularity is preserved and reflected by an integral-lattice isometry. -/
theorem isUnimodular_iff (e : TauCeti.IntegralLattice.Isometry L M) :
    L.IsUnimodular ↔ M.IsUnimodular := by
  rw [L.isUnimodular_iff_subsingleton_discriminantGroup,
    M.isUnimodular_iff_subsingleton_discriminantGroup]
  exact e.discriminantGroupEquiv.toEquiv.subsingleton_congr

end Isometry

section Pairing

variable (L : IntegralLattice V) [L.IsNondegenerate]

omit [L.IsNondegenerate] in
private theorem isUnimodular_iff_surjective_inclusion :
    L.IsUnimodular ↔
      Function.Surjective (Submodule.inclusion L.le_dualCarrier) := by
  rw [← LinearMap.range_eq_top, Submodule.range_inclusion]
  rw [← L.carrierInDual_eq_comap_subtype]
  exact L.isUnimodular_iff_carrierInDual_eq_top

/-- The restricted integral form factors as carrier inclusion followed by the perfect dual
pairing. -/
theorem integralForm_eq_dualPairingEquiv_comp :
    L.integralForm = L.dualPairingEquiv.toLinearMap.comp
      (Submodule.inclusion L.le_dualCarrier) := by
  ext x y
  apply Int.cast_injective (α := ℚ)
  rw [L.integralForm_cast]
  symm
  rw [LinearMap.comp_apply]
  convert L.dualPairingEquiv_cast (Submodule.inclusion L.le_dualCarrier x) y using 1 <;> rfl

/-- A nondegenerate integral lattice is unimodular exactly when its restricted pairing with the
module dual is bijective. -/
theorem isUnimodular_iff_integralForm_bijective :
    L.IsUnimodular ↔ Function.Bijective L.integralForm := by
  rw [L.isUnimodular_iff_surjective_inclusion]
  constructor
  · intro h
    rw [L.integralForm_eq_dualPairingEquiv_comp]
    exact L.dualPairingEquiv.bijective.comp
      ⟨Submodule.inclusion_injective L.le_dualCarrier, h⟩
  · intro h x
    obtain ⟨y, hy⟩ := h.2 (L.dualPairingEquiv x)
    refine ⟨y, L.dualPairingEquiv.injective ?_⟩
    rw [← hy, L.integralForm_eq_dualPairingEquiv_comp]
    rfl

/-- For a unimodular lattice, the restricted integral pairing is a linear equivalence with the
module dual. -/
noncomputable def integralPairingEquiv (hL : L.IsUnimodular) :
    L ≃ₗ[ℤ] Module.Dual ℤ L :=
  LinearEquiv.ofBijective L.integralForm
    (L.isUnimodular_iff_integralForm_bijective.mp hL)

/-- The underlying linear map of `integralPairingEquiv` is the restricted integral form. -/
@[simp]
theorem integralPairingEquiv_toLinearMap (hL : L.IsUnimodular) :
    (L.integralPairingEquiv hL).toLinearMap = L.integralForm := by
  apply LinearMap.ext
  intro x
  exact LinearEquiv.ofBijective_apply L.integralForm x

end Pairing

section Cardinality

variable (L : IntegralLattice V)

/-- The basis of the embedded carrier obtained from a basis of the original carrier. -/
noncomputable def carrierInDualBasis {ι : Type v} (e : Basis ι ℤ L) :
    Basis ι ℤ L.carrierInDual :=
  e.map ((Submodule.submoduleOfEquivOfLe L.le_dualCarrier).symm.trans
    (LinearEquiv.ofEq _ _ (by
      ext x
      exact (L.mem_carrierInDual_iff x).symm)))

/-- Embedding `carrierInDualBasis` into the dual carrier recovers the original carrier basis. -/
@[simp]
theorem coe_carrierInDualBasis {ι : Type v} (e : Basis ι ℤ L) (i : ι) :
    (L.carrierInDualBasis e i : L.dualCarrier) =
      Submodule.inclusion L.le_dualCarrier (e i) := by
  rw [carrierInDualBasis, Basis.map_apply, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply]
  rfl

variable [L.IsNondegenerate]

/-- Coordinates of an original carrier vector in the dual-carrier basis are its pairings with the
original basis. -/
theorem dualCarrierBasis_repr_inclusion {ι : Type v} [Finite ι]
    (e : Basis ι ℤ L) (x : L) (i : ι) :
    (L.dualCarrierBasis e).repr (Submodule.inclusion L.le_dualCarrier x) i =
      L.integralForm x (e i) := by
  classical
  have hb : L.dualCarrierBasis e = e.dualBasis.map L.dualPairingEquiv.symm := by
    ext j
    rw [L.dualCarrierBasis_apply, Basis.map_apply]
    apply congrArg Subtype.val
    apply L.dualPairingEquiv.injective
    rw [L.dualPairingEquiv_dualBasisElem, LinearEquiv.apply_symm_apply]
  rw [hb, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Basis.dualBasis_repr, L.integralForm_eq_dualPairingEquiv_comp]
  rfl

/-- The determinant of the embedded carrier basis relative to the dual-carrier basis is the Gram
determinant. -/
theorem dualCarrierBasis_det_carrierInDualBasis {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    (L.dualCarrierBasis e).det (fun i ↦ (L.carrierInDualBasis e i : L.dualCarrier)) =
      L.gramDet e := by
  rw [Basis.det_apply, L.gramDet_def]
  congr 1
  ext i j
  rw [Basis.toMatrix_apply, L.coe_carrierInDualBasis,
    L.dualCarrierBasis_repr_inclusion, L.gramMatrix_apply]
  exact L.isSymm_integralForm.eq _ _

/-- **The order of the discriminant group is the absolute Gram determinant.** -/
theorem natCard_discriminantGroup {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    Nat.card L.DiscriminantGroup = (L.gramDet e).natAbs := by
  rw [← L.dualCarrierBasis_det_carrierInDualBasis e]
  exact (Submodule.natAbs_det_basis_change (L.dualCarrierBasis e) L.carrierInDual
    (L.carrierInDualBasis e)).symm

/-- The order of the discriminant group is the basis-independent lattice discriminant. -/
theorem natCard_discriminantGroup_eq_discriminant :
    Nat.card L.DiscriminantGroup = L.discriminant := by
  classical
  rw [L.natCard_discriminantGroup (Module.Free.chooseBasis ℤ L),
    L.discriminant_eq_natAbs_gramDet (Module.Free.chooseBasis ℤ L)]

end Cardinality

section DeterminantCriteria

variable (L : IntegralLattice V) [L.IsNondegenerate]

/-- A nondegenerate integral lattice is unimodular exactly when its basis-independent
discriminant is one. -/
theorem isUnimodular_iff_discriminant_eq_one :
    L.IsUnimodular ↔ L.discriminant = 1 := by
  rw [L.isUnimodular_iff_natCard_discriminantGroup_eq_one,
    L.natCard_discriminantGroup_eq_discriminant]

/-- A nondegenerate integral lattice is unimodular exactly when its signed determinant is a unit
of `ℤ`. -/
theorem isUnimodular_iff_isUnit_determinant :
    L.IsUnimodular ↔ IsUnit L.determinant := by
  rw [L.isUnimodular_iff_discriminant_eq_one, L.discriminant_def,
    ← Int.isUnit_iff_natAbs_eq]

/-- In every carrier basis, unimodularity is equivalent to the Gram determinant having absolute
value one. -/
theorem isUnimodular_iff_natAbs_gramDet_eq_one {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    L.IsUnimodular ↔ (L.gramDet e).natAbs = 1 := by
  rw [L.isUnimodular_iff_discriminant_eq_one,
    L.discriminant_eq_natAbs_gramDet e]

/-- In every carrier basis, unimodularity is equivalent to the signed Gram determinant being a
unit of `ℤ`; in particular, determinant `-1` is allowed. -/
theorem isUnimodular_iff_isUnit_gramDet {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    L.IsUnimodular ↔ IsUnit (L.gramDet e) := by
  rw [L.isUnimodular_iff_natAbs_gramDet_eq_one e, ← Int.isUnit_iff_natAbs_eq]

end DeterminantCriteria

end IntegralLattice

end TauCeti
