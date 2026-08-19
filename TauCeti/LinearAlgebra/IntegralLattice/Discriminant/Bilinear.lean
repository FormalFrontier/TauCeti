/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Group

/-!
# Discriminant bilinear modules of integral lattices

For a nondegenerate integral lattice `L`, this file equips its finite discriminant group
`Lᵛ / L` with the pairing

```text
b_L (x + L) (y + L) = L.form x y mod ℤ.
```

Membership in `Lᵛ` makes the form change by an integer when either argument is translated by a
vector of `L`; integrality embeds `L` in `Lᵛ` so that the quotient can be formed. Double duality
for the embedded carrier proves that the resulting finite bilinear module is nondegenerate: a dual
vector pairing integrally with every dual vector already lies in `L`. Integral-lattice isometries
induce isometries of these discriminant bilinear modules.

The pairing `b_L` is `B(x, y) mod ℤ`; the even-lattice refinement
`q_L(x) = B(x, x) / 2 mod ℤ` (the half-norm convention) will have this pairing as its polar form.

## Main declarations

* `TauCeti.IntegralLattice.discriminantPairing`: the descended `ℚ/ℤ`-valued pairing.
* `TauCeti.IntegralLattice.discriminantBilinearModule`: the packaged finite bilinear module.
* `TauCeti.IntegralLattice.isNondegenerate_discriminantBilinearModule`: nondegeneracy of the
  discriminant pairing.
* `TauCeti.IntegralLattice.Isometry.discriminantBilinearIsometry`: functoriality under lattice
  isometry.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layers 2 and 3.
-/

public section

namespace TauCeti

universe u v w

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- The ambient form on two dual-carrier vectors, reduced modulo `ℤ`.

This is the pairing before quotienting either input by the original carrier. -/
private def dualCarrierFormModOne (L : IntegralLattice V) :
    L.dualCarrier →ₗ[ℤ] L.dualCarrier →ₗ[ℤ] AddCircle (1 : ℚ) :=
  LinearMap.mk₂' ℤ ℤ (fun x y ↦ (L.form x y : AddCircle (1 : ℚ)))
    (fun x y z ↦ by simp)
    (fun r x y ↦ by simp)
    (fun x y z ↦ by simp)
    (fun r x y ↦ by simp)

private theorem dualCarrierFormModOne_apply (L : IntegralLattice V) (x y : L.dualCarrier) :
    L.dualCarrierFormModOne x y = (L.form x y : AddCircle (1 : ℚ)) :=
  (rfl)

/-- A rational number reduces to zero in `ℚ/ℤ` exactly when it is an integer. -/
theorem coe_eq_zero_iff_mem_one (q : ℚ) :
    (q : AddCircle (1 : ℚ)) = 0 ↔ q ∈ (1 : Submodule ℤ ℚ) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).mp h
    exact Submodule.mem_one.mpr ⟨n, by simpa using hn⟩
  · intro h
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp h
    exact (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr ⟨n, by simpa using hn⟩

/-- The pairing modulo `ℤ` is symmetric, hence reflexive in the sense needed to descend a
bilinear map through the same quotient in both variables. -/
private theorem dualCarrierFormModOne_isRefl (L : IntegralLattice V) :
    L.dualCarrierFormModOne.IsRefl := by
  intro x y hxy
  rw [dualCarrierFormModOne_apply] at hxy ⊢
  rw [L.isSymm.eq]
  exact hxy

/-- Every original-lattice vector lies in the kernel of the pairing modulo `ℤ`. -/
private theorem carrierInDual_le_ker_dualCarrierFormModOne (L : IntegralLattice V) :
    L.carrierInDual ≤ L.dualCarrierFormModOne.ker := by
  intro x hx
  rw [LinearMap.mem_ker]
  ext y
  rw [LinearMap.zero_apply, dualCarrierFormModOne_apply]
  apply (coe_eq_zero_iff_mem_one _).mpr
  have hyx : L.form y x ∈ (1 : Submodule ℤ ℚ) :=
    y.2 x ((L.mem_carrierInDual_iff x).mp hx)
  rw [L.isSymm.eq]
  exact hyx

/-- The discriminant pairing `b_L : A_L × A_L → ℚ/ℤ` of an integral lattice. -/
noncomputable def discriminantPairing (L : IntegralLattice V) :
    L.DiscriminantGroup →ₗ[ℤ] L.DiscriminantGroup →ₗ[ℤ] AddCircle (1 : ℚ) :=
  LinearMap.IsRefl.liftQ₂ L.dualCarrierFormModOne L.carrierInDual
    L.dualCarrierFormModOne_isRefl L.carrierInDual_le_ker_dualCarrierFormModOne

/-- On representatives, the discriminant pairing is the ambient rational form modulo `ℤ`. -/
@[simp]
theorem discriminantPairing_mk (L : IntegralLattice V) (x y : L.dualCarrier) :
    L.discriminantPairing (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      (L.form x y : AddCircle (1 : ℚ)) :=
  (rfl)

/-- The discriminant pairing is symmetric. -/
theorem discriminantPairing_comm (L : IntegralLattice V) (x y : L.DiscriminantGroup) :
    L.discriminantPairing x y = L.discriminantPairing y x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y => simp only [discriminantPairing_mk, L.isSymm.eq]

/-- The finite discriminant group equipped with its canonical symmetric bilinear pairing.

The package is exposed so its dependent carrier and group-instance projections reduce to those of
`DiscriminantGroup`; its pairing should be used through the characteristic theorem below. -/
@[expose] noncomputable def discriminantBilinearModule (L : IntegralLattice V)
    [L.IsNondegenerate] :
    FiniteBilinearModule where
  carrier := L.DiscriminantGroup
  pairing := LinearMap.toAddMonoidHom'.comp L.discriminantPairing.toAddMonoidHom
  pairing_comm := L.discriminantPairing_comm

/-- The pairing of the discriminant bilinear module is the descended discriminant pairing. -/
@[simp]
theorem discriminantBilinearModule_pairing (L : IntegralLattice V) [L.IsNondegenerate]
    (x y : L.DiscriminantGroup) :
    L.discriminantBilinearModule.pairing x y = L.discriminantPairing x y :=
  (rfl)

private theorem injective_discriminantPairing (L : IntegralLattice V) [L.IsNondegenerate] :
    Function.Injective L.discriminantPairing := by
  intro a b hab
  induction a using Submodule.Quotient.induction_on with
  | _ x =>
    induction b using Submodule.Quotient.induction_on with
    | _ y =>
      apply (L.discriminantGroup_mk_eq_iff x y).mpr
      apply (L.forall_form_mem_one_dualCarrier_iff ((x - y : L.dualCarrier) : V)).mp
      intro z hz
      let z' : L.dualCarrier := ⟨z, hz⟩
      have hpair := DFunLike.congr_fun hab (Submodule.Quotient.mk z')
      have hzero : (L.form ((x - y : L.dualCarrier) : V) z : AddCircle (1 : ℚ)) = 0 := by
        rw [Submodule.coe_sub, map_sub, LinearMap.sub_apply, AddCircle.coe_sub, sub_eq_zero]
        exact hpair
      exact (coe_eq_zero_iff_mem_one _).mp hzero

/-- The discriminant bilinear module of a nondegenerate integral lattice is nondegenerate. -/
theorem isNondegenerate_discriminantBilinearModule (L : IntegralLattice V)
    [L.IsNondegenerate] : L.discriminantBilinearModule.IsNondegenerate := by
  rw [FiniteBilinearModule.isNondegenerate_iff_injective]
  intro a b hab
  apply L.injective_discriminantPairing
  apply LinearMap.ext
  intro z
  calc
    L.discriminantPairing a z = L.discriminantBilinearModule.pairing a z :=
      (L.discriminantBilinearModule_pairing a z).symm
    _ = L.discriminantBilinearModule.pairing b z := DFunLike.congr_fun hab z
    _ = L.discriminantPairing b z := L.discriminantBilinearModule_pairing b z

namespace Isometry

variable {W : Type v} {U : Type w}
variable [AddCommGroup W] [Module ℚ W]
variable [AddCommGroup U] [Module ℚ U]
variable {L : IntegralLattice V} {M : IntegralLattice W} {N : IntegralLattice U}

/-- An integral-lattice isometry preserves the discriminant pairing. -/
private theorem map_discriminantPairing (e : Isometry L M) (x y : L.DiscriminantGroup) :
    M.discriminantPairing (e.discriminantGroupEquiv x) (e.discriminantGroupEquiv y) =
      L.discriminantPairing x y := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      simp only [discriminantGroupEquiv_mk, discriminantPairing_mk,
        coe_dualCarrierEquiv_apply, e.map_app]

/-- An integral-lattice isometry induces an isometry of discriminant bilinear modules. -/
noncomputable def discriminantBilinearIsometry (e : Isometry L M)
    [L.IsNondegenerate] [M.IsNondegenerate] :
    FiniteBilinearModule.Isometry L.discriminantBilinearModule
      M.discriminantBilinearModule where
  toAddEquiv := e.discriminantGroupEquiv.toAddEquiv
  map_pairing' := e.map_discriminantPairing

/-- The underlying additive equivalence of the induced discriminant isometry is the one already
carried by `discriminantGroupEquiv`. -/
@[simp]
theorem discriminantBilinearIsometry_toAddEquiv (e : Isometry L M)
    [L.IsNondegenerate] [M.IsNondegenerate] :
    e.discriminantBilinearIsometry.toAddEquiv = e.discriminantGroupEquiv.toAddEquiv :=
  (rfl)

/-- The induced discriminant isometry acts through the discriminant-group equivalence. -/
@[simp]
theorem discriminantBilinearIsometry_apply (e : Isometry L M)
    [L.IsNondegenerate] [M.IsNondegenerate] (x : L.DiscriminantGroup) :
    e.discriminantBilinearIsometry x = e.discriminantGroupEquiv x :=
  (rfl)

/-- The induced discriminant isometry maps a representative through the dual-carrier
equivalence. -/
theorem discriminantBilinearIsometry_mk (e : Isometry L M)
    [L.IsNondegenerate] [M.IsNondegenerate] (x : L.dualCarrier) :
    e.discriminantBilinearIsometry (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e.dualCarrierEquiv x) := by
  rw [discriminantBilinearIsometry_apply, discriminantGroupEquiv_mk]

/-- The identity lattice isometry induces the identity discriminant-bilinear isometry. -/
@[simp]
theorem discriminantBilinearIsometry_refl (L : IntegralLattice V) [L.IsNondegenerate] :
    (Isometry.refl L).discriminantBilinearIsometry =
      FiniteBilinearModule.Isometry.refl L.discriminantBilinearModule := by
  apply FiniteBilinearModule.Isometry.toAddEquiv_injective
  rw [discriminantBilinearIsometry_toAddEquiv,
    FiniteBilinearModule.Isometry.refl_toAddEquiv, discriminantGroupEquiv_refl]
  rfl

/-- Passing to the inverse lattice isometry passes to the inverse discriminant-bilinear
isometry. -/
@[simp]
theorem discriminantBilinearIsometry_symm (e : Isometry L M)
    [L.IsNondegenerate] [M.IsNondegenerate] :
    e.symm.discriminantBilinearIsometry = e.discriminantBilinearIsometry.symm := by
  apply FiniteBilinearModule.Isometry.toAddEquiv_injective
  rw [discriminantBilinearIsometry_toAddEquiv,
    FiniteBilinearModule.Isometry.symm_toAddEquiv, discriminantGroupEquiv_symm]
  exact LinearEquiv.coe_toAddEquiv_symm

/-- The inverse induced discriminant isometry maps a representative through the inverse
dual-carrier equivalence. -/
@[simp]
theorem discriminantBilinearIsometry_symm_mk (e : Isometry L M)
    [L.IsNondegenerate] [M.IsNondegenerate] (y : M.dualCarrier) :
    e.discriminantBilinearIsometry.symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (e.symm.dualCarrierEquiv y) := by
  rw [← e.discriminantBilinearIsometry_symm, discriminantBilinearIsometry_mk]

/-- The discriminant-bilinear isometry induced by a composite is the composite of the induced
isometries. -/
@[simp]
theorem discriminantBilinearIsometry_trans (e : Isometry L M) (f : Isometry M N)
    [L.IsNondegenerate] [M.IsNondegenerate] [N.IsNondegenerate] :
    (e.trans f).discriminantBilinearIsometry =
      e.discriminantBilinearIsometry.trans f.discriminantBilinearIsometry := by
  apply FiniteBilinearModule.Isometry.toAddEquiv_injective
  rw [discriminantBilinearIsometry_toAddEquiv,
    FiniteBilinearModule.Isometry.trans_toAddEquiv, discriminantBilinearIsometry_toAddEquiv,
    discriminantBilinearIsometry_toAddEquiv, discriminantGroupEquiv_trans]
  rfl

end Isometry

end IntegralLattice

end TauCeti
