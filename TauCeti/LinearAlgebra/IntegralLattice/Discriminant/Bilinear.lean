/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.LinearAlgebra.FiniteBilinearModule
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Group

/-!
# Discriminant bilinear modules of integral lattices

For a nondegenerate integral lattice `L`, this file equips its finite discriminant group
`Lᵛ / L` with the pairing

```text
b_L (x + L) (y + L) = L.form x y mod ℤ.
```

Integrality of the original lattice makes this independent of both representatives. Double
duality for the embedded carrier proves that the resulting finite bilinear module is
nondegenerate: a dual vector pairing integrally with every dual vector already lies in `L`.
Integral-lattice isometries induce isometries of these discriminant bilinear modules.

The pairing uses the half-norm roadmap convention only indirectly; its quadratic refinement for
an even lattice will have polar form equal to the bilinear pairing constructed here.

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
private def dualPairingModOne (L : IntegralLattice V) :
    L.dualCarrier →ₗ[ℤ] L.dualCarrier →ₗ[ℤ] AddCircle (1 : ℚ) :=
  LinearMap.mk₂' ℤ ℤ (fun x y ↦ (L.form x y : AddCircle (1 : ℚ)))
    (fun x y z ↦ by simp)
    (fun r x y ↦ by simp)
    (fun x y z ↦ by simp)
    (fun r x y ↦ by simp)

private theorem dualPairingModOne_apply (L : IntegralLattice V) (x y : L.dualCarrier) :
    L.dualPairingModOne x y = (L.form x y : AddCircle (1 : ℚ)) :=
  (rfl)

/-- The pairing modulo `ℤ` is symmetric, hence reflexive in the sense needed to descend a
bilinear map through the same quotient in both variables. -/
private theorem dualPairingModOne_isRefl (L : IntegralLattice V) :
    L.dualPairingModOne.IsRefl := by
  intro x y hxy
  rw [dualPairingModOne_apply, L.isSymm.eq]
  exact hxy

/-- Every original-lattice vector lies in the kernel of the pairing modulo `ℤ`. -/
private theorem carrierInDual_le_ker_dualPairingModOne (L : IntegralLattice V) :
    L.carrierInDual ≤ L.dualPairingModOne.ker := by
  intro x hx
  rw [LinearMap.mem_ker]
  ext y
  rw [LinearMap.zero_apply, dualPairingModOne_apply, AddCircle.coe_eq_zero_iff]
  have hyx : L.form y x ∈ (1 : Submodule ℤ ℚ) :=
    y.2 x ((L.mem_carrierInDual_iff x).mp hx)
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp hyx
  refine ⟨n, ?_⟩
  rw [L.isSymm.eq]
  simpa using hn

/-- The discriminant pairing `b_L : A_L × A_L → ℚ/ℤ` of an integral lattice. -/
noncomputable def discriminantPairing (L : IntegralLattice V) :
    L.DiscriminantGroup →ₗ[ℤ] L.DiscriminantGroup →ₗ[ℤ] AddCircle (1 : ℚ) :=
  LinearMap.IsRefl.liftQ₂ L.dualPairingModOne L.carrierInDual L.dualPairingModOne_isRefl
    L.carrierInDual_le_ker_dualPairingModOne

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

/-- The finite discriminant group equipped with its canonical symmetric bilinear pairing. -/
noncomputable abbrev discriminantBilinearModule (L : IntegralLattice V)
    [L.IsNondegenerate] :
    FiniteBilinearModule where
  carrier := L.DiscriminantGroup
  pairing :=
    { toFun := fun x ↦
        { toFun := fun y ↦ L.discriminantPairing x y
          map_zero' := map_zero (L.discriminantPairing x)
          map_add' := map_add (L.discriminantPairing x) }
      map_zero' := by
        ext y
        exact LinearMap.congr_fun (map_zero L.discriminantPairing) y
      map_add' := fun x y ↦ by
        ext z
        exact LinearMap.congr_fun (map_add L.discriminantPairing x y) z }
  pairing_comm := L.discriminantPairing_comm

/-- The pairing of the discriminant bilinear module is the descended discriminant pairing. -/
theorem discriminantBilinearModule_pairing (L : IntegralLattice V) [L.IsNondegenerate]
    (x y : L.DiscriminantGroup) :
    L.discriminantBilinearModule.pairing x y = L.discriminantPairing x y :=
  (rfl)

/-- On representatives, the packaged discriminant pairing is the ambient form modulo `ℤ`. -/
theorem discriminantBilinearModule_pairing_mk (L : IntegralLattice V) [L.IsNondegenerate]
    (x y : L.dualCarrier) :
    L.discriminantBilinearModule.pairing (Submodule.Quotient.mk x)
        (Submodule.Quotient.mk y) = (L.form x y : AddCircle (1 : ℚ)) :=
  (rfl)

/-- The discriminant bilinear module of a nondegenerate integral lattice is nondegenerate. -/
theorem isNondegenerate_discriminantBilinearModule (L : IntegralLattice V)
    [L.IsNondegenerate] : L.discriminantBilinearModule.IsNondegenerate := by
  rw [FiniteBilinearModule.isNondegenerate_iff_injective]
  intro a b hab
  induction a using Submodule.Quotient.induction_on with
  | _ x =>
    induction b using Submodule.Quotient.induction_on with
    | _ y =>
      rw [L.discriminantGroup_mk_eq_iff]
      apply (L.forall_form_mem_one_dualCarrier_iff ((x - y : L.dualCarrier) : V)).mp
      intro z hz
      let z' : L.dualCarrier := ⟨z, hz⟩
      have hpair := DFunLike.congr_fun hab (Submodule.Quotient.mk z')
      rw [discriminantBilinearModule_pairing_mk,
        discriminantBilinearModule_pairing_mk] at hpair
      have hzero : (L.form ((x - y : L.dualCarrier) : V) z : AddCircle (1 : ℚ)) = 0 := by
        rw [Submodule.coe_sub, map_sub, LinearMap.sub_apply, AddCircle.coe_sub, sub_eq_zero]
        exact hpair
      have hzmem : L.form ((x - y : L.dualCarrier) : V) z ∈
          AddSubgroup.zmultiples (1 : ℚ) :=
        (QuotientAddGroup.eq_zero_iff _).mp hzero
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hzmem
      apply Submodule.mem_one.mpr
      exact ⟨n, by simpa using hn⟩

namespace Isometry

variable {W : Type v} {U : Type w}
variable [AddCommGroup W] [Module ℚ W]
variable [AddCommGroup U] [Module ℚ U]
variable {L : IntegralLattice V} {M : IntegralLattice W} {N : IntegralLattice U}

/-- An integral-lattice isometry induces an isometry of discriminant bilinear modules. -/
noncomputable def discriminantBilinearIsometry (e : Isometry L M)
    [L.IsNondegenerate] [M.IsNondegenerate] :
    FiniteBilinearModule.Isometry L.discriminantBilinearModule
      M.discriminantBilinearModule where
  toAddEquiv := e.discriminantGroupEquiv.toAddEquiv
  map_pairing' x y := by
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        have hx : e.discriminantGroupEquiv.toAddEquiv (Submodule.Quotient.mk x) =
            Submodule.Quotient.mk (e.dualCarrierEquiv x) :=
          e.discriminantGroupEquiv_mk x
        have hy : e.discriminantGroupEquiv.toAddEquiv (Submodule.Quotient.mk y) =
            Submodule.Quotient.mk (e.dualCarrierEquiv y) :=
          e.discriminantGroupEquiv_mk y
        rw [hx, hy, discriminantBilinearModule_pairing_mk,
          discriminantBilinearModule_pairing_mk, coe_dualCarrierEquiv_apply,
          coe_dualCarrierEquiv_apply, e.map_app]

/-- The underlying additive equivalence of the induced discriminant isometry is the one already
carried by `discriminantGroupEquiv`. -/
@[simp]
theorem discriminantBilinearIsometry_toAddEquiv (e : Isometry L M)
    [L.IsNondegenerate] [M.IsNondegenerate] :
    e.discriminantBilinearIsometry.toAddEquiv = e.discriminantGroupEquiv.toAddEquiv :=
  (rfl)

/-- The induced discriminant isometry maps a representative through the dual-carrier
equivalence. -/
@[simp]
theorem discriminantBilinearIsometry_mk (e : Isometry L M)
    [L.IsNondegenerate] [M.IsNondegenerate] (x : L.dualCarrier) :
    e.discriminantBilinearIsometry (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e.dualCarrierEquiv x) := by
  exact e.discriminantGroupEquiv_mk x

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
  rfl

/-- The discriminant-bilinear isometry induced by a composite is the composite of the induced
isometries. -/
@[simp]
theorem discriminantBilinearIsometry_trans (e : Isometry L M) (f : Isometry M N)
    [L.IsNondegenerate] [M.IsNondegenerate] [N.IsNondegenerate] :
    (e.trans f).discriminantBilinearIsometry =
      e.discriminantBilinearIsometry.trans f.discriminantBilinearIsometry := by
  apply FiniteBilinearModule.Isometry.toAddEquiv_injective
  rw [discriminantBilinearIsometry_toAddEquiv,
    FiniteBilinearModule.Isometry.trans_toAddEquiv, discriminantGroupEquiv_trans]
  rfl

end Isometry

end IntegralLattice

end TauCeti
