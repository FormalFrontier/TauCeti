/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import TauCeti.LinearAlgebra.IntegralLattice.Basic

/-!
# Isometries of integral lattices

An isometry of integral lattices is a rational linear isometry of their ambient bilinear spaces
which maps one integral carrier onto the other.  This is stronger than an additive or linear
equivalence of the carriers: the rational form-preservation equation is part of the data.

This file provides the identity, inverse, and composition isometries, restricts an isometry to an
integral linear equivalence of carriers, and extends every form-preserving carrier equivalence
uniquely to the rational ambient spaces.  It also transports an integral lattice along an ambient
linear equivalence and records the canonical isometry to the transported lattice.

The isometry API (coercions, `EquivLike`/`LinearEquivClass` instances, and identity, inverse, and
composition) follows Mathlib's `LinearMap.BilinForm.IsometryEquiv` API in
`Mathlib/LinearAlgebra/BilinearForm/IsometryEquiv.lean`.

## Main definitions

* `TauCeti.IntegralLattice.Isometry`: a form-preserving rational linear equivalence mapping one
  integral carrier onto another.
* `TauCeti.IntegralLattice.Isometry.ambientEquiv`: the ambient equivalence of an isometry, read
  over `ℤ`.
* `TauCeti.IntegralLattice.Isometry.carrierEquiv`: restriction of an isometry to the carriers.
* `TauCeti.IntegralLattice.Isometry.carrierBasisEquiv`: transport of carrier bases along an
  isometry.
* `TauCeti.IntegralLattice.Isometry.ofCarrierEquiv`: rational extension of a form-preserving
  integral linear equivalence of carriers.
* `TauCeti.IntegralLattice.transport`: transport of a lattice along a rational linear equivalence.
* `TauCeti.IntegralLattice.transportIsometry`: the canonical isometry to a transported lattice.

## Main results

* `TauCeti.IntegralLattice.Isometry.carrierEquiv_ofCarrierEquiv` and
  `TauCeti.IntegralLattice.Isometry.ofCarrierEquiv_carrierEquiv`: the two round trips between
  ambient isometries and form-preserving carrier equivalences.
* `TauCeti.IntegralLattice.Isometry.finrank_carrier_eq`: invariance of the carrier rank.
* `TauCeti.IntegralLattice.transport_refl`: transporting along the identity changes no lattice.

## References

* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 1
* W. Ebeling, *Lattices and Codes*, Chapter 1
-/

public section

open Module

namespace TauCeti

universe u v w

namespace IntegralLattice

variable {V : Type u} {W : Type v} {U : Type w}
variable [AddCommGroup V] [Module ℚ V]
variable [AddCommGroup W] [Module ℚ W]
variable [AddCommGroup U] [Module ℚ U]

/-- An isometry of integral lattices is an isometry of their ambient rational bilinear spaces
which maps the first carrier onto the second. -/
structure Isometry (L : IntegralLattice V) (M : IntegralLattice W)
    extends L.form.IsometryEquiv M.form where
  /-- The ambient equivalence maps the source lattice carrier onto the target carrier. -/
  map_carrier : L.carrier.map (toLinearEquiv.restrictScalars ℤ).toLinearMap = M.carrier

namespace Isometry

variable {L : IntegralLattice V} {M : IntegralLattice W} {N : IntegralLattice U}

/-- An integral-lattice isometry coerces to its ambient rational linear equivalence. -/
instance : CoeOut (Isometry L M) (V ≃ₗ[ℚ] W) := ⟨fun e ↦ e.toIsometryEquiv.toLinearEquiv⟩

/-- An integral-lattice isometry acts on the ambient rational vector spaces. -/
instance : EquivLike (Isometry L M) V W where
  coe e := e.toIsometryEquiv
  inv e := e.toIsometryEquiv.symm
  left_inv e := e.toIsometryEquiv.toLinearEquiv.left_inv
  right_inv e := e.toIsometryEquiv.toLinearEquiv.right_inv
  coe_injective' e f h := by
    cases e
    cases f
    simp_all

/-- Integral-lattice isometries are rational linear equivalences. -/
instance : LinearEquivClass (Isometry L M) ℚ V W where
  map_add e := map_add e.toIsometryEquiv
  map_smulₛₗ e := map_smulₛₗ e.toIsometryEquiv

/-- Coercion of an isometry to a linear equivalence acts the same as the isometry. -/
@[simp]
theorem coe_toLinearEquiv (e : Isometry L M) : ⇑(e : V ≃ₗ[ℚ] W) = e := rfl

/-- Coercion of the underlying bilinear-form isometry acts the same as the lattice isometry. -/
@[simp]
theorem coe_toIsometryEquiv (e : Isometry L M) : ⇑e.toIsometryEquiv = ⇑e := rfl

/-- An integral-lattice isometry preserves the ambient bilinear forms. -/
@[simp]
theorem map_app (e : Isometry L M) (x y : V) : M.form (e x) (e y) = L.form x y :=
  e.toIsometryEquiv.map_app y x

/-- The ambient rational equivalence of an integral-lattice isometry, read as an equivalence of
the underlying `ℤ`-modules. Carriers, dual carriers, and every submodule between them are
transported along this equivalence. -/
def ambientEquiv (e : Isometry L M) : V ≃ₗ[ℤ] W :=
  (e : V ≃ₗ[ℚ] W).restrictScalars ℤ

@[simp]
theorem ambientEquiv_apply (e : Isometry L M) (x : V) : e.ambientEquiv x = e x := (rfl)

/-- An ambient vector's image belongs to the target carrier if and only if the vector belongs
to the source carrier. -/
@[simp]
theorem apply_mem_carrier_iff (e : Isometry L M) (x : V) :
    e x ∈ M.carrier ↔ x ∈ L.carrier := by
  -- `map_carrier` is stated using the restricted ambient linear equivalence, while this goal is
  -- displayed through the `Isometry` coercion. Expose that equivalence definitionally so the
  -- standard membership theorem for mapped submodules can rewrite the goal.
  change e.ambientEquiv x ∈ M.carrier ↔ x ∈ L.carrier
  rw [← e.map_carrier, Submodule.mem_map_equiv]
  change e.ambientEquiv.symm (e.ambientEquiv x) ∈ L.carrier ↔ x ∈ L.carrier
  rw [LinearEquiv.symm_apply_apply]

/-- Two lattice isometries agreeing on the ambient space are equal. -/
@[ext]
theorem ext {e f : Isometry L M} (h : ∀ x, e x = f x) : e = f :=
  DFunLike.coe_injective (funext h)

/-- The identity isometry of an integral lattice. -/
@[refl]
def refl (L : IntegralLattice V) : Isometry L L where
  toIsometryEquiv := .refl L.form
  map_carrier := by
    simpa only [LinearMap.BilinForm.IsometryEquiv.refl,
      LinearEquiv.restrictScalars_toLinearMap, LinearEquiv.refl_toLinearMap,
      LinearMap.restrictScalars_id] using (Submodule.map_id (p := L.carrier))

/-- Evaluation of the identity isometry on an ambient vector. -/
@[simp]
theorem refl_apply (L : IntegralLattice V) (x : V) : refl L x = x := (rfl)

/-- The inverse of an integral-lattice isometry. -/
@[symm]
def symm (e : Isometry L M) : Isometry M L where
  toIsometryEquiv := e.toIsometryEquiv.symm
  map_carrier := (Submodule.map_symm_eq_iff
    ((e : V ≃ₗ[ℚ] W).restrictScalars ℤ)).mpr e.map_carrier

@[simp]
theorem symm_apply_apply (e : Isometry L M) (x : V) : e.symm (e x) = x :=
  (e : V ≃ₗ[ℚ] W).symm_apply_apply x

@[simp]
theorem apply_symm_apply (e : Isometry L M) (y : W) : e (e.symm y) = y :=
  (e : V ≃ₗ[ℚ] W).apply_symm_apply y

/-- Inverting an isometry twice yields the original isometry. -/
@[simp]
theorem symm_symm (e : Isometry L M) : e.symm.symm = e := by
  ext
  rfl

/-- Composition of integral-lattice isometries. -/
@[trans]
def trans (e : Isometry L M) (f : Isometry M N) : Isometry L N where
  toIsometryEquiv := e.toIsometryEquiv.trans f.toIsometryEquiv
  map_carrier := by
    rw [← f.map_carrier, ← e.map_carrier, ← Submodule.map_comp]
    -- The restricted linear map of a composite equivalence is definitionally the composite.
    rfl

@[simp]
theorem trans_apply (e : Isometry L M) (f : Isometry M N) (x : V) : e.trans f x = f (e x) :=
  (rfl)

/-- An isometry composed with its inverse is the identity. -/
@[simp]
theorem self_trans_symm (e : Isometry L M) : e.trans e.symm = refl L := by
  ext
  simp

/-- The inverse of an isometry composed with the isometry is the identity. -/
@[simp]
theorem symm_trans_self (e : Isometry L M) : e.symm.trans e = refl M := by
  ext
  simp

/-- The inverse of a composition is the reversed composition of the inverses. -/
@[simp]
theorem symm_trans (e : Isometry L M) (f : Isometry M N) :
    (e.trans f).symm = f.symm.trans e.symm := by
  ext
  rfl

@[simp]
theorem refl_trans (e : Isometry L M) : (refl L).trans e = e := by ext; rfl

@[simp]
theorem trans_refl (e : Isometry L M) : e.trans (refl M) = e := by ext; rfl

@[simp]
theorem trans_assoc (e : Isometry L M) (f : Isometry M N) {X : Type*}
    [AddCommGroup X] [Module ℚ X] {P : IntegralLattice X} (g : Isometry N P) :
    (e.trans f).trans g = e.trans (f.trans g) := by
  ext
  rfl

/-- The inverse lattice isometry acts as the inverse ambient linear equivalence. -/
theorem coe_symm (e : Isometry L M) : ⇑e.symm = ⇑(e : V ≃ₗ[ℚ] W).symm := by
  funext y
  simp only [symm]
  rfl

@[simp]
theorem ambientEquiv_symm_apply (e : Isometry L M) (y : W) : e.ambientEquiv.symm y = e.symm y := by
  rw [coe_symm]
  rfl

@[simp]
theorem ambientEquiv_refl (L : IntegralLattice V) :
    (refl L).ambientEquiv = LinearEquiv.refl ℤ V := by
  ext x
  rfl

@[simp]
theorem ambientEquiv_symm (e : Isometry L M) : e.symm.ambientEquiv = e.ambientEquiv.symm := by
  ext y
  rw [ambientEquiv_apply, ambientEquiv_symm_apply]

@[simp]
theorem ambientEquiv_trans (e : Isometry L M) (f : Isometry M N) :
    (e.trans f).ambientEquiv = e.ambientEquiv.trans f.ambientEquiv := by
  ext x
  rfl

/-- Restrict an integral-lattice isometry to an integral linear equivalence of its carriers. -/
def carrierEquiv (e : Isometry L M) : L ≃ₗ[ℤ] M :=
  e.ambientEquiv.ofSubmodules L.carrier M.carrier e.map_carrier

@[simp]
theorem coe_carrierEquiv_apply (e : Isometry L M) (x : L) :
    (e.carrierEquiv x : W) = e (x : V) := (rfl)

@[simp]
theorem coe_carrierEquiv_symm_apply (e : Isometry L M) (y : M) :
    (e.carrierEquiv.symm y : V) = e.symm (y : W) := (rfl)

/-- An isometry transports bases of its source carrier to bases of its target carrier. -/
noncomputable def carrierBasisEquiv (e : Isometry L M) (ι : Type*) :
    Basis ι ℤ L ≃ Basis ι ℤ M where
  toFun b := b.map e.carrierEquiv
  invFun b := b.map e.carrierEquiv.symm
  left_inv b := by ext i; simp
  right_inv b := by ext i; simp

@[simp]
theorem carrierBasisEquiv_apply (e : Isometry L M) (b : Basis ι ℤ L) :
    e.carrierBasisEquiv ι b = b.map e.carrierEquiv := (rfl)

@[simp]
theorem carrierBasisEquiv_symm_apply (e : Isometry L M) (b : Basis ι ℤ M) :
    (e.carrierBasisEquiv ι).symm b = b.map e.carrierEquiv.symm := (rfl)

/-- The carrier restriction of the identity isometry is the identity linear equivalence. -/
@[simp]
theorem carrierEquiv_refl (L : IntegralLattice V) :
    (refl L).carrierEquiv = LinearEquiv.refl ℤ L := by
  ext
  rfl

/-- The carrier restriction of an inverse isometry is the inverse of the carrier restriction. -/
@[simp]
theorem carrierEquiv_symm (e : Isometry L M) :
    e.symm.carrierEquiv = e.carrierEquiv.symm := by
  ext
  rfl

/-- The carrier restriction of a composed isometry is the composition of the carrier
restrictions. -/
@[simp]
theorem carrierEquiv_trans (e : Isometry L M) (f : Isometry M N) :
    (e.trans f).carrierEquiv = e.carrierEquiv.trans f.carrierEquiv := by
  ext
  rfl

/-- The carrier equivalence preserves the induced integral bilinear forms. -/
@[simp]
theorem carrierEquiv_map_integralForm (e : Isometry L M) (x y : L) :
    M.integralForm (e.carrierEquiv x) (e.carrierEquiv y) = L.integralForm x y := by
  apply Int.cast_injective (α := ℚ)
  simp

/-- Isometric integral lattices have carriers of the same rank. -/
theorem finrank_carrier_eq (e : Isometry L M) :
    Module.finrank ℤ L = Module.finrank ℤ M :=
  e.carrierEquiv.finrank_eq

/-- The ambient bilinear-form isometry obtained by extending a form-preserving carrier
equivalence. -/
private noncomputable def isometryEquivOfCarrierEquiv (e : L ≃ₗ[ℤ] M)
    (hform : ∀ x y, M.integralForm (e x) (e y) = L.integralForm x y) :
    L.form.IsometryEquiv M.form where
  toLinearEquiv := LinearEquiv.extendOfIsLattice e
  map_app' x y := by
    have hforms :
        M.form.comp (LinearEquiv.extendOfIsLattice e).toLinearMap
          (LinearEquiv.extendOfIsLattice e).toLinearMap = L.form := by
      apply LinearMap.BilinForm.ext_basis L.rationalBasis
      intro i j
      rw [LinearMap.BilinForm.comp_apply, L.rationalBasis_apply, L.rationalBasis_apply,
        LinearEquiv.coe_toLinearMap, LinearEquiv.extendOfIsLattice_apply,
        LinearEquiv.extendOfIsLattice_apply,
        ← M.integralForm_cast, ← L.integralForm_cast]
      exact_mod_cast hform (Module.Free.chooseBasis ℤ L i) (Module.Free.chooseBasis ℤ L j)
    exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y

/-- A form-preserving integral linear equivalence of carriers determines an isometry of the
integral lattices. -/
noncomputable def ofCarrierEquiv (e : L ≃ₗ[ℤ] M)
    (hform : ∀ x y, M.integralForm (e x) (e y) = L.integralForm x y) : Isometry L M where
  toIsometryEquiv := isometryEquivOfCarrierEquiv e hform
  map_carrier := LinearEquiv.extendOfIsLattice_map e

@[simp]
theorem ofCarrierEquiv_apply (e : L ≃ₗ[ℤ] M)
    (hform : ∀ x y, M.integralForm (e x) (e y) = L.integralForm x y) (x : V) :
    ofCarrierEquiv e hform x = LinearEquiv.extendOfIsLattice e x := (rfl)

/-- Restricting the isometry constructed from a form-preserving carrier equivalence recovers the
original carrier equivalence. -/
@[simp]
theorem carrierEquiv_ofCarrierEquiv (e : L ≃ₗ[ℤ] M)
    (hform : ∀ x y, M.integralForm (e x) (e y) = L.integralForm x y) :
    (ofCarrierEquiv e hform).carrierEquiv = e := by
  ext x
  simpa only [coe_carrierEquiv_apply, ofCarrierEquiv_apply] using
    LinearEquiv.extendOfIsLattice_apply e x

/-- Extending the carrier restriction of an isometry recovers the original ambient isometry. -/
@[simp]
theorem ofCarrierEquiv_carrierEquiv (e : Isometry L M) :
    ofCarrierEquiv e.carrierEquiv e.carrierEquiv_map_integralForm = e := by
  have hlinear : (e : V ≃ₗ[ℚ] W) = LinearEquiv.extendOfIsLattice e.carrierEquiv :=
    LinearEquiv.eq_extendOfIsLattice e.carrierEquiv (e : V ≃ₗ[ℚ] W) e.coe_carrierEquiv_apply
  ext x
  simpa only [ofCarrierEquiv_apply, coe_toLinearEquiv] using (LinearEquiv.congr_fun hlinear x).symm

end Isometry

/-- Transport an integral lattice along a rational linear equivalence.

The carrier is the image of the original carrier, and the form is pulled back along the inverse
equivalence. -/
noncomputable def transport (L : IntegralLattice V) (e : V ≃ₗ[ℚ] W) : IntegralLattice W where
  carrier := L.carrier.map (e.restrictScalars ℤ).toLinearMap
  form := L.form.comp e.symm.toLinearMap e.symm.toLinearMap
  isLattice := Submodule.IsLattice.map L.carrier e
  isSymm := ⟨fun x y ↦ L.isSymm.eq (e.symm x) (e.symm y)⟩
  le_dual := by
    rintro _ ⟨x, hx, rfl⟩
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    rintro _ ⟨y, hy, rfl⟩
    rw [LinearMap.BilinForm.comp_apply]
    have hex : e.symm (e.restrictScalars ℤ x) = x := e.symm_apply_apply x
    have hey : e.symm (e.restrictScalars ℤ y) = y := e.symm_apply_apply y
    simpa only [LinearEquiv.coe_coe, hex, hey] using L.le_dual hx y hy

@[simp]
theorem transport_carrier (L : IntegralLattice V) (e : V ≃ₗ[ℚ] W) :
    (L.transport e).carrier = L.carrier.map (e.restrictScalars ℤ).toLinearMap := (rfl)

@[simp]
theorem transport_form (L : IntegralLattice V) (e : V ≃ₗ[ℚ] W) :
    (L.transport e).form = L.form.comp e.symm.toLinearMap e.symm.toLinearMap := (rfl)

/-- The canonical isometry from a lattice to its transport along an ambient equivalence. -/
noncomputable def transportIsometry (L : IntegralLattice V) (e : V ≃ₗ[ℚ] W) :
    Isometry L (L.transport e) where
  toIsometryEquiv := LinearMap.BilinForm.isometryEquivOfCompLinearEquiv L.form e.symm
  -- The construction uses `e.symm.symm`, definitionally equal to `e`, as its underlying map.
  map_carrier := rfl

@[simp]
theorem transportIsometry_apply (L : IntegralLattice V) (e : V ≃ₗ[ℚ] W) (x : V) :
    L.transportIsometry e x = e x := by
  -- `isometryEquivOfCompLinearEquiv B f` has underlying equivalence `f.symm`.
  rfl

@[simp]
theorem transport_refl (L : IntegralLattice V) : L.transport (LinearEquiv.refl ℚ V) = L := by
  apply IntegralLattice.ext
  · simpa only [transport_carrier, LinearEquiv.restrictScalars_toLinearMap,
      LinearEquiv.refl_toLinearMap, LinearMap.restrictScalars_id] using
      (Submodule.map_id (p := L.carrier))
  · ext x y
    simp

end IntegralLattice

end TauCeti
