/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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

## Main definitions

* `TauCeti.IntegralLattice.Isometry`: a form-preserving rational linear equivalence mapping one
  integral carrier onto another.
* `TauCeti.IntegralLattice.Isometry.carrierEquiv`: restriction of an isometry to the carriers.
* `TauCeti.IntegralLattice.Isometry.ofCarrierEquiv`: rational extension of a form-preserving
  integral linear equivalence of carriers.
* `TauCeti.IntegralLattice.transport`: transport of a lattice along a rational linear equivalence.

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
theorem coe_toLinearEquiv (e : Isometry L M) : ⇑(e : V ≃ₗ[ℚ] W) = e := rfl

/-- An integral-lattice isometry preserves the ambient bilinear forms. -/
@[simp]
theorem map_app (e : Isometry L M) (x y : V) : M.form (e x) (e y) = L.form x y :=
  e.toIsometryEquiv.map_app y x

/-- A vector belongs to the target carrier exactly when its inverse image belongs to the source
carrier. -/
theorem mem_carrier_iff_symm_mem (e : Isometry L M) (y : W) :
    y ∈ M.carrier ↔ (e : V ≃ₗ[ℚ] W).symm y ∈ L.carrier := by
  rw [← e.map_carrier]
  let eℤ := (e : V ≃ₗ[ℚ] W).restrictScalars ℤ
  exact Submodule.mem_map_equiv (p := L.carrier) (e := eℤ)

/-- An ambient vector's image belongs to the target carrier if and only if the vector belongs
to the source carrier. -/
@[simp]
theorem mem_carrier_iff (e : Isometry L M) (x : V) : e x ∈ M.carrier ↔ x ∈ L.carrier := by
  rw [e.mem_carrier_iff_symm_mem, ← coe_toLinearEquiv, LinearEquiv.symm_apply_apply]

/-- The image of a source lattice vector belongs to the target carrier. -/
theorem apply_mem_carrier (e : Isometry L M) (x : L) : e (x : V) ∈ M.carrier :=
  (e.mem_carrier_iff (x : V)).mpr x.2

/-- Two lattice isometries agreeing on the ambient space are equal. -/
@[ext]
theorem ext {e f : Isometry L M} (h : ∀ x, e x = f x) : e = f :=
  DFunLike.coe_injective (funext h)

/-- The identity isometry of an integral lattice. -/
@[refl]
def refl (L : IntegralLattice V) : Isometry L L where
  toIsometryEquiv := .refl L.form
  map_carrier := by
    ext x
    simp only [Submodule.mem_map_equiv]
    rfl

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
theorem trans_symm (e : Isometry L M) (f : Isometry M N) :
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

/-- Restrict an integral-lattice isometry to an integral linear equivalence of its carriers. -/
def carrierEquiv (e : Isometry L M) : L ≃ₗ[ℤ] M :=
  ((e : V ≃ₗ[ℚ] W).restrictScalars ℤ).ofSubmodules L.carrier M.carrier e.map_carrier

@[simp]
theorem coe_carrierEquiv_apply (e : Isometry L M) (x : L) :
    (e.carrierEquiv x : W) = e (x : V) := (rfl)

@[simp]
theorem coe_carrierEquiv_symm_apply (e : Isometry L M) (y : M) :
    (e.carrierEquiv.symm y : V) = e.symm (y : W) := (rfl)

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

/-- Isometric integral lattices have ambient rational spaces of the same dimension. -/
theorem finrank_ambient_eq (e : Isometry L M) :
    Module.finrank ℚ V = Module.finrank ℚ W :=
  (e : V ≃ₗ[ℚ] W).finrank_eq

/-- Extend an integral linear equivalence between full carriers to their rational ambient spaces.

The construction uses the chosen basis of the source carrier, its image under `e`, and Mathlib's
`Basis.extendOfIsLattice` on both sides. -/
noncomputable def extendCarrierEquiv (e : L ≃ₗ[ℤ] M) : V ≃ₗ[ℚ] W :=
  let b := Module.Free.chooseBasis ℤ L
  (b.extendOfIsLattice ℚ).equiv ((b.map e).extendOfIsLattice ℚ) (Equiv.refl _)

/-- The rational extension of a carrier equivalence agrees with it on every lattice vector. -/
@[simp]
theorem extendCarrierEquiv_apply (e : L ≃ₗ[ℤ] M) (x : L) :
    extendCarrierEquiv e (x : V) = (e x : W) := by
  let b := Module.Free.chooseBasis ℤ L
  let f : L →ₗ[ℤ] W :=
    (extendCarrierEquiv e).toLinearMap.restrictScalars ℤ ∘ₗ L.carrier.subtype
  let g : L →ₗ[ℤ] W := M.carrier.subtype ∘ₗ e.toLinearMap
  have hfg : f = g := by
    apply b.ext
    intro i
    have hf_apply : f (b i) = extendCarrierEquiv e (b i : V) := by
      simp only [f, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply,
        LinearEquiv.coe_toLinearMap]
    have hg_apply : g (b i) = (e (b i) : W) := by
      simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_toLinearMap]
    rw [hf_apply, hg_apply, ← Basis.extendOfIsLattice_apply ℚ b i]
    unfold extendCarrierEquiv
    rw [Basis.equiv_apply, Basis.extendOfIsLattice_apply, Basis.map_apply, Equiv.refl_apply]
  exact LinearMap.congr_fun hfg x

/-- The rational extension of a carrier equivalence maps the source carrier onto the target
carrier. -/
theorem extendCarrierEquiv_map_carrier (e : L ≃ₗ[ℤ] M) :
    L.carrier.map ((extendCarrierEquiv e).restrictScalars ℤ).toLinearMap = M.carrier := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [LinearEquiv.restrictScalars_toLinearMap, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_toLinearMap, extendCarrierEquiv_apply e ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).2
  · intro hy
    let yM : M := ⟨y, hy⟩
    let xL : L := e.symm yM
    refine ⟨(xL : V), xL.2, ?_⟩
    rw [LinearEquiv.restrictScalars_toLinearMap, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_toLinearMap, extendCarrierEquiv_apply]
    exact congr_arg Subtype.val (e.apply_symm_apply yM)

/-- The ambient bilinear-form isometry obtained by extending a form-preserving carrier
equivalence. -/
private noncomputable def isometryEquivOfCarrierEquiv (e : L ≃ₗ[ℤ] M)
    (hform : ∀ x y, M.integralForm (e x) (e y) = L.integralForm x y) :
    L.form.IsometryEquiv M.form where
  toLinearEquiv := extendCarrierEquiv e
  map_app' x y := by
    let b := Module.Free.chooseBasis ℤ L
    have hforms :
        M.form.comp (extendCarrierEquiv e).toLinearMap (extendCarrierEquiv e).toLinearMap =
          L.form := by
      apply LinearMap.BilinForm.ext_basis (b.extendOfIsLattice ℚ)
      intro i j
      rw [LinearMap.BilinForm.comp_apply, Basis.extendOfIsLattice_apply,
        Basis.extendOfIsLattice_apply]
      have hi : (extendCarrierEquiv e).toLinearMap (b i : V) = (e (b i) : W) :=
        extendCarrierEquiv_apply e (b i)
      have hj : (extendCarrierEquiv e).toLinearMap (b j : V) = (e (b j) : W) :=
        extendCarrierEquiv_apply e (b j)
      rw [hi, hj, ← M.integralForm_cast, ← L.integralForm_cast]
      exact_mod_cast hform (b i) (b j)
    exact DFunLike.congr_fun (DFunLike.congr_fun hforms x) y

/-- A form-preserving integral linear equivalence of carriers determines an isometry of the
integral lattices. -/
noncomputable def ofCarrierEquiv (e : L ≃ₗ[ℤ] M)
    (hform : ∀ x y, M.integralForm (e x) (e y) = L.integralForm x y) : Isometry L M where
  toIsometryEquiv := isometryEquivOfCarrierEquiv e hform
  map_carrier := extendCarrierEquiv_map_carrier e

@[simp]
theorem ofCarrierEquiv_apply (e : L ≃ₗ[ℤ] M)
    (hform : ∀ x y, M.integralForm (e x) (e y) = L.integralForm x y) (x : V) :
    ofCarrierEquiv e hform x = extendCarrierEquiv e x := (rfl)

/-- Restricting the isometry constructed from a form-preserving carrier equivalence recovers the
original carrier equivalence. -/
@[simp]
theorem ofCarrierEquiv_carrierEquiv (e : L ≃ₗ[ℤ] M)
    (hform : ∀ x y, M.integralForm (e x) (e y) = L.integralForm x y) :
    (ofCarrierEquiv e hform).carrierEquiv = e := by
  ext x
  simpa only [coe_carrierEquiv_apply, ofCarrierEquiv_apply] using extendCarrierEquiv_apply e x

/-- Extending the carrier restriction of an isometry recovers the original ambient isometry. -/
@[simp]
theorem ofCarrierEquiv_carrierEquiv_self (e : Isometry L M) :
    ofCarrierEquiv e.carrierEquiv e.carrierEquiv_map_integralForm = e := by
  have hlinear : extendCarrierEquiv e.carrierEquiv = (e : V ≃ₗ[ℚ] W) := by
    apply LinearEquiv.toLinearMap_injective
    apply L.rationalBasis.ext
    intro i
    rw [L.rationalBasis_apply]
    exact (extendCarrierEquiv_apply e.carrierEquiv (Module.Free.chooseBasis ℤ L i)).trans
      (e.coe_carrierEquiv_apply (Module.Free.chooseBasis ℤ L i))
  ext x
  simpa only [ofCarrierEquiv_apply, coe_toLinearEquiv] using LinearEquiv.congr_fun hlinear x

end Isometry

private theorem isLattice_map (S : Submodule ℤ V) [S.IsLattice ℚ] (e : V ≃ₗ[ℚ] W) :
    (S.map (e.restrictScalars ℤ).toLinearMap).IsLattice ℚ where
  fg := Submodule.FG.map (e.restrictScalars ℤ).toLinearMap Submodule.IsLattice.fg
  span_eq_top := by
    rw [Submodule.map_coe, LinearEquiv.restrictScalars_toLinearMap, LinearMap.coe_restrictScalars,
      LinearEquiv.coe_toLinearMap, Submodule.span_image_linearEquiv,
      Submodule.IsLattice.span_eq_top]
    simp

/-- Transport an integral lattice along a rational linear equivalence.

The carrier is the image of the original carrier, and the form is pulled back along the inverse
equivalence. -/
noncomputable def transport (L : IntegralLattice V) (e : V ≃ₗ[ℚ] W) : IntegralLattice W where
  carrier := L.carrier.map (e.restrictScalars ℤ).toLinearMap
  form := L.form.comp e.symm.toLinearMap e.symm.toLinearMap
  isLattice := isLattice_map L.carrier e
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

/-- Evaluation of the transported form on vectors. -/
theorem transport_apply (L : IntegralLattice V) (e : V ≃ₗ[ℚ] W) (x y : W) :
    L.transport e x y = L.form (e.symm x) (e.symm y) := (rfl)

/-- The canonical isometry from a lattice to its transport along an ambient equivalence. -/
noncomputable def transportIsometry (L : IntegralLattice V) (e : V ≃ₗ[ℚ] W) :
    Isometry L (L.transport e) where
  toIsometryEquiv := LinearMap.BilinForm.isometryEquivOfCompLinearEquiv L.form e.symm
  map_carrier := rfl

@[simp]
theorem transportIsometry_apply (L : IntegralLattice V) (e : V ≃ₗ[ℚ] W) (x : V) :
    L.transportIsometry e x = e x := (rfl)

@[simp]
theorem transport_refl (L : IntegralLattice V) : L.transport (LinearEquiv.refl ℚ V) = L := by
  apply IntegralLattice.ext
  · simp only [transport_carrier]
    ext x
    simp only [Submodule.mem_map_equiv]
    rfl
  · ext x y
    simp

end IntegralLattice

end TauCeti
