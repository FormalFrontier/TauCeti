/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.Algebra.AddCircle
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Bilinear
public import TauCeti.LinearAlgebra.IntegralLattice.Even

/-!
# Discriminant quadratic modules of even integral lattices

For an even nondegenerate integral lattice `L`, the half-norm of a dual vector descends to its
discriminant group:

```text
q_L (x + L) = L.form x x / 2 mod Z.
```

Evenness is exactly what makes this independent of the representative.  Indeed, translating `x`
by a lattice vector `l` changes the half-norm by `L.form x l + L.form l l / 2`; the first term is
integral because `x` lies in the dual lattice, and the second is integral because `L` is even.
The polar of the descended quadratic map is the discriminant pairing
`b_L (x + L) (y + L) = L.form x y mod Z`.

The construction uses Mathlib's `QuadraticMap.lift`: the half-norm first defines a quadratic map
on the dual carrier, and evenness puts the original carrier in its quadratic radical.  The final
package reuses `discriminantBilinearModule` as its underlying finite bilinear module, so its
nondegeneracy and its functoriality under lattice isometries are inherited from the bilinear
construction.

## Main declarations

* `TauCeti.IntegralLattice.discriminantQuadraticMap`: the descended half-norm on `A_L`.
* `TauCeti.IntegralLattice.discriminantQuadraticModule`: the packaged finite quadratic module.
* `TauCeti.IntegralLattice.isNondegenerate_discriminantQuadraticModule`: nondegeneracy of its
  polar pairing.
* `TauCeti.IntegralLattice.Isometry.discriminantQuadraticIsometry`: functoriality under lattice
  isometry.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, section 1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 3.
-/

public section

namespace TauCeti

universe u v w

namespace IntegralLattice

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- Half the ambient form on two dual-carrier vectors, reduced modulo `Z`.

Its associated quadratic map is the half-norm before quotienting by the original carrier. -/
private def dualCarrierHalfFormModOne (L : IntegralLattice V) :
    L.dualCarrier →ₗ[ℤ] L.dualCarrier →ₗ[ℤ] AddCircle (1 : ℚ) :=
  LinearMap.mk₂' ℤ ℤ (fun x y ↦ ((L.form x y / 2 : ℚ) : AddCircle (1 : ℚ)))
    (fun x y z ↦ by simp [add_div])
    (fun r x y ↦ by simp [mul_div_assoc])
    (fun x y z ↦ by simp [add_div])
    (fun r x y ↦ by simp [mul_div_assoc])

private theorem dualCarrierHalfFormModOne_apply (L : IntegralLattice V)
    (x y : L.dualCarrier) :
    L.dualCarrierHalfFormModOne x y =
      ((L.form x y / 2 : ℚ) : AddCircle (1 : ℚ)) :=
  rfl

/-- The half-norm quadratic map on the dual carrier, before passage to the discriminant group. -/
private def dualCarrierHalfNormModOne (L : IntegralLattice V) :
    QuadraticMap ℤ L.dualCarrier (AddCircle (1 : ℚ)) :=
  LinearMap.BilinMap.toQuadraticMap L.dualCarrierHalfFormModOne

private theorem dualCarrierHalfNormModOne_apply (L : IntegralLattice V)
    (x : L.dualCarrier) :
    L.dualCarrierHalfNormModOne x =
      ((L.form x x / 2 : ℚ) : AddCircle (1 : ℚ)) :=
  rfl

/-- For an even lattice, its original carrier lies in the radical of the half-norm modulo `Z` on
the dual carrier.  This is the representative-independence condition for the discriminant
quadratic map. -/
private theorem carrierInDual_le_radical_dualCarrierHalfNormModOne
    (L : IntegralLattice V) (hL : L.IsEven) :
    L.carrierInDual ≤ L.dualCarrierHalfNormModOne.radical := by
  intro x hx
  constructor
  · rw [dualCarrierHalfNormModOne_apply]
    obtain ⟨z, hz⟩ := hL.exists_norm_eq_two_mul
      ⟨x, (L.mem_carrierInDual_iff x).mp hx⟩
    refine (AddCircle.coe_eq_zero_iff_mem_one _).mpr (Submodule.mem_one.mpr ⟨z, ?_⟩)
    rw [L.norm_apply] at hz
    rw [eq_intCast, hz]
    ring
  · apply LinearMap.ext
    intro y
    rw [dualCarrierHalfNormModOne, QuadraticMap.polarBilin_apply_apply, LinearMap.zero_apply,
      LinearMap.BilinMap.polar_toQuadraticMap, dualCarrierHalfFormModOne_apply,
      dualCarrierHalfFormModOne_apply, L.isSymm.eq]
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp
      (y.2 x ((L.mem_carrierInDual_iff x).mp hx))
    rw [← AddCircle.coe_add]
    refine (AddCircle.coe_eq_zero_iff_mem_one _).mpr (Submodule.mem_one.mpr ⟨z, ?_⟩)
    have hz' : L.form y x = (z : ℚ) := by simpa using hz.symm
    rw [eq_intCast, hz']
    ring

/-- The discriminant quadratic map of an even integral lattice, in the half-norm convention.

The definition does not require nondegeneracy; that hypothesis is needed only to make the
discriminant group finite and hence package it as a `FiniteQuadraticModule`. -/
noncomputable def discriminantQuadraticMap (L : IntegralLattice V) (hL : L.IsEven) :
    QuadraticMap ℤ L.DiscriminantGroup (AddCircle (1 : ℚ)) :=
  L.dualCarrierHalfNormModOne.lift L.carrierInDual
    (L.carrierInDual_le_radical_dualCarrierHalfNormModOne hL)

/-- On a representative, the discriminant quadratic map is the ambient half-norm modulo `Z`. -/
@[simp]
theorem discriminantQuadraticMap_mk (L : IntegralLattice V) (hL : L.IsEven)
    (x : L.dualCarrier) :
    L.discriminantQuadraticMap hL (Submodule.Quotient.mk x) =
      ((L.form x x / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  rw [discriminantQuadraticMap, QuadraticMap.lift_mk,
    dualCarrierHalfNormModOne_apply]

/-- The discriminant quadratic value of a representative vanishes exactly when the ambient
self-pairing is twice an integer. -/
theorem discriminantQuadraticMap_mk_eq_zero_iff (L : IntegralLattice V) (hL : L.IsEven)
    (x : L.dualCarrier) :
    L.discriminantQuadraticMap hL (Submodule.Quotient.mk x) = 0 ↔
      ∃ n : ℤ, L.form x x = ((2 * n : ℤ) : ℚ) := by
  rw [discriminantQuadraticMap_mk, AddCircle.coe_eq_zero_iff_mem_one]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp h
    rw [eq_intCast] at hn
    refine ⟨n, ?_⟩
    push_cast
    linarith [hn]
  · rintro ⟨n, hn⟩
    refine Submodule.mem_one.mpr ⟨n, ?_⟩
    rw [eq_intCast, hn]
    push_cast
    ring

/-- The polar of the half-norm discriminant quadratic map is the discriminant pairing. -/
@[simp]
theorem polar_discriminantQuadraticMap (L : IntegralLattice V) (hL : L.IsEven)
    (x y : L.DiscriminantGroup) :
    QuadraticMap.polar (L.discriminantQuadraticMap hL) x y =
      L.discriminantPairing x y := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      simp only [QuadraticMap.polar, ← Submodule.Quotient.mk_add,
        discriminantQuadraticMap_mk, discriminantPairing_mk, Submodule.coe_add,
        map_add, LinearMap.add_apply, L.isSymm.eq]
      simp only [← AddCircle.coe_sub]
      congr 1
      ring

/-- The polar bilinear map of the half-norm discriminant quadratic map is the discriminant
pairing. -/
@[simp]
theorem polarBilin_discriminantQuadraticMap (L : IntegralLattice V) (hL : L.IsEven) :
    (L.discriminantQuadraticMap hL).polarBilin = L.discriminantPairing := by
  apply LinearMap.ext₂
  intro x y
  exact L.polar_discriminantQuadraticMap hL x y

/-- The discriminant group of an even nondegenerate integral lattice, equipped with its canonical
half-norm quadratic map and discriminant polar pairing. -/
@[expose] noncomputable def discriminantQuadraticModule (L : IntegralLattice V)
    [L.IsNondegenerate] (hL : L.IsEven) : FiniteQuadraticModule where
  toFiniteBilinearModule := L.discriminantBilinearModule
  quadratic := L.discriminantQuadraticMap hL
  polar_eq_pairing' x y :=
    (L.polar_discriminantQuadraticMap hL x y).trans
      (L.discriminantBilinearModule_pairing x y).symm

/-- The quadratic map of the discriminant quadratic module is the descended half-norm. -/
@[simp]
theorem discriminantQuadraticModule_quadratic (L : IntegralLattice V)
    [L.IsNondegenerate] (hL : L.IsEven) (x : L.DiscriminantGroup) :
    (L.discriminantQuadraticModule hL).quadratic x = L.discriminantQuadraticMap hL x :=
  rfl

/-- The polar finite bilinear module of the discriminant quadratic module is the existing
discriminant bilinear module. -/
theorem discriminantQuadraticModule_toFiniteBilinearModule (L : IntegralLattice V)
    [L.IsNondegenerate] (hL : L.IsEven) :
    (L.discriminantQuadraticModule hL).toFiniteBilinearModule =
      L.discriminantBilinearModule :=
  rfl

/-- The discriminant quadratic module of an even nondegenerate lattice is nondegenerate. -/
theorem isNondegenerate_discriminantQuadraticModule (L : IntegralLattice V)
    [L.IsNondegenerate] (hL : L.IsEven) :
    (L.discriminantQuadraticModule hL).IsNondegenerate :=
  L.isNondegenerate_discriminantBilinearModule

namespace Isometry

variable {W : Type v} {U : Type w}
variable [AddCommGroup W] [Module ℚ W]
variable [AddCommGroup U] [Module ℚ U]
variable {L : IntegralLattice V} {M : IntegralLattice W} {N : IntegralLattice U}

/-- An integral-lattice isometry preserves the discriminant quadratic value. -/
private theorem map_discriminantQuadraticMap (e : Isometry L M) (hL : L.IsEven)
    (x : L.DiscriminantGroup) :
    M.discriminantQuadraticMap (e.isEven_iff.mp hL) (e.discriminantGroupEquiv x) =
      L.discriminantQuadraticMap hL x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    simp only [discriminantGroupEquiv_mk, discriminantQuadraticMap_mk,
      coe_dualCarrierEquiv_apply, e.map_app]

/-- An isometry of even nondegenerate integral lattices induces an isometry of their
discriminant quadratic modules. -/
noncomputable def discriminantQuadraticIsometry (e : Isometry L M)
    [L.IsNondegenerate] [M.IsNondegenerate] (hL : L.IsEven) :
    FiniteQuadraticModule.Isometry (L.discriminantQuadraticModule hL)
      (M.discriminantQuadraticModule (e.isEven_iff.mp hL)) where
  toLinearEquiv := e.discriminantGroupEquiv
  map_app' := e.map_discriminantQuadraticMap hL

/-- The underlying additive equivalence of the induced discriminant quadratic isometry is the
discriminant-group equivalence. -/
@[simp]
theorem discriminantQuadraticIsometry_toAddEquiv (e : Isometry L M)
    [L.IsNondegenerate] [M.IsNondegenerate] (hL : L.IsEven) :
    (e.discriminantQuadraticIsometry hL).toAddEquiv =
      e.discriminantGroupEquiv.toAddEquiv :=
  (rfl)

/-- The induced discriminant quadratic isometry acts through the discriminant-group
equivalence. -/
@[simp]
theorem discriminantQuadraticIsometry_apply (e : Isometry L M)
    [L.IsNondegenerate] [M.IsNondegenerate] (hL : L.IsEven)
    (x : L.DiscriminantGroup) :
    e.discriminantQuadraticIsometry hL x = e.discriminantGroupEquiv x :=
  (rfl)

/-- The induced discriminant quadratic isometry maps a representative through the dual-carrier
equivalence. -/
theorem discriminantQuadraticIsometry_mk (e : Isometry L M)
    [L.IsNondegenerate] [M.IsNondegenerate] (hL : L.IsEven) (x : L.dualCarrier) :
    e.discriminantQuadraticIsometry hL (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e.dualCarrierEquiv x) := by
  rw [e.discriminantQuadraticIsometry_apply hL, e.discriminantGroupEquiv_mk]

/-- Forgetting the quadratic map from the induced isometry recovers the discriminant bilinear
isometry. -/
@[simp]
theorem discriminantQuadraticIsometry_toFiniteBilinearModule (e : Isometry L M)
    [L.IsNondegenerate] [M.IsNondegenerate] (hL : L.IsEven) :
    (e.discriminantQuadraticIsometry hL).toFiniteBilinearModule =
      e.discriminantBilinearIsometry := by
  apply FiniteBilinearModule.Isometry.toAddEquiv_injective
  rw [FiniteQuadraticModule.Isometry.toFiniteBilinearModule_toAddEquiv,
    discriminantQuadraticIsometry_toAddEquiv,
    discriminantBilinearIsometry_toAddEquiv]

end Isometry

end IntegralLattice

end TauCeti
