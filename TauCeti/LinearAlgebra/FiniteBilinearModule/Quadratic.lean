/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Finite quadratic modules

A finite quadratic module is a finite abelian group equipped with a quadratic map to `ℚ/ℤ`.
Its symmetric bilinear pairing is not stored separately: it is the polar form of the quadratic
map.  This file packages that canonical underlying finite bilinear module and develops restriction,
form negation, orthogonal products, isometries, quadratic-isotropic subgroups, and quadratic
Lagrangians.

The convention is the half-norm convention used for discriminant forms: for an even integral
lattice the quadratic value of a dual class represented by `x` is `B(x, x) / 2` modulo `ℤ`, and
the polar pairing is therefore `B(x, y)` modulo `ℤ`.

## Main definitions

* `TauCeti.FiniteQuadraticModule`: a finite abelian group with an `AddCircle (1 : ℚ)`-valued
  quadratic map.
* `TauCeti.FiniteQuadraticModule.toFiniteBilinearModule`: the canonical polar bilinear module.
* `TauCeti.FiniteQuadraticModule.Isometry`: a quadratic-map isometric equivalence.
* `TauCeti.FiniteQuadraticModule.IsIsotropic`: quadratic isotropy of an additive subgroup.
* `TauCeti.FiniteQuadraticModule.IsLagrangian`: a quadratic-isotropic subgroup equal to its
  bilinear orthogonal complement.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.

This is the finite-quadratic-module part of Layer 3 of
`TauCetiRoadmap/IntegralLattices/README.md`.
-/

public section

namespace TauCeti

universe u v

/-- A finite abelian group equipped with a quadratic map to `ℚ/ℤ`.

The associated bilinear pairing is required to be the polar form, so the quadratic map determines
all pairing values. -/
structure FiniteQuadraticModule extends toFiniteBilinearModule : FiniteBilinearModule where
  /-- The `ℚ/ℤ`-valued quadratic map. -/
  quadratic : QuadraticMap ℤ toFiniteBilinearModule.carrier (AddCircle (1 : ℚ))
  /-- The polar form is the stored bilinear pairing. -/
  polar_eq_pairing' : ∀ x y,
    QuadraticMap.polar quadratic x y = toFiniteBilinearModule.pairing x y

namespace FiniteQuadraticModule

/-- A finite quadratic module coerces to its underlying type. -/
instance : CoeSort FiniteQuadraticModule (Type u) :=
  ⟨fun A ↦ A.toFiniteBilinearModule.carrier⟩

variable (A : FiniteQuadraticModule)

/-- The polar of the quadratic map is the pairing of the underlying finite bilinear module. -/
@[simp]
theorem polar_eq_pairing (x y : A) :
    QuadraticMap.polar A.quadratic x y = A.toFiniteBilinearModule.pairing x y :=
  A.polar_eq_pairing' x y

/-- The bilinear map of the underlying finite bilinear module is exactly the polar bilinear map. -/
theorem toFiniteBilinearModule_toBilin :
    A.toFiniteBilinearModule.toBilin = A.quadratic.polarBilin := by
  ext x y
  rw [FiniteBilinearModule.toBilin_apply, QuadraticMap.polarBilin_apply_apply,
    A.polar_eq_pairing]

/-- A finite quadratic module is nondegenerate when its polar pairing is nondegenerate. -/
abbrev IsNondegenerate : Prop := A.toFiniteBilinearModule.IsNondegenerate

/-- A nondegenerate finite quadratic module is identified with the character dual by its polar
pairing. -/
noncomputable def adjointEquiv (hA : A.IsNondegenerate) :
    A ≃+ CharacterModule A :=
  A.toFiniteBilinearModule.adjointEquiv hA

@[simp]
theorem adjointEquiv_apply (hA : A.IsNondegenerate) (x : A) :
    A.adjointEquiv hA x = A.toFiniteBilinearModule.pairing x := by
  exact A.toFiniteBilinearModule.adjointEquiv_apply hA x

/-- An isometry of finite quadratic modules is Mathlib's isometric equivalence of their quadratic
maps. -/
abbrev Isometry (A : FiniteQuadraticModule.{u}) (B : FiniteQuadraticModule.{v}) : Type (max u v) :=
  A.quadratic.IsometryEquiv B.quadratic

namespace Isometry

variable {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}

/-- A quadratic isometry induces an isometry of the canonical polar bilinear modules. -/
def toFiniteBilinearModule (f : Isometry A B) :
    FiniteBilinearModule.Isometry A.toFiniteBilinearModule B.toFiniteBilinearModule where
  toAddEquiv := f.toLinearEquiv.toAddEquiv
  map_pairing' x y := by
    rw [← B.polar_eq_pairing, ← A.polar_eq_pairing]
    simp only [QuadraticMap.polar]
    rw [← f.toAddEquiv.map_add]
    have hxy : B.quadratic (f.toAddEquiv (x + y)) = A.quadratic (x + y) := f.map_app (x + y)
    have hx : B.quadratic (f.toAddEquiv x) = A.quadratic x := f.map_app x
    have hy : B.quadratic (f.toAddEquiv y) = A.quadratic y := f.map_app y
    rw [hxy, hx, hy]

/-- The induced bilinear isometry has the same underlying additive equivalence. -/
@[simp]
theorem toFiniteBilinearModule_toAddEquiv (f : Isometry A B) :
    f.toFiniteBilinearModule.toAddEquiv = f.toAddEquiv := (rfl)

/-- Nondegeneracy transfers along a quadratic isometry. -/
theorem isNondegenerate (f : Isometry A B) (hA : A.IsNondegenerate) : B.IsNondegenerate :=
  f.toFiniteBilinearModule.isNondegenerate hA

/-- Nondegeneracy is invariant under quadratic isometry. -/
theorem isNondegenerate_iff (f : Isometry A B) : A.IsNondegenerate ↔ B.IsNondegenerate :=
  f.toFiniteBilinearModule.isNondegenerate_iff

end Isometry

/-! ## Canonical constructions -/

/-- Restrict a finite quadratic module to an additive subgroup.

No nondegeneracy conclusion is asserted: the polar pairing can become degenerate after
restriction. -/
@[expose] def restrict (H : AddSubgroup A) : FiniteQuadraticModule where
  toFiniteBilinearModule := A.toFiniteBilinearModule.restrict H
  quadratic := A.quadratic.restrict H.toIntSubmodule
  polar_eq_pairing' x y := by
    rw [FiniteBilinearModule.restrict_pairing, ← A.polar_eq_pairing]
    rfl

@[simp]
theorem restrict_quadratic (H : AddSubgroup A) (x : H) :
    (A.restrict H).quadratic x = A.quadratic x.1 := by
  rfl

@[simp]
theorem restrict_pairing (H : AddSubgroup A) (x y : H) :
    (A.restrict H).toFiniteBilinearModule.pairing x y =
      A.toFiniteBilinearModule.pairing x.1 y.1 := by
  rfl

/-- Taking the polar bilinear module commutes with restriction. -/
@[simp]
theorem restrict_toFiniteBilinearModule (H : AddSubgroup A) :
    (A.restrict H).toFiniteBilinearModule = A.toFiniteBilinearModule.restrict H := by
  rfl

/-- Negate the quadratic map of a finite quadratic module. -/
@[expose] def neg : FiniteQuadraticModule where
  toFiniteBilinearModule := A.toFiniteBilinearModule.neg
  quadratic := -A.quadratic
  polar_eq_pairing' x y := by
    rw [FiniteBilinearModule.neg_pairing, ← A.polar_eq_pairing]
    exact QuadraticMap.polar_neg A.quadratic x y

@[simp]
theorem neg_quadratic (x : A) : A.neg.quadratic x = -A.quadratic x := by
  rfl

@[simp]
theorem neg_pairing (x y : A) :
    A.neg.toFiniteBilinearModule.pairing x y =
      -A.toFiniteBilinearModule.pairing x y := by
  rfl

/-- Taking the polar bilinear module commutes with form negation. -/
@[simp]
theorem neg_toFiniteBilinearModule :
    A.neg.toFiniteBilinearModule = A.toFiniteBilinearModule.neg := by
  rfl

/-- Form negation preserves nondegeneracy. -/
@[simp]
theorem isNondegenerate_neg : A.neg.IsNondegenerate ↔ A.IsNondegenerate := by
  exact A.toFiniteBilinearModule.isNondegenerate_neg

/-- The orthogonal product of two finite quadratic modules. -/
@[expose] def prod (B : FiniteQuadraticModule) : FiniteQuadraticModule where
  toFiniteBilinearModule := A.toFiniteBilinearModule.prod B.toFiniteBilinearModule
  quadratic := A.quadratic.prod B.quadratic
  polar_eq_pairing' x y := by
    rw [FiniteBilinearModule.prod_pairing, ← A.polar_eq_pairing, ← B.polar_eq_pairing]
    exact QuadraticMap.polar_prod A.quadratic B.quadratic x y

@[simp]
theorem prod_quadratic (B : FiniteQuadraticModule) (x : A) (y : B) :
    (A.prod B).quadratic (x, y) = A.quadratic x + B.quadratic y := by
  rfl

@[simp]
theorem prod_pairing (B : FiniteQuadraticModule) (x y : A.carrier × B.carrier) :
    (A.prod B).toFiniteBilinearModule.pairing x y =
      A.toFiniteBilinearModule.pairing x.1 y.1 +
        B.toFiniteBilinearModule.pairing x.2 y.2 := by
  rfl

/-- Taking the polar bilinear module commutes with orthogonal products. -/
@[simp]
theorem prod_toFiniteBilinearModule (B : FiniteQuadraticModule) :
    (A.prod B).toFiniteBilinearModule =
      A.toFiniteBilinearModule.prod B.toFiniteBilinearModule := by
  rfl

/-- An orthogonal product is nondegenerate exactly when both factors are nondegenerate. -/
@[simp]
theorem isNondegenerate_prod (B : FiniteQuadraticModule) :
    (A.prod B).IsNondegenerate ↔ A.IsNondegenerate ∧ B.IsNondegenerate := by
  exact A.toFiniteBilinearModule.isNondegenerate_prod B.toFiniteBilinearModule

/-! ## Quadratic isotropy -/

/-- An element of a finite quadratic module is isotropic when its quadratic value vanishes. -/
def IsIsotropicElem (x : A) : Prop := A.quadratic x = 0

/-- Zero is quadratically isotropic. -/
@[simp]
theorem isIsotropicElem_zero : A.IsIsotropicElem 0 := by
  simp [IsIsotropicElem]

/-- Negating an element preserves quadratic isotropy. -/
@[simp]
theorem isIsotropicElem_neg (x : A) : A.IsIsotropicElem (-x) ↔ A.IsIsotropicElem x := by
  simp [IsIsotropicElem]

/-- A quadratic isometry preserves isotropic elements. -/
@[simp]
theorem Isometry.isIsotropicElem_iff {B : FiniteQuadraticModule} (f : Isometry A B) (x : A) :
    B.IsIsotropicElem (f x) ↔ A.IsIsotropicElem x := by
  simp [IsIsotropicElem]

/-- Form negation preserves quadratic isotropy. -/
@[simp]
theorem isIsotropicElem_neg_module (x : A) : A.neg.IsIsotropicElem x ↔ A.IsIsotropicElem x := by
  simp [IsIsotropicElem]

/-- An element of an orthogonal product is quadratically isotropic exactly when the sum of its
quadratic values vanishes. -/
@[simp]
theorem isIsotropicElem_prod (B : FiniteQuadraticModule) (x : A) (y : B) :
    (A.prod B).IsIsotropicElem (x, y) ↔ A.quadratic x + B.quadratic y = 0 := by
  simp [IsIsotropicElem]

/-- A subgroup is quadratically isotropic when the quadratic map vanishes on it. -/
def IsIsotropic (H : AddSubgroup A) : Prop := ∀ x ∈ H, A.quadratic x = 0

/-- Quadratic isotropy of a subgroup, unfolded to its defining property. -/
theorem isIsotropic_def {H : AddSubgroup A} :
    A.IsIsotropic H ↔ ∀ x ∈ H, A.quadratic x = 0 :=
  Iff.rfl

/-- A quadratic isometry transports quadratic isotropy of a subgroup. -/
@[simp]
theorem Isometry.isIsotropic_map_iff {B : FiniteQuadraticModule} (f : Isometry A B)
    (H : AddSubgroup A) :
    B.IsIsotropic (H.map f.toAddEquiv) ↔ A.IsIsotropic H := by
  simp only [IsIsotropic]
  constructor
  · intro hH x hx
    rw [← f.map_app x]
    exact hH (f x) ⟨x, hx, rfl⟩
  · intro hH y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (f.map_app x).trans (hH x hx)

/-- An element of a quadratically isotropic subgroup is isotropic. -/
theorem isIsotropicElem_of_mem_isIsotropic {H : AddSubgroup A} (hH : A.IsIsotropic H)
    {x : A} (hx : x ∈ H) : A.IsIsotropicElem x :=
  hH x hx

/-- Quadratic isotropy passes to additive subgroups. -/
theorem IsIsotropic.mono {H K : AddSubgroup A} (hK : A.IsIsotropic K) (h : H ≤ K) :
    A.IsIsotropic H := fun x hx ↦ hK x (h hx)

/-- The trivial subgroup is quadratically isotropic. -/
@[simp]
theorem isIsotropic_bot : A.IsIsotropic ⊥ := by
  simp [IsIsotropic]

/-- A subgroup is quadratically isotropic exactly when the restricted quadratic map is zero. -/
theorem isIsotropic_iff_restrict_eq_zero (H : AddSubgroup A) :
    A.IsIsotropic H ↔ (A.restrict H).quadratic = 0 := by
  constructor
  · intro hH
    ext x
    exact hH x.1 x.2
  · intro h x hx
    rw [← A.restrict_quadratic H (⟨x, hx⟩ : H), h]
    rfl

/-- Quadratic isotropy implies bilinear isotropy for the polar pairing. -/
theorem IsIsotropic.toFiniteBilinearModule {H : AddSubgroup A} (hH : A.IsIsotropic H) :
    A.toFiniteBilinearModule.IsIsotropic H := by
  rw [A.toFiniteBilinearModule.isIsotropic_iff_le_orthogonalComplement]
  intro x hx
  rw [A.toFiniteBilinearModule.mem_orthogonalComplement_iff]
  intro y hy
  rw [← A.polar_eq_pairing]
  simp only [QuadraticMap.polar, hH x hx, hH y hy,
    hH (x + y) (H.add_mem hx hy), sub_zero]

/-- A quadratically isotropic subgroup is contained in its bilinear orthogonal complement. -/
theorem IsIsotropic.le_orthogonalComplement {H : AddSubgroup A} (hH : A.IsIsotropic H) :
    H ≤ A.toFiniteBilinearModule.orthogonalComplement H :=
  A.toFiniteBilinearModule.isIsotropic_iff_le_orthogonalComplement H |>.mp
    hH.toFiniteBilinearModule

/-- A quadratic Lagrangian is a quadratically isotropic subgroup which is Lagrangian for the
polar bilinear pairing. -/
def IsLagrangian (H : AddSubgroup A) : Prop :=
  A.IsIsotropic H ∧ A.toFiniteBilinearModule.IsLagrangian H

/-- A quadratic isometry transports quadratic Lagrangian subgroups. -/
@[simp]
theorem Isometry.isLagrangian_map_iff {B : FiniteQuadraticModule} (f : Isometry A B)
    (H : AddSubgroup A) :
    B.IsLagrangian (H.map f.toAddEquiv) ↔ A.IsLagrangian H := by
  rw [IsLagrangian, IsLagrangian, f.isIsotropic_map_iff]
  rw [← f.toFiniteBilinearModule_toAddEquiv,
    f.toFiniteBilinearModule.isLagrangian_map_iff]

/-- A quadratic Lagrangian is quadratically isotropic. -/
theorem IsLagrangian.isIsotropic {H : AddSubgroup A} (hH : A.IsLagrangian H) :
    A.IsIsotropic H := hH.1

/-- A quadratic Lagrangian is Lagrangian for the polar bilinear pairing. -/
theorem IsLagrangian.toFiniteBilinearModule {H : AddSubgroup A} (hH : A.IsLagrangian H) :
    A.toFiniteBilinearModule.IsLagrangian H := hH.2

/-- A quadratic Lagrangian equals its orthogonal complement for the polar pairing. -/
theorem IsLagrangian.eq_orthogonalComplement {H : AddSubgroup A} (hH : A.IsLagrangian H) :
    H = A.toFiniteBilinearModule.orthogonalComplement H :=
  A.toFiniteBilinearModule.isLagrangian_def H |>.mp hH.2

end FiniteQuadraticModule

end TauCeti
