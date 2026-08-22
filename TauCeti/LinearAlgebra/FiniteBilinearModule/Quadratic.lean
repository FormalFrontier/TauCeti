/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.OrthogonalComplement
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
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
* `TauCeti.FiniteQuadraticModule.orthogonalQuotient`: the quadratic module induced on
  `H^⊥ / H` by a quadratic-isotropic subgroup `H`.

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

/-! ## Quotients by isotropic subgroups -/

/-- A quadratic-isotropic subgroup contained in the radical of the polar pairing lies in the
radical of the quadratic map. This is the exact condition needed to descend the quadratic map to
the quotient. -/
theorem IsIsotropic.toIntSubmodule_le_quadraticRadical {K : AddSubgroup A}
    (hK : A.IsIsotropic K) (hKrad : K ≤ A.toFiniteBilinearModule.radical) :
    K.toIntSubmodule ≤ A.quadratic.radical := by
  intro x hx
  refine ⟨hK x hx, ?_⟩
  ext y
  rw [QuadraticMap.polarBilin_apply_apply, A.polar_eq_pairing, LinearMap.zero_apply]
  exact A.toFiniteBilinearModule.mem_radical_iff x |>.mp (hKrad hx) y

/-- A subgroup contained in the radical of the quadratic map is quadratic-isotropic. -/
theorem isIsotropic_of_toIntSubmodule_le_quadraticRadical {K : AddSubgroup A}
    (hK : K.toIntSubmodule ≤ A.quadratic.radical) : A.IsIsotropic K :=
  fun _ hx ↦ (hK hx).1

/-- A subgroup contained in the radical of the quadratic map is contained in the radical of the
polar pairing. -/
theorem le_radical_of_toIntSubmodule_le_quadraticRadical {K : AddSubgroup A}
    (hK : K.toIntSubmodule ≤ A.quadratic.radical) :
    K ≤ A.toFiniteBilinearModule.radical := by
  intro x hx
  rw [A.toFiniteBilinearModule.mem_radical_iff]
  intro y
  rw [← A.polar_eq_pairing, ← QuadraticMap.polarBilin_apply_apply, (hK hx).2,
    LinearMap.zero_apply]

/-- The finite quadratic module obtained by quotienting by a subgroup contained in the radical of
the quadratic map. That radical consists of the isotropic elements of the radical of the polar
pairing, so this is exactly the condition making the quadratic map descend.

The underlying bilinear module is the corresponding quotient of the polar pairing, while the
quadratic map is Mathlib's `QuadraticMap.lift`.

Exposed for the same reason as `FiniteBilinearModule.quotientOfLeRadical`: so that its carrier
reduces to the `Submodule` quotient and maps out of it are definable. -/
@[expose] noncomputable def quotientOfLeQuadraticRadical (K : AddSubgroup A)
    (hK : K.toIntSubmodule ≤ A.quadratic.radical) :
    FiniteQuadraticModule where
  toFiniteBilinearModule := A.toFiniteBilinearModule.quotientOfLeRadical K
    (A.le_radical_of_toIntSubmodule_le_quadraticRadical hK)
  quadratic := A.quadratic.lift K.toIntSubmodule hK
  polar_eq_pairing' x y := by
    unfold FiniteBilinearModule.quotientOfLeRadical
    induction x using Submodule.Quotient.induction_on with | H x =>
    induction y using Submodule.Quotient.induction_on with | H y =>
    -- Expose the two quotient lifts; their public representative lemmas then determine both sides.
    change (A.quadratic.lift K.toIntSubmodule hK)
          (Submodule.Quotient.mk x + Submodule.Quotient.mk y) -
        A.quadratic x - A.quadratic y =
      A.toFiniteBilinearModule.quotientOfLeRadicalBilin K
          (A.le_radical_of_toIntSubmodule_le_quadraticRadical hK)
        (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)
    rw [← Submodule.Quotient.mk_add, QuadraticMap.lift_mk,
      A.toFiniteBilinearModule.quotientOfLeRadicalBilin_mk]
    exact A.polar_eq_pairing x y

/-- The quotient map onto a quadratic quotient by a subgroup of the quadratic radical. -/
noncomputable def quotientOfLeQuadraticRadicalMk (K : AddSubgroup A)
    (hK : K.toIntSubmodule ≤ A.quadratic.radical) :
    A →+ A.quotientOfLeQuadraticRadical K hK :=
  K.toIntSubmodule.mkQ.toAddMonoidHom

/-- The quotient quadratic map is represented by the original quadratic map. -/
@[simp]
theorem quotientOfLeQuadraticRadical_quadratic_mk (K : AddSubgroup A)
    (hK : K.toIntSubmodule ≤ A.quadratic.radical) (x : A) :
    (A.quotientOfLeQuadraticRadical K hK).quadratic
      (A.quotientOfLeQuadraticRadicalMk K hK x) = A.quadratic x := by
  exact QuadraticMap.lift_mk hK x

/-- The quotient polar pairing is represented by the original pairing. -/
@[simp]
theorem quotientOfLeQuadraticRadical_pairing_mk (K : AddSubgroup A)
    (hK : K.toIntSubmodule ≤ A.quadratic.radical) (x y : A) :
    (A.quotientOfLeQuadraticRadical K hK).toFiniteBilinearModule.pairing
      (A.quotientOfLeQuadraticRadicalMk K hK x)
      (A.quotientOfLeQuadraticRadicalMk K hK y) =
        A.toFiniteBilinearModule.pairing x y := by
  -- The quotient pairing *is* the descended polar pairing; unfold the opaque `CharacterModule`
  -- alias so that its representative lemma applies.
  change A.toFiniteBilinearModule.quotientOfLeRadicalBilin K
      (A.le_radical_of_toIntSubmodule_le_quadraticRadical hK)
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = _
  exact A.toFiniteBilinearModule.quotientOfLeRadicalBilin_mk K
    (A.le_radical_of_toIntSubmodule_le_quadraticRadical hK) x y

/-- The quotient map onto a quadratic quotient is surjective. -/
theorem quotientOfLeQuadraticRadicalMk_surjective (K : AddSubgroup A)
    (hK : K.toIntSubmodule ≤ A.quadratic.radical) :
    Function.Surjective (A.quotientOfLeQuadraticRadicalMk K hK) :=
  K.toIntSubmodule.mkQ_surjective

/-- Every element of a quadratic quotient is the class of a representative. -/
@[elab_as_elim]
theorem quotientOfLeQuadraticRadical_induction_on (K : AddSubgroup A)
    (hK : K.toIntSubmodule ≤ A.quadratic.radical)
    {motive : A.quotientOfLeQuadraticRadical K hK → Prop}
    (q : A.quotientOfLeQuadraticRadical K hK)
    (mk : ∀ x : A, motive (A.quotientOfLeQuadraticRadicalMk K hK x)) : motive q := by
  obtain ⟨x, rfl⟩ := A.quotientOfLeQuadraticRadicalMk_surjective K hK q
  exact mk x

/-- A representative has zero class in a quadratic quotient exactly when it belongs to the
subgroup being divided out. -/
@[simp]
theorem quotientOfLeQuadraticRadicalMk_eq_zero_iff (K : AddSubgroup A)
    (hK : K.toIntSubmodule ≤ A.quadratic.radical) (x : A) :
    A.quotientOfLeQuadraticRadicalMk K hK x = 0 ↔ x ∈ K := by
  -- Expose the canonical quotient map to apply Mathlib's zero-class criterion.
  change Submodule.Quotient.mk x = 0 ↔ x ∈ K.toIntSubmodule
  exact Submodule.Quotient.mk_eq_zero K.toIntSubmodule

/-- Two representatives have the same class in a quadratic quotient exactly when they differ by an
element of the subgroup being divided out. -/
@[simp]
theorem quotientOfLeQuadraticRadicalMk_eq_iff (K : AddSubgroup A)
    (hK : K.toIntSubmodule ≤ A.quadratic.radical) (x y : A) :
    A.quotientOfLeQuadraticRadicalMk K hK x =
      A.quotientOfLeQuadraticRadicalMk K hK y ↔ x - y ∈ K := by
  rw [← sub_eq_zero, ← map_sub, A.quotientOfLeQuadraticRadicalMk_eq_zero_iff K hK]

/-- Taking the polar bilinear module commutes with quotienting by a subgroup of the quadratic
radical. -/
@[simp]
theorem quotientOfLeQuadraticRadical_toFiniteBilinearModule (K : AddSubgroup A)
    (hK : K.toIntSubmodule ≤ A.quadratic.radical) :
    (A.quotientOfLeQuadraticRadical K hK).toFiniteBilinearModule =
      A.toFiniteBilinearModule.quotientOfLeRadical K
        (A.le_radical_of_toIntSubmodule_le_quadraticRadical hK) := by
  rfl

/-- The quadratic quotient is nondegenerate exactly when the subgroup contains the radical of the
polar pairing. -/
theorem isNondegenerate_quotientOfLeQuadraticRadical_iff (K : AddSubgroup A)
    (hK : K.toIntSubmodule ≤ A.quadratic.radical) :
    (A.quotientOfLeQuadraticRadical K hK).IsNondegenerate ↔
      A.toFiniteBilinearModule.radical ≤ K := by
  exact A.toFiniteBilinearModule.isNondegenerate_quotientOfLeRadical_iff K
    (A.le_radical_of_toIntSubmodule_le_quadraticRadical hK)

/-- The order of a quadratic quotient is the index of the subgroup being divided out. -/
theorem card_quotientOfLeQuadraticRadical (K : AddSubgroup A)
    (hK : K.toIntSubmodule ≤ A.quadratic.radical) :
    Nat.card (A.quotientOfLeQuadraticRadical K hK) = K.index := by
  exact A.toFiniteBilinearModule.card_quotientOfLeRadical K
    (A.le_radical_of_toIntSubmodule_le_quadraticRadical hK)

/-! ### The induced quadratic form on `H^⊥ / H` -/

/-- The elements of `H` lying in `H^⊥`, viewed as a subgroup of `H^⊥`. When `H ≤ H^⊥`, this
intersection is a copy of all of `H`. -/
def subgroupInOrthogonalComplement (H : AddSubgroup A) :
    AddSubgroup (A.toFiniteBilinearModule.orthogonalComplement H) :=
  H.addSubgroupOf (A.toFiniteBilinearModule.orthogonalComplement H)

/-- Membership in `H ∩ H^⊥`, viewed inside `H^⊥`, is membership of the underlying element in
`H`. -/
@[simp]
theorem mem_subgroupInOrthogonalComplement_iff (H : AddSubgroup A)
    (x : A.toFiniteBilinearModule.orthogonalComplement H) :
    x ∈ A.subgroupInOrthogonalComplement H ↔ (x : A) ∈ H :=
  Iff.rfl

/-- If `H ≤ H^⊥`, its copy inside `H^⊥` is additively equivalent to `H`. -/
def subgroupInOrthogonalComplementEquiv {H : AddSubgroup A}
    (hH : H ≤ A.toFiniteBilinearModule.orthogonalComplement H) :
    A.subgroupInOrthogonalComplement H ≃+ H :=
  AddSubgroup.addSubgroupOfEquivOfLe hH

/-- The copy of a quadratic-isotropic subgroup in its orthogonal complement remains
quadratic-isotropic for the restricted form. -/
theorem isIsotropic_subgroupInOrthogonalComplement {H : AddSubgroup A}
    (hH : A.IsIsotropic H) :
    (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H)).IsIsotropic
      (A.subgroupInOrthogonalComplement H) := by
  intro x hx
  exact hH x.1 (A.mem_subgroupInOrthogonalComplement_iff H x |>.mp hx)

/-- The elements of `H` lying in `H^⊥` belong to the radical of the pairing restricted to
`H^⊥`. -/
theorem subgroupInOrthogonalComplement_le_radical {H : AddSubgroup A}
    : A.subgroupInOrthogonalComplement H ≤
      FiniteBilinearModule.radical
        (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H)).toFiniteBilinearModule := by
  intro x hx
  apply FiniteBilinearModule.mem_radical_iff
    (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H)).toFiniteBilinearModule x |>.mpr
  intro y
  -- The restricted pairing has the same values on the underlying subtype.
  change A.toFiniteBilinearModule.pairing x.1 y.1 = 0
  rw [A.toFiniteBilinearModule.pairing_comm]
  exact A.toFiniteBilinearModule.mem_orthogonalComplement_iff H y.1 |>.mp y.2 x.1
    (A.mem_subgroupInOrthogonalComplement_iff H x |>.mp hx)

/-- The copy of a quadratic-isotropic subgroup in its orthogonal complement lies in the radical of
the quadratic map restricted to that complement. -/
theorem subgroupInOrthogonalComplement_le_quadraticRadical {H : AddSubgroup A}
    (hH : A.IsIsotropic H) :
    (A.subgroupInOrthogonalComplement H).toIntSubmodule ≤
      (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H)).quadratic.radical :=
  IsIsotropic.toIntSubmodule_le_quadraticRadical _
    (A.isIsotropic_subgroupInOrthogonalComplement hH)
    A.subgroupInOrthogonalComplement_le_radical

/-- The finite quadratic module induced on `H^⊥ / H` by a quadratic-isotropic subgroup `H`.

The form is first restricted to `H^⊥`; the copy of `H` there lies in the radical of the restricted
quadratic map, so the restricted form descends to the quotient.

Exposed for the same reason as `quotientOfLeQuadraticRadical`: so that its carrier reduces to the
`Submodule` quotient and maps out of it are definable. -/
@[expose] noncomputable def orthogonalQuotient (H : AddSubgroup A) (hH : A.IsIsotropic H) :
    FiniteQuadraticModule :=
  (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H)).quotientOfLeQuadraticRadical
    (A.subgroupInOrthogonalComplement H)
    (A.subgroupInOrthogonalComplement_le_quadraticRadical hH)

/-- The quotient map from `H^⊥` onto its induced quadratic quotient. -/
noncomputable def orthogonalQuotientMk (H : AddSubgroup A) (hH : A.IsIsotropic H) :
    A.toFiniteBilinearModule.orthogonalComplement H →+
      A.orthogonalQuotient H hH :=
  quotientOfLeQuadraticRadicalMk
    (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H))
    (A.subgroupInOrthogonalComplement H)
    (A.subgroupInOrthogonalComplement_le_quadraticRadical hH)

/-- The quadratic form on `H^⊥ / H` is represented by the original quadratic form. -/
@[simp]
theorem orthogonalQuotient_quadratic_mk (H : AddSubgroup A) (hH : A.IsIsotropic H)
    (x : A.toFiniteBilinearModule.orthogonalComplement H) :
    (A.orthogonalQuotient H hH).quadratic (A.orthogonalQuotientMk H hH x) =
      A.quadratic x.1 :=
  quotientOfLeQuadraticRadical_quadratic_mk
    (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H))
    (A.subgroupInOrthogonalComplement H)
    (A.subgroupInOrthogonalComplement_le_quadraticRadical hH) x

/-- The pairing on `H^⊥ / H` is represented by the original polar pairing. -/
@[simp]
theorem orthogonalQuotient_pairing_mk (H : AddSubgroup A) (hH : A.IsIsotropic H)
    (x y : A.toFiniteBilinearModule.orthogonalComplement H) :
    (A.orthogonalQuotient H hH).toFiniteBilinearModule.pairing
      (A.orthogonalQuotientMk H hH x) (A.orthogonalQuotientMk H hH y) =
      A.toFiniteBilinearModule.pairing x.1 y.1 :=
  quotientOfLeQuadraticRadical_pairing_mk
    (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H))
    (A.subgroupInOrthogonalComplement H)
    (A.subgroupInOrthogonalComplement_le_quadraticRadical hH) x y

/-- The quotient map from `H^⊥` is surjective. -/
theorem orthogonalQuotientMk_surjective (H : AddSubgroup A) (hH : A.IsIsotropic H) :
    Function.Surjective (A.orthogonalQuotientMk H hH) :=
  quotientOfLeQuadraticRadicalMk_surjective
    (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H))
    (A.subgroupInOrthogonalComplement H)
    (A.subgroupInOrthogonalComplement_le_quadraticRadical hH)

/-- Every element of `H^⊥ / H` is the class of an element of `H^⊥`. -/
@[elab_as_elim]
theorem orthogonalQuotient_induction_on (H : AddSubgroup A) (hH : A.IsIsotropic H)
    {motive : A.orthogonalQuotient H hH → Prop} (q : A.orthogonalQuotient H hH)
    (mk : ∀ x : A.toFiniteBilinearModule.orthogonalComplement H,
      motive (A.orthogonalQuotientMk H hH x)) : motive q := by
  obtain ⟨x, rfl⟩ := A.orthogonalQuotientMk_surjective H hH q
  exact mk x

/-- An element of `H^⊥` has zero class in `H^⊥ / H` exactly when it lies in `H`. -/
@[simp]
theorem orthogonalQuotientMk_eq_zero_iff (H : AddSubgroup A) (hH : A.IsIsotropic H)
    (x : A.toFiniteBilinearModule.orthogonalComplement H) :
    A.orthogonalQuotientMk H hH x = 0 ↔ (x : A) ∈ H :=
  quotientOfLeQuadraticRadicalMk_eq_zero_iff
    (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H))
    (A.subgroupInOrthogonalComplement H)
    (A.subgroupInOrthogonalComplement_le_quadraticRadical hH) x

/-- Two elements of `H^⊥` have the same class in `H^⊥ / H` exactly when they differ by an element
of `H`. -/
@[simp]
theorem orthogonalQuotientMk_eq_iff (H : AddSubgroup A) (hH : A.IsIsotropic H)
    (x y : A.toFiniteBilinearModule.orthogonalComplement H) :
    A.orthogonalQuotientMk H hH x = A.orthogonalQuotientMk H hH y ↔ (x : A) - y ∈ H :=
  quotientOfLeQuadraticRadicalMk_eq_iff
    (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H))
    (A.subgroupInOrthogonalComplement H)
    (A.subgroupInOrthogonalComplement_le_quadraticRadical hH) x y

/-- If `A` is nondegenerate, the quadratic module induced on `H^⊥ / H` is nondegenerate. -/
theorem IsNondegenerate.isNondegenerate_orthogonalQuotient (hA : A.IsNondegenerate)
    {H : AddSubgroup A} (hH : A.IsIsotropic H) :
    (A.orthogonalQuotient H hH).IsNondegenerate := by
  apply (isNondegenerate_quotientOfLeQuadraticRadical_iff
    (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H))
    (A.subgroupInOrthogonalComplement H)
    (A.subgroupInOrthogonalComplement_le_quadraticRadical hH)).mpr
  intro x hx
  have hx' : (x.1 : A) ∈ A.toFiniteBilinearModule.orthogonalComplement
      (A.toFiniteBilinearModule.orthogonalComplement H) := by
    rw [A.toFiniteBilinearModule.mem_orthogonalComplement_iff]
    intro y hy
    exact FiniteBilinearModule.mem_radical_iff
      (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H)).toFiniteBilinearModule x
      |>.mp hx ⟨y, hy⟩
  have hdouble := FiniteBilinearModule.IsNondegenerate.orthogonalComplement_orthogonalComplement
    A.toFiniteBilinearModule hA H
  rw [hdouble] at hx'
  exact hx'

/-- For nondegenerate `A`, the order of `H^⊥ / H` multiplied by `|H|²` is `|A|`. -/
theorem IsNondegenerate.card_orthogonalQuotient_mul_card_sq (hA : A.IsNondegenerate)
    {H : AddSubgroup A} (hH : A.IsIsotropic H) :
    Nat.card (A.orthogonalQuotient H hH) * Nat.card H ^ 2 = Nat.card A := by
  have hcard : Nat.card (A.subgroupInOrthogonalComplement H) = Nat.card H :=
    Nat.card_congr (A.subgroupInOrthogonalComplementEquiv hH.le_orthogonalComplement).toEquiv
  have hindex : Nat.card (A.orthogonalQuotient H hH) =
      (A.subgroupInOrthogonalComplement H).index := by
    unfold orthogonalQuotient
    exact card_quotientOfLeQuadraticRadical
      (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H))
      (A.subgroupInOrthogonalComplement H)
      (A.subgroupInOrthogonalComplement_le_quadraticRadical hH)
  have hquot : Nat.card (A.orthogonalQuotient H hH) * Nat.card H =
      Nat.card (A.toFiniteBilinearModule.orthogonalComplement H) := by
    calc
      Nat.card (A.orthogonalQuotient H hH) * Nat.card H =
          (A.subgroupInOrthogonalComplement H).index * Nat.card H := by
            rw [hindex]
      _ = (A.subgroupInOrthogonalComplement H).index *
          Nat.card (A.subgroupInOrthogonalComplement H) := congrArg _ hcard.symm
      _ = Nat.card (A.toFiniteBilinearModule.orthogonalComplement H) :=
        (A.subgroupInOrthogonalComplement H).index_mul_card
  rw [pow_two, ← mul_assoc, hquot, mul_comm]
  exact FiniteBilinearModule.IsNondegenerate.card_mul_card_orthogonalComplement
    A.toFiniteBilinearModule hA H

end FiniteQuadraticModule

end TauCeti
