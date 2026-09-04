/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Orthogonal.Quotient
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.QuadraticForm.Prod

/-!
# Finite quadratic modules

A finite quadratic module is a finite abelian group equipped with a quadratic map to `ℚ/ℤ`.
Its symmetric bilinear pairing is not stored separately: it is the polar form of the quadratic
map.  This file packages that canonical underlying finite bilinear module and develops restriction,
form negation, orthogonal products, morphisms, isometries, quadratic-isotropic subgroups, and
quadratic Lagrangians.

The convention is the half-norm convention used for discriminant forms: for an even integral
lattice the quadratic value of a dual class represented by `x` is `B(x, x) / 2` modulo `ℤ`, and
the polar pairing is therefore `B(x, y)` modulo `ℤ`.

## Main definitions

* `QuadraticMap.liftOfSurjective`: descent of a quadratic map along a surjection whose
  kernel lies in the radical.
* `TauCeti.FiniteQuadraticModule`: a finite abelian group with an `AddCircle (1 : ℚ)`-valued
  quadratic map.
* `TauCeti.FiniteQuadraticModule.ofQuadraticMap`: the finite quadratic module presented by a
  quadratic map on a finite abelian group.
* `TauCeti.FiniteQuadraticModule.toFiniteBilinearModule`: the canonical polar bilinear module.
* `TauCeti.FiniteQuadraticModule.Hom`: a quadratic-map-preserving additive homomorphism.
* `TauCeti.FiniteQuadraticModule.Isometry`: a quadratic-map isometric equivalence.
* `TauCeti.FiniteQuadraticModule.IsIsotropic`: quadratic isotropy of an additive subgroup.
* `TauCeti.FiniteQuadraticModule.IsLagrangian`: a quadratic-isotropic subgroup equal to its
  bilinear orthogonal complement.
* `TauCeti.FiniteQuadraticModule.orthogonalQuotient`: the quadratic module induced on
  `H^⊥ / H` by a quadratic-isotropic subgroup `H`.  Its underlying bilinear module is
  `TauCeti.FiniteBilinearModule.orthogonalQuotient`, as recorded by
  `TauCeti.FiniteQuadraticModule.orthogonalQuotient_toFiniteBilinearModule`.
* `TauCeti.FiniteQuadraticModule.orthogonalQuotientCongr`: the canonical isometry between the
  orthogonal quotients along equal subgroups.
* `TauCeti.FiniteQuadraticModule.Isometry.orthogonalQuotientEquiv`: transport of an orthogonal
  quotient along an isometry carrying one isotropic subgroup onto another.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* W. Ebeling, *Lattices and Codes*, Chapter 1.

This is the finite-quadratic-module part of Layer 3 of
`TauCetiRoadmap/IntegralLattices/README.md`.
-/

public section

universe u v

/-! ## Descent of a quadratic map along a surjection -/

namespace QuadraticMap

variable {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

/-- Descend a quadratic map along a surjective linear map whose kernel lies in its radical.

Mathlib's `QuadraticMap.lift` descends along the quotient by a submodule of the radical.  A
quotient is usually presented instead by a surjection onto a concrete group — reduction modulo `m`
onto `ZMod m`, say — and this is that formulation. -/
noncomputable def liftOfSurjective (Q : QuadraticMap R M P) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (h : LinearMap.ker f ≤ Q.radical) : QuadraticMap R N P :=
  (Q.lift (LinearMap.ker f) h).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap

/-- The descended quadratic map takes the original value on every representative. -/
@[simp]
theorem liftOfSurjective_apply (Q : QuadraticMap R M P) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (h : LinearMap.ker f ≤ Q.radical) (x : M) :
    liftOfSurjective Q f hf h (f x) = Q x := by
  rw [liftOfSurjective, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, QuadraticMap.lift_mk]

end QuadraticMap

namespace TauCeti

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

/-- **The finite quadratic module presented by a quadratic map** on a finite abelian group.  The
pairing is the polar form, which is what the structure demands anyway, so no data beyond the
quadratic map is needed.

Exposed for the same reason as `quotientOfLeQuadraticRadical`: so that its carrier reduces to the
given group and maps into or out of it are definable. -/
@[expose] def ofQuadraticMap {C : Type u} [AddCommGroup C] [Finite C]
    (q : QuadraticMap ℤ C (AddCircle (1 : ℚ))) : FiniteQuadraticModule where
  toFiniteBilinearModule := {
    carrier := C
    pairing := LinearMap.toAddMonoidHom'.comp q.polarBilin.toAddMonoidHom
    pairing_comm := fun x y ↦ QuadraticMap.polar_comm q x y }
  quadratic := q
  polar_eq_pairing' := fun _ _ ↦ (rfl)

@[simp]
theorem ofQuadraticMap_quadratic {C : Type u} [AddCommGroup C] [Finite C]
    (q : QuadraticMap ℤ C (AddCircle (1 : ℚ))) (x : C) :
    (ofQuadraticMap q).quadratic x = q x := (rfl)

@[simp]
theorem ofQuadraticMap_pairing {C : Type u} [AddCommGroup C] [Finite C]
    (q : QuadraticMap ℤ C (AddCircle (1 : ℚ))) (x y : C) :
    (ofQuadraticMap q).toFiniteBilinearModule.pairing x y = QuadraticMap.polar q x y := (rfl)

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

/-! ## Morphisms and isometries -/

/-- A morphism of finite quadratic modules is an additive homomorphism preserving the quadratic
map.

This is Mathlib's `QuadraticMap.Isometry` applied to the stored quadratic maps. -/
abbrev Hom (A : FiniteQuadraticModule.{u}) (B : FiniteQuadraticModule.{v}) : Type (max u v) :=
  A.quadratic.Isometry B.quadratic

namespace Hom

variable {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}
  {C : FiniteQuadraticModule}

/-- The identity morphism of a finite quadratic module. -/
def id (A : FiniteQuadraticModule) : Hom A A :=
  QuadraticMap.Isometry.id A.quadratic

/-- The composite of two finite quadratic module morphisms. -/
def comp (g : Hom B C) (f : Hom A B) : Hom A C :=
  QuadraticMap.Isometry.comp g f

/-- Two finite quadratic module morphisms are equal when they agree on every element. -/
@[ext]
theorem ext {f g : Hom A B} (h : ∀ x, f x = g x) : f = g :=
  QuadraticMap.Isometry.ext h

@[simp]
theorem id_apply (A : FiniteQuadraticModule) (x : A) : id A x = x :=
  (rfl)

@[simp]
theorem comp_apply (g : Hom B C) (f : Hom A B) (x : A) : g.comp f x = g (f x) :=
  (rfl)

@[simp]
theorem id_comp (f : Hom A B) : (id B).comp f = f :=
  QuadraticMap.Isometry.id_comp f

@[simp]
theorem comp_id (f : Hom A B) : f.comp (id A) = f :=
  QuadraticMap.Isometry.comp_id f

@[simp]
theorem comp_assoc {D : FiniteQuadraticModule} (h : Hom C D) (g : Hom B C) (f : Hom A B) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  QuadraticMap.Isometry.comp_assoc h g f

/-- A morphism of finite quadratic modules preserves the canonical polar pairing. -/
@[simp]
theorem map_pairing (f : Hom A B) (x y : A) :
    B.toFiniteBilinearModule.pairing (f x) (f y) =
      A.toFiniteBilinearModule.pairing x y := by
  rw [← B.polar_eq_pairing, ← A.polar_eq_pairing]
  simp only [QuadraticMap.polar]
  rw [← map_add f, f.map_app, f.map_app, f.map_app]

/-- A quadratic-module morphism induces a morphism of the canonical polar bilinear modules. -/
def toFiniteBilinearModule (f : Hom A B) :
    FiniteBilinearModule.Hom A.toFiniteBilinearModule B.toFiniteBilinearModule where
  toAddMonoidHom := f.toLinearMap.toAddMonoidHom
  map_pairing' := f.map_pairing

@[simp]
theorem toFiniteBilinearModule_apply (f : Hom A B) (x : A) :
    f.toFiniteBilinearModule x = f x := (rfl)

/-- Forgetting the identity quadratic morphism gives the identity bilinear morphism. -/
@[simp]
theorem toFiniteBilinearModule_id (A : FiniteQuadraticModule) :
    (id A).toFiniteBilinearModule = FiniteBilinearModule.Hom.id A.toFiniteBilinearModule := by
  ext x
  rw [toFiniteBilinearModule_apply, id_apply, FiniteBilinearModule.Hom.id_apply]

/-- Forgetting a composite quadratic morphism gives the composite bilinear morphism. -/
@[simp]
theorem toFiniteBilinearModule_comp (g : Hom B C) (f : Hom A B) :
    (g.comp f).toFiniteBilinearModule =
      g.toFiniteBilinearModule.comp f.toFiniteBilinearModule := by
  ext x
  rw [toFiniteBilinearModule_apply, comp_apply, FiniteBilinearModule.Hom.comp_apply,
    toFiniteBilinearModule_apply, toFiniteBilinearModule_apply]

/-- A morphism out of a nondegenerate finite quadratic module is injective. -/
theorem injective (f : Hom A B) (hA : A.IsNondegenerate) : Function.Injective f :=
  fun _ _ hxy ↦ f.toFiniteBilinearModule.injective hA hxy

end Hom

/-- An isometry of finite quadratic modules is Mathlib's isometric equivalence of their quadratic
maps. -/
abbrev Isometry (A : FiniteQuadraticModule.{u}) (B : FiniteQuadraticModule.{v}) : Type (max u v) :=
  A.quadratic.IsometryEquiv B.quadratic

namespace Isometry

variable {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}

/-- Applying a composite quadratic isometry applies its two factors in order. -/
@[simp]
theorem trans_apply {C : FiniteQuadraticModule} (f : Isometry A B) (g : Isometry B C) (x : A) :
    (f.trans g) x = g (f x) :=
  rfl

/-- A quadratic isometry is, after forgetting bijectivity, a morphism. -/
def toHom (f : Isometry A B) : Hom A B :=
  f.toIsometry

@[simp]
theorem toHom_apply (f : Isometry A B) (x : A) : f.toHom x = f x := (rfl)

/-- Forgetting the identity quadratic isometry gives the identity quadratic morphism. -/
@[simp]
theorem refl_toHom (A : FiniteQuadraticModule) :
    toHom (QuadraticMap.IsometryEquiv.refl A.quadratic) = Hom.id A := by
  ext
  rfl

/-- Forgetting a composite quadratic isometry gives the composite quadratic morphism. -/
@[simp]
theorem trans_toHom {C : FiniteQuadraticModule} (f : Isometry A B) (g : Isometry B C) :
    toHom (f.trans g) = g.toHom.comp f.toHom := by
  ext
  rfl

/-- The underlying morphism of a quadratic isometry is bijective. -/
theorem toHom_bijective (f : Isometry A B) : Function.Bijective f.toHom := by
  simpa only [Function.Bijective, Function.Injective, Function.Surjective, toHom_apply,
    QuadraticMap.IsometryEquiv.coe_toLinearEquiv] using f.toLinearEquiv.bijective

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

namespace Hom

variable {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}

/-- A bijective morphism of finite quadratic modules is an isometry. -/
noncomputable def toIsometry (f : Hom A B) (hf : Function.Bijective f) : Isometry A B where
  toLinearEquiv := (AddEquiv.ofBijective f.toLinearMap.toAddMonoidHom hf).toIntLinearEquiv
  map_app' := f.map_app

@[simp]
theorem toIsometry_apply (f : Hom A B) (hf : Function.Bijective f) (x : A) :
    f.toIsometry hf x = f x := (rfl)

/-- Forgetting a bijective morphism after packaging it as an isometry recovers the morphism. -/
@[simp]
theorem toIsometry_toHom (f : Hom A B) (hf : Function.Bijective f) :
    (f.toIsometry hf).toHom = f := by
  ext
  rfl

/-- Packaging the underlying morphism of an isometry recovers the isometry. -/
@[simp]
theorem toHom_toIsometry (f : Isometry A B) :
    f.toHom.toIsometry f.toHom_bijective = f := by
  exact DFunLike.ext _ _ fun _ ↦ rfl

end Hom

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

/-- The inclusion of a restricted finite quadratic module into the original module. -/
def restrictHom (H : AddSubgroup A) : Hom (restrict A H) A where
  toLinearMap := H.toIntSubmodule.subtype
  map_app' _ := rfl

@[simp]
theorem restrictHom_apply (H : AddSubgroup A) (x : H) : A.restrictHom H x = x := (rfl)

/-- Forgetting the quadratic structure of a restriction inclusion gives the bilinear restriction
inclusion. -/
@[simp]
theorem restrictHom_toFiniteBilinearModule (H : AddSubgroup A) :
    (A.restrictHom H).toFiniteBilinearModule = A.toFiniteBilinearModule.restrictHom H := by
  ext x
  calc
    (A.restrictHom H).toFiniteBilinearModule x = A.restrictHom H x :=
      Hom.toFiniteBilinearModule_apply _ _
    _ = x.1 := restrictHom_apply A H x
    _ = A.toFiniteBilinearModule.restrictHom H x :=
      (FiniteBilinearModule.restrictHom_apply _ H x).symm

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

/-- The copy of a quadratic-isotropic subgroup in its orthogonal complement remains
quadratic-isotropic for the restricted form. -/
theorem isIsotropic_subgroupInOrthogonalComplement {H : AddSubgroup A}
    (hH : A.IsIsotropic H) :
    (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H)).IsIsotropic
      (A.subgroupInOrthogonalComplement H) := by
  intro x hx
  exact hH x.1 (A.mem_subgroupInOrthogonalComplement_iff H x |>.mp hx)

/-- The copy of a quadratic-isotropic subgroup in its orthogonal complement lies in the radical of
the quadratic map restricted to that complement. -/
theorem subgroupInOrthogonalComplement_le_quadraticRadical {H : AddSubgroup A}
    (hH : A.IsIsotropic H) :
    (A.subgroupInOrthogonalComplement H).toIntSubmodule ≤
      (A.restrict (A.toFiniteBilinearModule.orthogonalComplement H)).quadratic.radical :=
  IsIsotropic.toIntSubmodule_le_quadraticRadical _
    (A.isIsotropic_subgroupInOrthogonalComplement hH)
    (A.toFiniteBilinearModule.addSubgroupOf_orthogonalComplement_le_radical_restrict H)

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

/-- **The underlying bilinear module of a quadratic orthogonal quotient** is the bilinear
orthogonal quotient.  Both are the restriction of the form to `H^⊥` divided by the copy of `H`
inside it, so the two constructions agree. -/
@[simp]
theorem orthogonalQuotient_toFiniteBilinearModule (H : AddSubgroup A) (hH : A.IsIsotropic H) :
    (A.orthogonalQuotient H hH).toFiniteBilinearModule =
      A.toFiniteBilinearModule.orthogonalQuotient H := (rfl)

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

/-- Equal quadratic-isotropic subgroups induce the same orthogonal quotient, up to the canonical
isometry. -/
noncomputable def orthogonalQuotientCongr {H K : AddSubgroup A} (hH : A.IsIsotropic H)
    (hK : A.IsIsotropic K) (h : H = K) :
    Isometry (A.orthogonalQuotient H hH) (A.orthogonalQuotient K hK) := by
  subst h
  exact QuadraticMap.IsometryEquiv.refl _

/-- The canonical isometry between the orthogonal quotients along equal subgroups is the identity
on representatives. -/
@[simp]
theorem orthogonalQuotientCongr_orthogonalQuotientMk {H K : AddSubgroup A} (hH : A.IsIsotropic H)
    (hK : A.IsIsotropic K) (h : H = K)
    (x : A.toFiniteBilinearModule.orthogonalComplement H) :
    A.orthogonalQuotientCongr hH hK h (A.orthogonalQuotientMk H hH x) =
      A.orthogonalQuotientMk K hK ⟨x.1, h ▸ x.2⟩ := by
  subst h
  rfl

/-- If `A` is nondegenerate, the quadratic module induced on `H^⊥ / H` is nondegenerate. -/
theorem IsNondegenerate.isNondegenerate_orthogonalQuotient (hA : A.IsNondegenerate)
    {H : AddSubgroup A} (hH : A.IsIsotropic H) :
    (A.orthogonalQuotient H hH).IsNondegenerate := by
  rw [FiniteQuadraticModule.IsNondegenerate, A.orthogonalQuotient_toFiniteBilinearModule H hH]
  exact FiniteBilinearModule.IsNondegenerate.isNondegenerate_orthogonalQuotient
    A.toFiniteBilinearModule hA H

/-- For nondegenerate `A`, the order of `H^⊥ / H` multiplied by `|H|²` is `|A|`. -/
theorem IsNondegenerate.card_orthogonalQuotient_mul_card_sq (hA : A.IsNondegenerate)
    {H : AddSubgroup A} (hH : A.IsIsotropic H) :
    Nat.card (A.orthogonalQuotient H hH) * Nat.card H ^ 2 = Nat.card A := by
  simpa only [A.orthogonalQuotient_toFiniteBilinearModule H hH] using
    (FiniteBilinearModule.IsNondegenerate.card_orthogonalQuotient_mul_card_sq
      A.toFiniteBilinearModule hA hH.toFiniteBilinearModule)

/-! ### Transport of an orthogonal quotient along an isometry -/

namespace Isometry

universe w

variable {A : FiniteQuadraticModule.{u}} {B : FiniteQuadraticModule.{v}}

/-- A quadratic isometry carrying `H` onto `K` transports quadratic isotropy from `H` to `K`. -/
theorem isIsotropic_of_map_eq (f : Isometry A B) {H : AddSubgroup A} {K : AddSubgroup B}
    (hH : A.IsIsotropic H) (h : H.map f.toAddEquiv = K) : B.IsIsotropic K := by
  rw [← h, f.isIsotropic_map_iff]
  exact hH

/-- The additive equivalence from a quadratic orthogonal quotient to its underlying bilinear
orthogonal quotient. -/
private noncomputable def orthogonalQuotientUnderlyingEquiv (A : FiniteQuadraticModule.{w})
    (H : AddSubgroup A) (hH : A.IsIsotropic H) :
    A.orthogonalQuotient H hH ≃+ A.toFiniteBilinearModule.orthogonalQuotient H := by
  unfold FiniteQuadraticModule.orthogonalQuotient
  unfold subgroupInOrthogonalComplement quotientOfLeQuadraticRadical
  unfold FiniteBilinearModule.orthogonalQuotient
  exact AddEquiv.refl _

@[simp]
private theorem orthogonalQuotientUnderlyingEquiv_orthogonalQuotientMk
    (A : FiniteQuadraticModule.{w}) (H : AddSubgroup A) (hH : A.IsIsotropic H)
    (x : A.toFiniteBilinearModule.orthogonalComplement H) :
    orthogonalQuotientUnderlyingEquiv A H hH (A.orthogonalQuotientMk H hH x) =
      A.toFiniteBilinearModule.orthogonalQuotientMk H x := by
  unfold orthogonalQuotientUnderlyingEquiv FiniteQuadraticModule.orthogonalQuotientMk
  unfold subgroupInOrthogonalComplement quotientOfLeQuadraticRadicalMk
  rw [A.toFiniteBilinearModule.orthogonalQuotientMk_apply]
  exact Submodule.mkQ_apply _ _

/-- The bilinear transport induced by a quadratic isometry. -/
private noncomputable def orthogonalQuotientBilinearMapAddEquiv (f : Isometry A B)
    (H : AddSubgroup A) :
    A.toFiniteBilinearModule.orthogonalQuotient H ≃+
      B.toFiniteBilinearModule.orthogonalQuotient (H.map f.toAddEquiv) :=
  ((FiniteBilinearModule.Isometry.orthogonalQuotientEquiv
      (H := H) f.toFiniteBilinearModule rfl).trans
    (B.toFiniteBilinearModule.orthogonalQuotientCongr
      (by rw [f.toFiniteBilinearModule_toAddEquiv]))).toAddEquiv

@[simp]
private theorem orthogonalQuotientBilinearMapAddEquiv_orthogonalQuotientMk
    (f : Isometry A B) (H : AddSubgroup A)
    (x : A.toFiniteBilinearModule.orthogonalComplement H) :
    orthogonalQuotientBilinearMapAddEquiv f H
        (A.toFiniteBilinearModule.orthogonalQuotientMk H x) =
      B.toFiniteBilinearModule.orthogonalQuotientMk (H.map f.toAddEquiv)
        ⟨f (x : A), FiniteBilinearModule.Isometry.map_mem_orthogonalComplement_of_map_eq
          A.toFiniteBilinearModule f.toFiniteBilinearModule
          (by rw [f.toFiniteBilinearModule_toAddEquiv]) x.2⟩ := by
  rw [orthogonalQuotientBilinearMapAddEquiv]
  -- The definition ends by forgetting a bilinear isometry to its additive equivalence; normalize
  -- that coercion so the two public representative formulas apply.
  change ((FiniteBilinearModule.Isometry.orthogonalQuotientEquiv
      (H := H) f.toFiniteBilinearModule rfl).trans
      (B.toFiniteBilinearModule.orthogonalQuotientCongr
        (by rw [f.toFiniteBilinearModule_toAddEquiv])))
      (A.toFiniteBilinearModule.orthogonalQuotientMk H x) = _
  rw [
    FiniteBilinearModule.Isometry.trans_apply,
    FiniteBilinearModule.Isometry.orthogonalQuotientEquiv_orthogonalQuotientMk,
    B.toFiniteBilinearModule.orthogonalQuotientCongr_orthogonalQuotientMk]
  apply congrArg (B.toFiniteBilinearModule.orthogonalQuotientMk (H.map f.toAddEquiv))
  exact Subtype.ext (congrArg (fun e : A ≃+ B => e (x : A))
    f.toFiniteBilinearModule_toAddEquiv)

/-- The bilinear transport, viewed on the underlying groups of the quadratic quotients. -/
private noncomputable def orthogonalQuotientMapAddEquiv (f : Isometry A B)
    (H : AddSubgroup A) (hH : A.IsIsotropic H)
    (hK : B.IsIsotropic (H.map f.toAddEquiv)) :
    A.orthogonalQuotient H hH ≃+
      B.orthogonalQuotient (H.map f.toAddEquiv) hK := by
  let eA : A.orthogonalQuotient H hH ≃+
      A.toFiniteBilinearModule.orthogonalQuotient H :=
    orthogonalQuotientUnderlyingEquiv A H hH
  let e : A.toFiniteBilinearModule.orthogonalQuotient H ≃+
      B.toFiniteBilinearModule.orthogonalQuotient (H.map f.toAddEquiv) :=
    orthogonalQuotientBilinearMapAddEquiv f H
  let eB : B.toFiniteBilinearModule.orthogonalQuotient (H.map f.toAddEquiv) ≃+
      B.orthogonalQuotient (H.map f.toAddEquiv) hK := by
    unfold FiniteQuadraticModule.orthogonalQuotient
    unfold subgroupInOrthogonalComplement quotientOfLeQuadraticRadical
    unfold FiniteBilinearModule.orthogonalQuotient
    exact AddEquiv.refl _
  exact (eA.trans e).trans eB

@[simp]
private theorem orthogonalQuotientMapAddEquiv_orthogonalQuotientMk (f : Isometry A B)
    (H : AddSubgroup A) (hH : A.IsIsotropic H)
    (hK : B.IsIsotropic (H.map f.toAddEquiv))
    (x : A.toFiniteBilinearModule.orthogonalComplement H) :
    orthogonalQuotientMapAddEquiv f H hH hK (A.orthogonalQuotientMk H hH x) =
      B.orthogonalQuotientMk (H.map f.toAddEquiv) hK
        ⟨f (x : A), FiniteBilinearModule.Isometry.map_mem_orthogonalComplement_of_map_eq
          A.toFiniteBilinearModule f.toFiniteBilinearModule
          (by rw [f.toFiniteBilinearModule_toAddEquiv]) x.2⟩ := by
  rw [orthogonalQuotientMapAddEquiv, AddEquiv.trans_apply, AddEquiv.trans_apply,
    orthogonalQuotientUnderlyingEquiv_orthogonalQuotientMk,
    orthogonalQuotientBilinearMapAddEquiv_orthogonalQuotientMk]
  unfold FiniteQuadraticModule.orthogonalQuotientMk
  unfold subgroupInOrthogonalComplement quotientOfLeQuadraticRadicalMk
  rw [B.toFiniteBilinearModule.orthogonalQuotientMk_apply]
  exact (Submodule.mkQ_apply _ _).symm

/-- The isometry of orthogonal quotients when the target subgroup is exactly the image. -/
private noncomputable def orthogonalQuotientMap (f : Isometry A B) (H : AddSubgroup A)
    (hH : A.IsIsotropic H) :
    Isometry (A.orthogonalQuotient H hH)
      (B.orthogonalQuotient (H.map f.toAddEquiv) ((f.isIsotropic_map_iff (H := H)).mpr hH)) where
  toLinearEquiv := (orthogonalQuotientMapAddEquiv f H hH
    ((f.isIsotropic_map_iff (H := H)).mpr hH)).toIntLinearEquiv
  map_app' q := by
    induction q using orthogonalQuotient_induction_on with
    | mk x =>
      -- Normalize the reflexive coercion from an additive equivalence to its `ℤ`-linear form.
      change (B.orthogonalQuotient (H.map f.toAddEquiv) _).quadratic
          (orthogonalQuotientMapAddEquiv f H hH _ (A.orthogonalQuotientMk H hH x)) =
        (A.orthogonalQuotient H hH).quadratic (A.orthogonalQuotientMk H hH x)
      rw [orthogonalQuotientMapAddEquiv_orthogonalQuotientMk,
        B.orthogonalQuotient_quadratic_mk, A.orthogonalQuotient_quadratic_mk]
      exact f.map_app (x : A)

/-- The image-subgroup transport sends the class of `x ∈ H⊥` to the class of `f x`. -/
@[simp]
private theorem orthogonalQuotientMap_orthogonalQuotientMk (f : Isometry A B)
    (H : AddSubgroup A) (hH : A.IsIsotropic H)
    (x : A.toFiniteBilinearModule.orthogonalComplement H) :
    f.orthogonalQuotientMap H hH (A.orthogonalQuotientMk H hH x) =
      B.orthogonalQuotientMk (H.map f.toAddEquiv) ((f.isIsotropic_map_iff (H := H)).mpr hH)
        ⟨f (x : A), FiniteBilinearModule.Isometry.map_mem_orthogonalComplement_of_map_eq
          A.toFiniteBilinearModule f.toFiniteBilinearModule
          (by rw [f.toFiniteBilinearModule_toAddEquiv]) x.2⟩ :=
  by
    rw [orthogonalQuotientMap]
    -- Normalize the reflexive coercion from the additive equivalence used by the structure field.
    change orthogonalQuotientMapAddEquiv f H hH _ (A.orthogonalQuotientMk H hH x) = _
    exact orthogonalQuotientMapAddEquiv_orthogonalQuotientMk f H hH _ x

/-- **Transport of an orthogonal quotient along an isometry.** An isometry `f : A ≅ B` of finite
quadratic modules carrying a quadratic-isotropic subgroup `H` of `A` onto `K` induces an isometry
`H⊥ / H ≅ K⊥ / K`. -/
noncomputable def orthogonalQuotientEquiv (f : Isometry A B) {H : AddSubgroup A}
    {K : AddSubgroup B} (hH : A.IsIsotropic H) (h : H.map f.toAddEquiv = K) :
    Isometry (A.orthogonalQuotient H hH)
      (B.orthogonalQuotient K (f.isIsotropic_of_map_eq hH h)) :=
  (f.orthogonalQuotientMap H hH).trans
    (B.orthogonalQuotientCongr ((f.isIsotropic_map_iff (H := H)).mpr hH)
      (f.isIsotropic_of_map_eq hH h) h)

/-- **The representative formula for a transported orthogonal quotient.** The transported
isometry sends the class of `x ∈ H⊥` to the class of `f x ∈ K⊥`. -/
@[simp]
theorem orthogonalQuotientEquiv_orthogonalQuotientMk (f : Isometry A B)
    {H : AddSubgroup A} {K : AddSubgroup B} (hH : A.IsIsotropic H)
    (h : H.map f.toAddEquiv = K)
    (x : A.toFiniteBilinearModule.orthogonalComplement H) :
    f.orthogonalQuotientEquiv hH h (A.orthogonalQuotientMk H hH x) =
      B.orthogonalQuotientMk K (f.isIsotropic_of_map_eq hH h)
        ⟨f (x : A), by
          apply FiniteBilinearModule.Isometry.map_mem_orthogonalComplement_of_map_eq
            A.toFiniteBilinearModule f.toFiniteBilinearModule (K := K) (x := (x : A))
          · simpa only [toFiniteBilinearModule_toAddEquiv] using h
          · exact x.2⟩ := by
  rw [orthogonalQuotientEquiv, trans_apply, orthogonalQuotientMap_orthogonalQuotientMk,
    B.orthogonalQuotientCongr_orthogonalQuotientMk]

/-- **The inverse representative formula for a transported orthogonal quotient.** The inverse
transport sends the class of `y ∈ K⊥` to the class of `f.symm y ∈ H⊥`. -/
@[simp]
theorem orthogonalQuotientEquiv_symm_orthogonalQuotientMk (f : Isometry A B)
    {H : AddSubgroup A} {K : AddSubgroup B} (hH : A.IsIsotropic H)
    (h : H.map f.toAddEquiv = K)
    (y : B.toFiniteBilinearModule.orthogonalComplement K) :
    (f.orthogonalQuotientEquiv hH h).symm
        (B.orthogonalQuotientMk K (f.isIsotropic_of_map_eq hH h) y) =
      A.orthogonalQuotientMk H hH
        ⟨f.symm (y : B), by
          apply (AddSubgroup.mem_map_equiv (f := f.toAddEquiv) (K :=
            A.toFiniteBilinearModule.orthogonalComplement H) (x := (y : B))).mp
          have hcomp :
              (A.toFiniteBilinearModule.orthogonalComplement H).map f.toAddEquiv =
                B.toFiniteBilinearModule.orthogonalComplement (H.map f.toAddEquiv) := by
            simpa only [toFiniteBilinearModule_toAddEquiv] using
              f.toFiniteBilinearModule.map_orthogonalComplement (H := H)
          -- `mem_map_equiv` leaves the additive equivalence coerced through its monoid hom;
          -- normalize that coercion before rewriting with the subgroup equality.
          change (y : B) ∈
            (A.toFiniteBilinearModule.orthogonalComplement H).map f.toAddEquiv
          rw [hcomp, h]
          exact y.2⟩ := by
  refine (Equiv.symm_apply_eq
    (f.orthogonalQuotientEquiv hH h).toLinearEquiv.toEquiv).mpr ?_
  -- `Equiv.symm_apply_eq` exposes the `toEquiv` coercion; normalize it to the isometry coercion
  -- so the public forward representative formula applies.
  change B.orthogonalQuotientMk K (f.isIsotropic_of_map_eq hH h) y =
    f.orthogonalQuotientEquiv hH h
      (A.orthogonalQuotientMk H hH ⟨f.symm (y : B), _⟩)
  rw [orthogonalQuotientEquiv_orthogonalQuotientMk]
  congr 1
  exact Subtype.ext (f.apply_symm_apply (y : B)).symm

end Isometry

end FiniteQuadraticModule

end TauCeti
