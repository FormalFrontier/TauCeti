/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Global-functions actions on sheaves of modules

This file constructs the canonical action of the ring of global functions on a sheaf of modules
on a scheme. It also records the restriction of this action to the base ring for a scheme over a
commutative ring.

These constructions are independent of sheaf cohomology. They supply the scalar actions used by
`TauCeti.AlgebraicGeometry.Cohomology.Module`.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- The restriction of a global function to an open subset. -/
private def restrictGlobal (U : X.Opens) (r : Γ(X, ⊤)) :
    X.ringCatSheaf.obj.obj (.op U) :=
  X.presheaf.map (homOfLE le_top).op r

/-- Multiplication by a global function, as a morphism of sheaves of modules. -/
def _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul
    (M : X.Modules) (r : Γ(X, ⊤)) : M ⟶ M where
  val.app U := by
    letI : CommRing (X.ringCatSheaf.obj.obj U) :=
      inferInstanceAs (CommRing (X.presheaf.obj U))
    exact ModuleCat.ofHom <|
      LinearMap.lsmul (X.ringCatSheaf.obj.obj U) (M.val.obj U) (restrictGlobal U.unop r)
  val.naturality {U V} f := by
    let : CommRing (X.ringCatSheaf.obj.obj U) :=
      inferInstanceAs (CommRing (X.presheaf.obj U))
    let : CommRing (X.ringCatSheaf.obj.obj V) :=
      inferInstanceAs (CommRing (X.presheaf.obj V))
    ext x
    dsimp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.lsmul_apply]
    rw [M.val.map_smul]
    -- The restriction-of-scalars wrapper is transparent but has no lemma exposing this
    -- pointwise goal, so normalize it to the presheaf action explicitly.
    change restrictGlobal V.unop r • M.val.map f x =
      X.ringCatSheaf.obj.map f (restrictGlobal U.unop r) • M.val.map f x
    congr 1
    change X.presheaf.map (homOfLE le_top).op r =
      X.presheaf.map f (X.presheaf.map (homOfLE le_top).op r)
    rw [← Functor.map_comp_apply]
    congr

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_app
    (M : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) :
    (globalSectionsSmul M r).app U = M.smul (X.presheaf.map U.leTop.op r) := by
  rfl

-- In the next four proofs, sheaf-morphism extensionality leaves pointwise bundled-module goals.
-- The wrappers have no pointwise equality lemmas, so each `change` records the corresponding
-- public presheaf/module formulation before applying the ring and module laws.
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_zero
    (M : X.Modules) : globalSectionsSmul M 0 = 0 := by
  ext U x
  change X.presheaf.map U.leTop.op 0 • x = 0
  simp

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_add
    (M : X.Modules) (r s : Γ(X, ⊤)) :
    globalSectionsSmul M (r + s) = globalSectionsSmul M r + globalSectionsSmul M s := by
  ext U x
  change X.presheaf.map U.leTop.op (r + s) • x =
    X.presheaf.map U.leTop.op r • x +
      X.presheaf.map U.leTop.op s • x
  simp [add_smul]

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_one
    (M : X.Modules) : globalSectionsSmul M 1 = 𝟙 M := by
  ext U x
  change X.presheaf.map U.leTop.op 1 • x = x
  simp

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_mul
    (M : X.Modules) (r s : Γ(X, ⊤)) :
    globalSectionsSmul M (r * s) = globalSectionsSmul M s ≫ globalSectionsSmul M r := by
  ext U x
  change X.presheaf.map U.leTop.op (r * s) • x =
    X.presheaf.map U.leTop.op r •
      X.presheaf.map U.leTop.op s • x
  rw [map_mul, mul_smul]

/-- The action of global functions on a sheaf of modules, bundled as a ring homomorphism into
the endomorphism ring of the sheaf. -/
def _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsAction
    (M : X.Modules) : Γ(X, ⊤) →+* End M where
  toFun := globalSectionsSmul M
  map_one' := globalSectionsSmul_one M
  map_mul' := fun r s ↦ by
    rw [globalSectionsSmul_mul]
    exact (End.mul_def _ _).symm
  map_zero' := globalSectionsSmul_zero M
  map_add' := globalSectionsSmul_add M

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsAction_apply
    (M : X.Modules) (r : Γ(X, ⊤)) :
    globalSectionsAction M r = globalSectionsSmul M r :=
  by rfl

/-- Multiplication by a global function is natural in the sheaf of modules. -/
@[reassoc]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_naturality
    (f : M ⟶ N) (r : Γ(X, ⊤)) :
    globalSectionsSmul M r ≫ f = f ≫ globalSectionsSmul N r := by
  ext U x
  -- As above, extensionality exposes the underlying bundled maps only definitionally.
  change f.app U (X.presheaf.map U.leTop.op r • x) =
    X.presheaf.map U.leTop.op r • f.app U x
  exact f.app_smul _ _

section Base

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The homomorphism from the base ring to global functions on a scheme over that ring. -/
def _root_.AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop).hom

/-- The base ring acts through the pullback along the structure morphism: `r` is sent to the
global function obtained by pulling back the function on `Spec R` corresponding to `r`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections_apply (r : R) :
    baseRingToGlobalSections R X r =
      (X ↘ Spec (.of R)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) :=
  (rfl)

/-- Global sections of a sheaf of modules on a scheme over a commutative ring form a module over
the base ring. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsBaseModule
    (M : X.Modules) : Module R Γ(M, ⊤) :=
  Module.compHom Γ(M, ⊤) (baseRingToGlobalSections R X)

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.base_smul_globalSections
    (M : X.Modules) (r : R) (x : Γ(M, ⊤)) :
    r • x = baseRingToGlobalSections R X r • x :=
  rfl

end Base

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
