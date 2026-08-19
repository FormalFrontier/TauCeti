/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic

/-!
# The module structure on coherent cohomology

This file equips the cohomology of a sheaf of modules on a scheme with its canonical module
structure over the ring of global functions. The construction first realizes a global function
as a scalar endomorphism of the coefficient sheaf, then applies the cohomology functor.

The resulting action agrees in degree zero with the usual action on global sections, and every
map on cohomology induced by a morphism of coefficient sheaves is linear.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

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
def globalSectionsSmul (M : X.Modules) (r : Γ(X, ⊤)) : M ⟶ M where
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
    change restrictGlobal V.unop r • M.val.map f x =
      X.ringCatSheaf.obj.map f (restrictGlobal U.unop r) • M.val.map f x
    congr 1
    change X.presheaf.map (homOfLE le_top).op r =
      X.presheaf.map f (X.presheaf.map (homOfLE le_top).op r)
    rw [← Functor.map_comp_apply]
    congr

@[simp]
lemma globalSectionsSmul_app (M : X.Modules) (r : Γ(X, ⊤)) (U : X.Opens) :
    (globalSectionsSmul M r).app U = M.smul (X.presheaf.map U.leTop.op r) := by
  rfl

@[simp]
lemma globalSectionsSmul_zero (M : X.Modules) : globalSectionsSmul M 0 = 0 := by
  ext U x
  change X.presheaf.map U.leTop.op 0 • x = 0
  simp

@[simp]
lemma globalSectionsSmul_add (M : X.Modules) (r s : Γ(X, ⊤)) :
    globalSectionsSmul M (r + s) = globalSectionsSmul M r + globalSectionsSmul M s := by
  ext U x
  change X.presheaf.map U.leTop.op (r + s) • x =
    X.presheaf.map U.leTop.op r • x +
      X.presheaf.map U.leTop.op s • x
  simp [add_smul]

@[simp]
lemma globalSectionsSmul_one (M : X.Modules) : globalSectionsSmul M 1 = 𝟙 M := by
  ext U x
  change X.presheaf.map U.leTop.op 1 • x = x
  simp

@[simp]
lemma globalSectionsSmul_mul (M : X.Modules) (r s : Γ(X, ⊤)) :
    globalSectionsSmul M (r * s) = globalSectionsSmul M s ≫ globalSectionsSmul M r := by
  ext U x
  change X.presheaf.map U.leTop.op (r * s) • x =
    X.presheaf.map U.leTop.op r •
      X.presheaf.map U.leTop.op s • x
  rw [map_mul, mul_smul]

/-- The action of global functions on a sheaf of modules, bundled as a ring homomorphism into
the endomorphism ring of the sheaf. -/
def globalSectionsAction (M : X.Modules) : Γ(X, ⊤) →+* End M where
  toFun := globalSectionsSmul M
  map_one' := globalSectionsSmul_one M
  map_mul' := fun r s ↦ by
    rw [globalSectionsSmul_mul]
    exact (End.mul_def _ _).symm
  map_zero' := globalSectionsSmul_zero M
  map_add' := globalSectionsSmul_add M

@[simp]
lemma globalSectionsAction_apply (M : X.Modules) (r : Γ(X, ⊤)) :
    globalSectionsAction M r = globalSectionsSmul M r :=
  by rfl

@[reassoc]
lemma globalSectionsSmul_naturality (f : M ⟶ N) (r : Γ(X, ⊤)) :
    globalSectionsSmul M r ≫ f = f ≫ globalSectionsSmul N r := by
  ext U x
  change f.app U (X.presheaf.map U.leTop.op r • x) =
    X.presheaf.map U.leTop.op r • f.app U x
  exact f.app_smul _ _

/-- The action of global functions on cohomology, bundled as a ring homomorphism into additive
endomorphisms. -/
def cohomologyAction (M : X.Modules) (i : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (Cohomology M i) where
  toFun r := ((cohomologyFunctor X i).map (globalSectionsSmul M r)).hom
  map_one' := by
    ext x
    rw [globalSectionsSmul_one]
    exact ConcreteCategory.congr_hom ((cohomologyFunctor X i).map_id M) x
  map_mul' r s := by
    ext x
    rw [globalSectionsSmul_mul, Functor.map_comp]
    rfl
  map_zero' := by
    ext x
    rw [globalSectionsSmul_zero]
    exact ConcreteCategory.congr_hom (Functor.map_zero (cohomologyFunctor X i) M M) x
  map_add' r s := by
    ext x
    rw [globalSectionsSmul_add, Functor.map_add]
    rfl

/-- Cohomology is canonically a module over the ring of global functions. -/
instance cohomologyModule (M : X.Modules) (i : ℕ) : Module Γ(X, ⊤) (Cohomology M i) :=
  Module.compHom (Cohomology M i) (cohomologyAction M i)

@[simp]
lemma cohomology_smul (M : X.Modules) (i : ℕ) (r : Γ(X, ⊤)) (x : Cohomology M i) :
    r • x = (cohomologyFunctor X i).map (globalSectionsSmul M r) x :=
  by
    change cohomologyAction M i r x = _
    rfl

/-- The map on cohomology induced by a morphism of coefficient sheaves is linear over global
functions. -/
def cohomologyMapLinear (f : M ⟶ N) (i : ℕ) :
    Cohomology M i →ₗ[Γ(X, ⊤)] Cohomology N i where
  toFun := (cohomologyFunctor X i).map f
  map_add' := map_add _
  map_smul' r x := by
    change CategoryTheory.Sheaf.H.map
        ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f) i
          (CategoryTheory.Sheaf.H.map
            ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
              (globalSectionsSmul M r)) i x) =
      CategoryTheory.Sheaf.H.map
        ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
          (globalSectionsSmul N r)) i
          (CategoryTheory.Sheaf.H.map
            ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f) i x)
    rw [← CategoryTheory.Sheaf.H.map_comp_apply,
      ← CategoryTheory.Sheaf.H.map_comp_apply]
    congr 2
    exact congrArg (fun g ↦ (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map g)
      (globalSectionsSmul_naturality f r)

@[simp]
lemma cohomologyMapLinear_apply (f : M ⟶ N) (i : ℕ) (x : Cohomology M i) :
    cohomologyMapLinear f i x = (cohomologyFunctor X i).map f x :=
  by
    change (cohomologyFunctor X i).map f x = _
    rfl

/-- The canonical identification of zeroth cohomology with global sections is linear over global
functions. -/
def cohomologyZeroLinearEquiv (M : X.Modules) :
    Cohomology M 0 ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) where
  __ := cohomologyZeroEquiv M
  map_smul' r x := by
    change cohomologyZeroEquiv M
        ((cohomologyFunctor X 0).map (globalSectionsSmul M r) x) =
      r • cohomologyZeroEquiv M x
    rw [cohomologyZeroEquiv_naturality]
    rw [globalSectionsSmul_app]
    have h : X.presheaf.map (⊤ : X.Opens).leTop.op r = r := by
      have hf : (⊤ : X.Opens).leTop.op = 𝟙 (Opposite.op (⊤ : X.Opens)) :=
        Subsingleton.elim _ _
      rw [hf]
      exact ConcreteCategory.congr_hom (X.presheaf.map_id _) r
    rw [h]
    exact M.smul_apply r (cohomologyZeroEquiv M x)

@[simp]
lemma cohomologyZeroLinearEquiv_apply (M : X.Modules) (x : Cohomology M 0) :
    cohomologyZeroLinearEquiv M x = cohomologyZeroEquiv M x :=
  by
    change cohomologyZeroEquiv M x = _
    rfl

section Base

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The homomorphism from the base ring to global functions on a scheme over that ring. -/
def baseRingToGlobalSections : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop).hom

/-- Cohomology of a scheme over a commutative ring is a module over the base ring. -/
instance cohomologyBaseModule (M : X.Modules) (i : ℕ) : Module R (Cohomology M i) :=
  Module.compHom (Cohomology M i) (baseRingToGlobalSections R X)

/-- Global sections of a sheaf of modules on a scheme over a commutative ring form a module over
the base ring. -/
instance globalSectionsBaseModule (M : X.Modules) : Module R Γ(M, ⊤) :=
  Module.compHom Γ(M, ⊤) (baseRingToGlobalSections R X)

@[simp]
lemma base_smul_cohomology (M : X.Modules) (i : ℕ) (r : R) (x : Cohomology M i) :
    r • x = (baseRingToGlobalSections R X r) • x :=
  rfl

@[simp]
lemma base_smul_globalSections (M : X.Modules) (r : R) (x : Γ(M, ⊤)) :
    r • x = baseRingToGlobalSections R X r • x :=
  rfl

/-- For a scheme over a commutative ring, the canonical identification of zeroth cohomology with
global sections is linear over the base ring. -/
def cohomologyZeroBaseLinearEquiv (M : X.Modules) :
    Cohomology M 0 ≃ₗ[R] Γ(M, ⊤) where
  __ := cohomologyZeroEquiv M
  map_smul' r x := (cohomologyZeroLinearEquiv M).map_smul
    (baseRingToGlobalSections R X r) x

@[simp]
lemma cohomologyZeroBaseLinearEquiv_apply (M : X.Modules) (x : Cohomology M 0) :
    cohomologyZeroBaseLinearEquiv R X M x = cohomologyZeroEquiv M x := by
  change cohomologyZeroEquiv M x = _
  rfl

end Base

end Scheme.Modules

end


end AlgebraicGeometry

end TauCeti
