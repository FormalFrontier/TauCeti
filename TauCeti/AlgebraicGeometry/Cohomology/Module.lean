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

@[reassoc]
lemma _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsSmul_naturality
    (f : M ⟶ N) (r : Γ(X, ⊤)) :
    globalSectionsSmul M r ≫ f = f ≫ globalSectionsSmul N r := by
  ext U x
  -- As above, extensionality exposes the underlying bundled maps only definitionally.
  change f.app U (X.presheaf.map U.leTop.op r • x) =
    X.presheaf.map U.leTop.op r • f.app U x
  exact f.app_smul _ _

/-- The action of global functions on cohomology, bundled as a ring homomorphism into additive
endomorphisms. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyAction
    (M : X.Modules) (i : ℕ) :
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

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyAction_apply
    (M : X.Modules) (i : ℕ) (r : Γ(X, ⊤)) (x : Cohomology M i) :
    cohomologyAction M i r x =
      (cohomologyFunctor X i).map (globalSectionsSmul M r) x := by
  simp only [cohomologyAction]
  exact DFunLike.congr_fun (AddCommGrpCat.homAddEquiv_apply
    ((cohomologyFunctor X i).map (globalSectionsSmul M r))) x

/-- Cohomology is canonically a module over the ring of global functions. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.cohomologyModule
    (M : X.Modules) (i : ℕ) : Module Γ(X, ⊤) (Cohomology M i) :=
  Module.compHom (Cohomology M i) (cohomologyAction M i)

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomology_smul
    (M : X.Modules) (i : ℕ) (r : Γ(X, ⊤)) (x : Cohomology M i) :
    r • x = (cohomologyFunctor X i).map (globalSectionsSmul M r) x :=
  by
    -- `Module.compHom` exposes its action definitionally, without an accessor lemma.
    change cohomologyAction M i r x = _
    rfl

/-- The map on cohomology induced by a morphism of coefficient sheaves is linear over global
functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapLinear
    (f : M ⟶ N) (i : ℕ) :
    Cohomology M i →ₗ[Γ(X, ⊤)] Cohomology N i where
  toFun := (cohomologyFunctor X i).map f
  map_add' := map_add _
  map_smul' r x := by
    -- Normalize only the scalar action supplied by `Module.compHom`; keep cohomology
    -- abstract so functoriality, rather than `Sheaf.H` implementation details, proves it.
    change (cohomologyFunctor X i).map f
        ((cohomologyFunctor X i).map (globalSectionsSmul M r) x) =
      (cohomologyFunctor X i).map (globalSectionsSmul N r)
        ((cohomologyFunctor X i).map f x)
    erw [← (cohomologyFunctor X i).map_comp_apply,
      ← (cohomologyFunctor X i).map_comp_apply, globalSectionsSmul_naturality]

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapLinear_apply
    (f : M ⟶ N) (i : ℕ) (x : Cohomology M i) :
    cohomologyMapLinear f i x = (cohomologyFunctor X i).map f x :=
  by rfl

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapLinear_id
    (M : X.Modules) (i : ℕ) :
    cohomologyMapLinear (𝟙 M) i = LinearMap.id := by
  apply LinearMap.ext
  exact (cohomologyFunctor X i).map_id_apply M

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapLinear_comp
    {P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (i : ℕ) :
    cohomologyMapLinear (f ≫ g) i =
      (cohomologyMapLinear g i).comp (cohomologyMapLinear f i) := by
  apply LinearMap.ext
  exact (cohomologyFunctor X i).map_comp_apply f g

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapLinear_zero
    (M N : X.Modules) (i : ℕ) :
    cohomologyMapLinear (0 : M ⟶ N) i = 0 := by
  apply LinearMap.ext
  intro x
  simp only [cohomologyMapLinear_apply, LinearMap.zero_apply]
  rw [Functor.map_zero]
  rfl

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapLinear_add
    (f g : M ⟶ N) (i : ℕ) :
    cohomologyMapLinear (f + g) i = cohomologyMapLinear f i + cohomologyMapLinear g i := by
  apply LinearMap.ext
  intro x
  simp only [cohomologyMapLinear_apply, LinearMap.add_apply]
  rw [Functor.map_add]
  rfl

/-- The canonical identification of zeroth cohomology with global sections is linear over global
functions. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyZeroLinearEquiv
    (M : X.Modules) :
    Cohomology M 0 ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) where
  __ := cohomologyZeroEquiv M
  map_smul' r x := by
    -- The inherited linear-equivalence fields have no accessor lemmas for their actions;
    -- normalize them to the named cohomology and section operations.
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
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyZeroLinearEquiv_apply
    (M : X.Modules) (x : Cohomology M 0) :
    cohomologyZeroLinearEquiv M x = cohomologyZeroEquiv M x :=
  by rfl

section Base

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The homomorphism from the base ring to global functions on a scheme over that ring. -/
def _root_.AlgebraicGeometry.Scheme.Modules.baseRingToGlobalSections : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ (X ↘ Spec (.of R)).appTop).hom

/-- Cohomology of a scheme over a commutative ring is a module over the base ring. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.cohomologyBaseModule
    (M : X.Modules) (i : ℕ) : Module R (Cohomology M i) :=
  Module.compHom (Cohomology M i) (baseRingToGlobalSections R X)

/-- Global sections of a sheaf of modules on a scheme over a commutative ring form a module over
the base ring. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.globalSectionsBaseModule
    (M : X.Modules) : Module R Γ(M, ⊤) :=
  Module.compHom Γ(M, ⊤) (baseRingToGlobalSections R X)

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.base_smul_cohomology
    (M : X.Modules) (i : ℕ) (r : R) (x : Cohomology M i) :
    r • x = (baseRingToGlobalSections R X r) • x :=
  rfl

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.base_smul_globalSections
    (M : X.Modules) (r : R) (x : Γ(M, ⊤)) :
    r • x = baseRingToGlobalSections R X r • x :=
  rfl

/-- For a scheme over a commutative ring, the canonical identification of zeroth cohomology with
global sections is linear over the base ring. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyZeroBaseLinearEquiv
    (M : X.Modules) :
    Cohomology M 0 ≃ₗ[R] Γ(M, ⊤) where
  __ := cohomologyZeroEquiv M
  map_smul' r x := (cohomologyZeroLinearEquiv M).map_smul
    (baseRingToGlobalSections R X r) x

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyZeroBaseLinearEquiv_apply
    (M : X.Modules) (x : Cohomology M 0) :
    cohomologyZeroBaseLinearEquiv R X M x = cohomologyZeroEquiv M x := by
  rfl

end Base

end Scheme.Modules

end


end AlgebraicGeometry

end TauCeti
