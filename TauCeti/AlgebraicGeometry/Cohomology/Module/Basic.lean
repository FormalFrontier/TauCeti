/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections

/-!
# Scalar actions on the cohomology of a sheaf of modules on a scheme

This file equips the cohomology of a sheaf of modules on a scheme with its canonical module
structure over the ring of global functions. The construction first realizes a global function
as a scalar endomorphism of the coefficient sheaf, then applies the cohomology functor. No
coherence or quasi-coherence hypothesis is imposed on the coefficient sheaf.

The resulting action agrees in degree zero with the usual action on global sections, and every
map on cohomology induced by a morphism of coefficient sheaves is linear. For a scheme over a
base commutative ring, `TauCeti.AlgebraicGeometry.Cohomology.Module.Base` restricts these
actions along the induced map on global functions to actions of the base ring.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

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

/-- Scalar multiplication on cohomology is induced by the cohomology map of the corresponding
scalar endomorphism of the coefficient sheaf. -/
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

end Scheme.Modules

end


end AlgebraicGeometry

end TauCeti
