/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Module.Basic

/-!
# Base-ring actions on the cohomology of a sheaf of modules on a scheme

For a scheme over a base commutative ring, restricting the global-functions actions of
`TauCeti.AlgebraicGeometry.Cohomology.Module.Basic` along the induced map on global functions gives
the corresponding actions of the base ring: the module structure on cohomology, the linearity
of the maps induced by morphisms of coefficient sheaves, and the degree-zero identification
with global sections.

The base-ring statements live in their own file, rather than alongside the global-functions
ones, to keep each file's kernel-checking time inside the CI per-file budget: every declaration
here re-checks the full `CategoryTheory.Sheaf.H` instance terms, which is expensive.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
variable {M N : X.Modules}

/-- Cohomology of a scheme over a commutative ring is a module over the base ring. As for
`globalSectionsBaseModule`, the priority is below the default so that `cohomologyModule`, the
canonical action of `Γ(X, ⊤)`, is still the one found when the base ring is the ring of global
functions itself. -/
instance (priority := 900) _root_.AlgebraicGeometry.Scheme.Modules.cohomologyBaseModule
    (M : X.Modules) (i : ℕ) : Module R (Cohomology M i) :=
  Module.compHom (Cohomology M i) (baseRingToGlobalSections R X)

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.base_smul_cohomology
    (M : X.Modules) (i : ℕ) (r : R) (x : Cohomology M i) :
    r • x = (baseRingToGlobalSections R X r) • x :=
  rfl

/-- The map on cohomology induced by a morphism of coefficient sheaves on a scheme over a
commutative ring is linear over the base ring. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapBaseLinear
    (f : M ⟶ N) (i : ℕ) :
    Cohomology M i →ₗ[R] Cohomology N i where
  toFun := (cohomologyFunctor X i).map f
  map_add' := map_add _
  map_smul' r x := by
    simp only [base_smul_cohomology, RingHom.id_apply, ← cohomologyMapLinear_apply]
    exact (cohomologyMapLinear f i).map_smul (baseRingToGlobalSections R X r) x

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapBaseLinear_apply
    (f : M ⟶ N) (i : ℕ) (x : Cohomology M i) :
    cohomologyMapBaseLinear R X f i x = (cohomologyFunctor X i).map f x :=
  by rfl

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapBaseLinear_id
    (M : X.Modules) (i : ℕ) :
    cohomologyMapBaseLinear R X (𝟙 M) i = LinearMap.id := by
  apply LinearMap.ext
  exact (cohomologyFunctor X i).map_id_apply M

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapBaseLinear_comp
    {P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (i : ℕ) :
    cohomologyMapBaseLinear R X (f ≫ g) i =
      (cohomologyMapBaseLinear R X g i).comp (cohomologyMapBaseLinear R X f i) := by
  apply LinearMap.ext
  exact (cohomologyFunctor X i).map_comp_apply f g

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapBaseLinear_zero
    (M N : X.Modules) (i : ℕ) :
    cohomologyMapBaseLinear R X (0 : M ⟶ N) i = 0 := by
  apply LinearMap.ext
  intro x
  simp only [cohomologyMapBaseLinear_apply, LinearMap.zero_apply]
  rw [Functor.map_zero]
  rfl

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyMapBaseLinear_add
    (f g : M ⟶ N) (i : ℕ) :
    cohomologyMapBaseLinear R X (f + g) i =
      cohomologyMapBaseLinear R X f i + cohomologyMapBaseLinear R X g i := by
  apply LinearMap.ext
  intro x
  simp only [cohomologyMapBaseLinear_apply, LinearMap.add_apply]
  rw [Functor.map_add]
  rfl

/-- For a scheme over a commutative ring, the canonical identification of zeroth cohomology with
global sections is linear over the base ring. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyZeroBaseLinearEquiv
    (M : X.Modules) :
    Cohomology M 0 ≃ₗ[R] Γ(M, ⊤) where
  __ := (cohomologyZeroLinearEquiv M).toAddEquiv
  map_smul' r x := by
    simp only [base_smul_cohomology, base_smul_globalSections, RingHom.id_apply]
    exact (cohomologyZeroLinearEquiv M).map_smul (baseRingToGlobalSections R X r) x

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyZeroBaseLinearEquiv_apply
    (M : X.Modules) (x : Cohomology M 0) :
    cohomologyZeroBaseLinearEquiv R X M x = cohomologyZeroEquiv M x := by
  exact cohomologyZeroLinearEquiv_apply M x

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
