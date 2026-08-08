/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Cohomology of sheaves of modules on a scheme

Mathlib defines the cohomology `CategoryTheory.Sheaf.H` of an abelian sheaf on a site as an
`Ext` group from the constant sheaf `ℤ`. This file applies that construction to the underlying
abelian sheaf of an `𝒪_X`-module and packages the result in the scheme-module API.

For a scheme `X` and `M : X.Modules`, the main declarations are:

* `Scheme.Modules.cohomology M i`, the group `Hⁱ(X, M)`;
* `Scheme.Modules.cohomologyMap f i`, the map on cohomology induced by a morphism of
  `𝒪_X`-modules;
* `Scheme.Modules.cohomologyFunctor X i`, functoriality in the coefficient sheaf;
* `Scheme.Modules.cohomologyEquivOfIso e i`, invariance under an isomorphism of coefficient
  sheaves;
* `Scheme.Modules.cohomologyZeroEquiv`, the canonical equivalence
  `H⁰(X, M) ≃+ Γ(X, M)` with global sections.

The construction is stated for every sheaf of modules, which is the natural generality of sheaf
cohomology. In particular it applies to finitely presented sheaves through their underlying
objects, and hence supplies the `Hⁱ(X, ℱ)` used for coherent sheaves in
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer B. Finite-dimensionality for proper schemes,
vanishing on curves, and the comparison with Čech cohomology remain later Layer B work.

No formalization is vendored. The definitions reuse Mathlib's `Sheaf.H`, `Sheaf.H.map`,
`Sheaf.functorH`, and `Sheaf.H.equiv₀`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- The `i`th cohomology group `Hⁱ(X, M)` of a sheaf of modules on a scheme.

This is sheaf cohomology on the small Zariski site of `X`, obtained by forgetting the
`𝒪_X`-module structure and applying Mathlib's `CategoryTheory.Sheaf.H`. -/
abbrev cohomology (M : X.Modules) (i : ℕ) : Type u :=
  CategoryTheory.Sheaf.H.{u}
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) i

/-- A morphism of sheaves of modules induces an additive map on cohomology. -/
def cohomologyMap {M N : X.Modules} (f : M ⟶ N) (i : ℕ) :
    cohomology M i →+ cohomology N i :=
  CategoryTheory.Sheaf.H.map
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f) i

/-- The identity morphism induces the identity on cohomology. -/
@[simp]
lemma cohomologyMap_id_apply (M : X.Modules) (i : ℕ) (x : cohomology M i) :
    cohomologyMap (𝟙 M) i x = x := by
  exact CategoryTheory.Sheaf.H.map_id_apply x

/-- The map induced by a composite is the composite of the induced cohomology maps. -/
@[simp]
lemma cohomologyMap_comp_apply {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P)
    (i : ℕ) (x : cohomology M i) :
    cohomologyMap (f ≫ g) i x = cohomologyMap g i (cohomologyMap f i x) := by
  exact CategoryTheory.Sheaf.H.map_comp_apply
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f)
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map g) x

/-- Cohomology maps preserve addition of morphisms in the coefficient sheaf. -/
@[simp]
lemma cohomologyMap_add_apply {M N : X.Modules} (f g : M ⟶ N) (i : ℕ)
    (x : cohomology M i) :
    cohomologyMap (f + g) i x = cohomologyMap f i x + cohomologyMap g i x := by
  exact CategoryTheory.Sheaf.H.map_add_apply
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f)
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map g) x

/-- Degree-`i` cohomology as an additive functor from sheaves of modules to abelian groups. -/
abbrev cohomologyFunctor (X : Scheme.{u}) (i : ℕ) : X.Modules ⥤ AddCommGrpCat.{u} :=
  _root_.SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.functorH.{u} _ i

/-- Degreewise cohomology is additive. This is Mathlib's instance for a composite of additive
functors; it has to be restated because inference does not see through the `X.Modules` type
synonym. -/
instance (X : Scheme.{u}) (i : ℕ) : (cohomologyFunctor X i).Additive :=
  inferInstanceAs ((_root_.SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.functorH.{u} _ i).Additive)

/-- The zero morphism induces the zero map on cohomology. -/
@[simp]
lemma cohomologyMap_zero_apply (M N : X.Modules) (i : ℕ) (x : cohomology M i) :
    cohomologyMap (0 : M ⟶ N) i x = 0 := by
  rw [show cohomologyMap (0 : M ⟶ N) i =
    ((cohomologyFunctor X i).map (0 : M ⟶ N)).hom from rfl,
    (cohomologyFunctor X i).map_zero]
  rfl

/-- Isomorphic sheaves of modules have canonically additively equivalent cohomology groups. -/
def cohomologyEquivOfIso {M N : X.Modules} (e : M ≅ N) (i : ℕ) :
    cohomology M i ≃+ cohomology N i :=
  ((cohomologyFunctor X i).mapIso e).addCommGroupIsoToAddEquiv

/-- The forward map of `cohomologyEquivOfIso` is the cohomology map induced by the forward
morphism. -/
@[simp]
lemma cohomologyEquivOfIso_apply {M N : X.Modules} (e : M ≅ N) (i : ℕ)
    (x : cohomology M i) :
    cohomologyEquivOfIso e i x = cohomologyMap e.hom i x := by
  rw [show cohomologyMap e.hom i = ((cohomologyFunctor X i).map e.hom).hom from rfl,
    ← Functor.mapIso_hom]
  exact ((cohomologyFunctor X i).mapIso e).addCommGroupIsoToAddEquiv_apply x

/-- The inverse of `cohomologyEquivOfIso` is the cohomology map induced by the inverse
morphism. -/
@[simp]
lemma cohomologyEquivOfIso_symm_apply {M N : X.Modules} (e : M ≅ N) (i : ℕ)
    (x : cohomology N i) :
    (cohomologyEquivOfIso e i).symm x = cohomologyMap e.inv i x := by
  rw [show cohomologyMap e.inv i = ((cohomologyFunctor X i).map e.inv).hom from rfl,
    ← Functor.mapIso_inv]
  exact ((cohomologyFunctor X i).mapIso e).addCommGroupIsoToAddEquiv_symm_apply x

/-- Zeroth cohomology is canonically equivalent to the group of global sections. -/
def cohomologyZeroEquiv (M : X.Modules) :
    cohomology M 0 ≃+ Γ(M, ⊤) :=
  CategoryTheory.Sheaf.H.equiv₀
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) isTerminalTop

/-- The degree-zero equivalence is natural in the coefficient sheaf. -/
theorem cohomologyZeroEquiv_naturality {M N : X.Modules} (f : M ⟶ N)
    (x : cohomology M 0) :
    f.app ⊤ (cohomologyZeroEquiv M x) =
      cohomologyZeroEquiv N (cohomologyMap f 0 x) := by
  exact CategoryTheory.Sheaf.H.equiv₀_naturality
    isTerminalTop ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f) x

/-- Naturality of the inverse degree-zero equivalence. -/
theorem cohomologyZeroEquiv_symm_naturality {M N : X.Modules} (f : M ⟶ N)
    (x : Γ(M, ⊤)) :
    cohomologyMap f 0 ((cohomologyZeroEquiv M).symm x) =
      (cohomologyZeroEquiv N).symm (f.app ⊤ x) := by
  exact CategoryTheory.Sheaf.H.equiv₀_symm_naturality
    isTerminalTop ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f) x

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
