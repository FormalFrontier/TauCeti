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

* `Scheme.Modules.Cohomology M i`, the group `Hⁱ(X, M)`;
* `Scheme.Modules.cohomologyFunctor X i`, functoriality in the coefficient sheaf;
* `Scheme.Modules.cohomologyZeroEquiv`, the canonical equivalence
  `H⁰(X, M) ≃+ Γ(M, ⊤)` with global sections.

The construction is stated for every sheaf of modules, which is the natural generality of sheaf
cohomology. In particular it applies to finitely presented sheaves through their underlying
objects, and hence supplies the `Hⁱ(X, ℱ)` used for coherent sheaves in
`TauCetiRoadmap/JacobianChallenge/README.md`, Layer B. Finite-dimensionality for proper schemes,
vanishing on curves, and the comparison with Čech cohomology remain later Layer B work.

No formalization is vendored. The definitions reuse Mathlib's `Sheaf.H`, `Sheaf.functorH`,
and `Sheaf.H.equiv₀`.
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
abbrev Cohomology (M : X.Modules) (i : ℕ) : Type u :=
  CategoryTheory.Sheaf.H.{u}
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) i

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

/-- Zeroth cohomology is canonically equivalent to the group of global sections.

The equivalence is natural in the coefficient sheaf; see `cohomologyZeroEquiv_naturality` and
`cohomologyZeroEquiv_symm_naturality`. -/
def cohomologyZeroEquiv (M : X.Modules) :
    Cohomology M 0 ≃+ Γ(M, ⊤) :=
  CategoryTheory.Sheaf.H.equiv₀
    ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj M) isTerminalTop

/-- The degree-zero cohomology equivalence commutes with maps of coefficient sheaves. -/
lemma cohomologyZeroEquiv_naturality {M N : X.Modules} (f : M ⟶ N)
    (x : Cohomology M 0) :
    f.app ⊤ (cohomologyZeroEquiv M x) =
      cohomologyZeroEquiv N (((cohomologyFunctor X 0).map f).hom x) := by
  -- The scheme-level section map and cohomology-functor map are definitionally the maps of the
  -- underlying abelian sheaves.
  exact CategoryTheory.Sheaf.H.equiv₀_naturality
    isTerminalTop ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f) x

/-- The inverse degree-zero cohomology equivalence commutes with maps of coefficient sheaves. -/
lemma cohomologyZeroEquiv_symm_naturality {M N : X.Modules} (f : M ⟶ N)
    (x : Γ(M, ⊤)) :
    ((cohomologyFunctor X 0).map f).hom ((cohomologyZeroEquiv M).symm x) =
      (cohomologyZeroEquiv N).symm (f.app ⊤ x) := by
  -- The scheme-level section map and cohomology-functor map are definitionally the maps of the
  -- underlying abelian sheaves.
  exact CategoryTheory.Sheaf.H.equiv₀_symm_naturality
    isTerminalTop ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map f) x

end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti
