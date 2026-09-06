/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony M. Licata
-/
module

public import Mathlib.CategoryTheory.Enriched.Opposite
public import TauCeti.Algebra.Homology.Monoidal.Braiding

/-!
# Differential graded categories

A differential graded category over a commutative ring `R` is a category enriched in cochain
complexes of `R`-modules.  This file gives that specialization of Mathlib's enriched-category API
a name and exposes its first ordinary shadow: the category `Z⁰(C)` whose morphisms are closed
degree-zero elements of the enriched Hom complexes.

Mathlib constructs the underlying category of an enrichment by applying coyoneda at the monoidal
unit.  For cochain complexes, a map from the unit complex is precisely a closed degree-zero
element, so `DGCategory.ZerothCycles C` is the requested `Z⁰` category without a second explicit
category structure.  Enriched functors induce functors on zeroth cycles, and Mathlib's braided
opposite supplies the expected comparison `Z⁰(Cᵒᵖ) ≌ Z⁰(C)ᵒᵖ`.

The enrichment uses `TauCeti.koszulSymmetricCategory`; hence its opposite composition carries the
Koszul braiding.

## Main definitions

* `TauCeti.DGCategory`: categories enriched in cochain complexes of modules.
* `TauCeti.DGFunctor`: enriched functors between differential graded categories.
* `TauCeti.DGCategory.ZerothCycles`: the category of closed degree-zero morphisms.
* `TauCeti.DGFunctor.zerothCycles`: the induced functor on closed degree-zero morphisms.
* `TauCeti.DGCategory.zerothCyclesOppositeEquivalence`: compatibility of `Z⁰` with opposites.
* `CategoryTheory.EnrichedFunctor.forget_map`: the inherited normalization formula for the action
  of `DGFunctor.zerothCycles` on a closed degree-zero morphism.

## References

* B. Keller, *Deriving DG categories*, Section 2.
* A. M. Licata, `CategorifiedLeech.Categorification.DGCategory` and
  `CategorifiedLeech.Categorification.DGHomotopyCategory`, for the source-side explicit-Hom model
  which motivated this enriched formulation.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uC uD

/-- A differential graded category over `R` is a category enriched in cochain complexes of
`R`-modules. -/
abbrev DGCategory (R : Type uR) [CommRing R] (C : Type uC) :=
  EnrichedCategory (CochainComplex (ModuleCat.{uR} R) ℤ) C

/-- A differential graded functor is a functor enriched in cochain complexes of modules. -/
abbrev DGFunctor (R : Type uR) [CommRing R] (C : Type uC) [DGCategory R C]
    (D : Type uD) [DGCategory R D] :=
  EnrichedFunctor (CochainComplex (ModuleCat.{uR} R) ℤ) C D

namespace DGCategory

variable (R : Type uR) [CommRing R] (C : Type uC) [DGCategory R C]

/-- The category `Z⁰(C)` of a differential graded category.  Its objects are those of `C`, and a
morphism is a map from the monoidal unit to the enriched Hom complex, equivalently a closed
degree-zero element. -/
abbrev ZerothCycles :=
  ForgetEnrichment (CochainComplex (ModuleCat.{uR} R) ℤ) C

/-- Taking closed degree-zero morphisms commutes with passing to the DG opposite. -/
noncomputable def zerothCyclesOppositeEquivalence :
    ZerothCycles R Cᵒᵖ ≌ (ZerothCycles R C)ᵒᵖ :=
  forgetEnrichmentOppositeEquivalence (CochainComplex (ModuleCat.{uR} R) ℤ) C

end DGCategory

namespace DGFunctor

variable {R : Type uR} [CommRing R]
  {C : Type uC} {D : Type uD} [DGCategory R C] [DGCategory R D]

/-- A DG functor acts on the categories of closed degree-zero morphisms. -/
noncomputable abbrev zerothCycles (F : DGFunctor R C D) :
    DGCategory.ZerothCycles R C ⥤ DGCategory.ZerothCycles R D :=
  F.forget

end DGFunctor

end TauCeti
