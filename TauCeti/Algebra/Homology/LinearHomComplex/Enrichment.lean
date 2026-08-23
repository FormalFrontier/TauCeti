/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Enriched.Basic
public import TauCeti.Algebra.Homology.LinearHomComplex.Composition

/-!
# Cochain complexes enriched in their linear Hom complexes

Let `C` be an `R`-linear preadditive category.  This file enriches
`CochainComplex C ℤ` in `CochainComplex (ModuleCat R) ℤ`.  The enriched Hom object from `F` to
`G` is `TauCeti.linearHomComplex R F G`, and the enriched identity is the degree-zero cocycle
associated to the identity morphism of `F`.

Mathlib's enriched-category convention orders composition as

`Hom(F, G) ⊗ Hom(G, K) ⟶ Hom(F, K)`.

The closed composition map `TauCeti.linearHomComplexComp` has the opposite factor order, dictated
by the tensor differential and Keller's convention `m₂(g, f) = g ∘ f`.  The enriched composition
therefore first applies the Koszul braiding.  On homogeneous cochains of degrees `p` and `q`, it
sends `f ⊗ g` to `(-1)^(p*q) • (g ∘ f)`, exactly the bridge between Mathlib's factor order and
Keller's operation.

## Main definitions

* `TauCeti.linearHomComplexEnrichedComp`: composition in Mathlib's enriched-category factor order.
* `TauCeti.linearHomComplexEnrichedCategory`: the enrichment of cochain complexes in their
  `R`-linear Hom complexes.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1.
* B. Keller, *Deriving DG categories*, Section 1.
* Kim Morrison's Mathlib `CategoryTheory.EnrichedCategory` interface.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe v u

variable (R : Type v) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- Composition of linear Hom complexes in Mathlib's enriched-category factor order.  It applies
the Koszul braiding and then composes cochains in Keller's order. -/
noncomputable def linearHomComplexEnrichedComp (F G K : CochainComplex C ℤ) :
    linearHomComplex R F G ⊗ linearHomComplex R G K ⟶ linearHomComplex R F K :=
  (β_ (linearHomComplex R F G) (linearHomComplex R G K)).hom ≫
    linearHomComplexComp R F G K

/-- The enriched-order composition is the closed composition map preceded by the Koszul
braiding. -/
lemma linearHomComplexEnrichedComp_def (F G K : CochainComplex C ℤ) :
    linearHomComplexEnrichedComp R F G K =
      (β_ (linearHomComplex R F G) (linearHomComplex R G K)).hom ≫
        linearHomComplexComp R F G K :=
  (rfl)

/-- On the bidegree-`(p, q)` summand, enriched-order composition carries the Koszul sign
`(-1)^(p*q)`, swaps the two module factors, and composes the resulting cochains. -/
@[reassoc (attr := simp)]
lemma ι_linearHomComplexEnrichedComp (F G K : CochainComplex C ℤ) (p q j : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = j) :
    HomologicalComplex.ιMapBifunctor (linearHomComplex R F G) (linearHomComplex R G K)
          (curriedTensor (ModuleCat.{v} R)) (ComplexShape.up ℤ) p q j h ≫
        (linearHomComplexEnrichedComp R F G K).f j =
      (p * q).negOnePow •
        ((β_ ((linearHomComplex R F G).X p) ((linearHomComplex R G K).X q)).hom ≫
          cochainCompTensor R F G K q p j (by dsimp at h ⊢; omega)) := by
  rw [linearHomComplexEnrichedComp_def, HomologicalComplex.comp_f, ← Category.assoc,
    braiding_eq_koszulBraiding, koszulBraiding_hom, ι_koszulBraidingHom,
    koszulBraidingSummand_eq, Linear.units_smul_comp, Category.assoc,
    ι_linearHomComplexComp]

/-- Cochain complexes in an `R`-linear preadditive category are enriched in cochain complexes of
`R`-modules through their `R`-linear Hom complexes. -/
noncomputable instance linearHomComplexEnrichedCategory :
    EnrichedCategory (CochainComplex (ModuleCat.{v} R) ℤ) (CochainComplex C ℤ) where
  Hom := linearHomComplex R
  id := linearHomComplexUnit R
  comp := linearHomComplexEnrichedComp R
  id_comp F G := by
    simp [linearHomComplexEnrichedComp]
  comp_id F G := by
    simp [linearHomComplexEnrichedComp]
  assoc F G K L := by
    simp [linearHomComplexEnrichedComp, linearHomComplexComp_assoc]
    simpa only [Category.assoc] using
      BraidedCategory.yang_baxter_assoc (linearHomComplex R F G) (linearHomComplex R G K)
        (linearHomComplex R K L)
        ((linearHomComplex R K L ◁ linearHomComplexComp R F G K) ≫
          linearHomComplexComp R F K L)

/-- The enriched Hom object is the `R`-linear Hom complex. -/
@[simp]
lemma linearHomComplexEnrichedCategory_hom (F G : CochainComplex C ℤ) :
    (F ⟶[CochainComplex (ModuleCat.{v} R) ℤ] G) = linearHomComplex R F G :=
  rfl

/-- The enriched identity is the identity morphism regarded as a degree-zero cocycle. -/
@[simp]
lemma linearHomComplexEnrichedCategory_eId (F : CochainComplex C ℤ) :
    eId (CochainComplex (ModuleCat.{v} R) ℤ) F = linearHomComplexUnit R F :=
  rfl

/-- Enriched composition is composition in Mathlib's factor order. -/
@[simp]
lemma linearHomComplexEnrichedCategory_eComp (F G K : CochainComplex C ℤ) :
    eComp (CochainComplex (ModuleCat.{v} R) ℤ) F G K =
      linearHomComplexEnrichedComp R F G K :=
  rfl

end TauCeti
