/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Homology and exact colimits

This file proves that homology of short complexes in an abelian category, and hence homology of
homological complexes, commutes with colimits of every shape whose colimits are exact. It also
supplies the small-universe AB5 instance for module categories in which the ring and its modules
live in unrelated universes.

## Main results

* `TauCeti.moduleCat_ab5OfSize`: small filtered colimits of modules are exact.
* `TauCeti.shortComplexHomologyFunctor_preservesColimitsOfShape`: homology of short complexes
  preserves colimits of any exact shape.
* `TauCeti.homologicalComplexShortComplexFunctor_preservesColimitsOfShape`: the short complex
  associated to a homological complex preserves all existing colimits.
* `TauCeti.homologicalComplexHomologyFunctor_preservesColimitsOfShape`: homology of homological
  complexes preserves colimits of any exact shape.

## Implementation notes

A diagram `F : J ⥤ ShortComplex C` corresponds under `ShortComplex.functorEquivalence` to a short
complex `S` of diagrams, and the colimit cocone used here is the image of `S` under
`colim : (J ⥤ C) ⥤ C`, with legs assembled from the counit of that equivalence. Working with the
counit rather than with the definitional identification of the two presentations keeps every
intermediate statement well typed for `rw` and `simp`: in a general category, unlike in a concrete
one, neither the unit laws nor associativity hold definitionally, so the composites appearing here
cannot be manipulated by `rfl` alone.

Exactness of `J`-shaped colimits makes `colim` preserve homology, which turns the homology of that
cocone into the chosen colimit of the pointwise homology diagram.

Mathlib's AB5 instance for `ModuleCat.{u} R` asks for `R : Type u`. The instance here removes the
corresponding restriction on the module universe for small filtered shapes by transporting
exactness along the forgetful functor to abelian groups.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w u' v'

variable {R : Type u} [Ring R]

/-- Small filtered colimits of `R`-modules are exact, with no relation imposed between the
universe of the ring and the universe of the modules. -/
instance moduleCat_ab5OfSize : AB5OfSize.{0, 0} (ModuleCat.{v} R) where
  ofShape J _ _ := by
    have : AB5OfSize.{0, 0} AddCommGrpCat.{v} :=
      AB5OfSize_of_univLE.{0, 0, v, v, v, v + 1} _
    exact HasExactColimitsOfShape.domain_of_functor J
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})

variable {C : Type u'} [Category.{v'} C] [Abelian C]
variable {J : Type w} [Category.{w} J] [HasColimitsOfShape J C]
  [HasExactColimitsOfShape J C]

private noncomputable abbrev shortComplexDiagram
    (F : J ⥤ ShortComplex C) : ShortComplex (J ⥤ C) :=
  (ShortComplex.functorEquivalence J C).inverse.obj F

omit [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] in
/-- Evaluating the short complex of diagrams attached to `F` at `j` gives back `F.obj j`. This is
the corresponding component of the counit of `ShortComplex.functorEquivalence`, stated with the
evaluated short complex as its source so that later composites are well typed. -/
private noncomputable def shortComplexDiagramEvaluationIso
    (F : J ⥤ ShortComplex C) (j : J) :
    (shortComplexDiagram F).map ((evaluation J C).obj j) ≅ F.obj j :=
  ((ShortComplex.functorEquivalence J C).counitIso.app F).app j

omit [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] in
private theorem shortComplexDiagramEvaluationIso_hom_naturality
    (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    (shortComplexDiagram F).mapNatTrans ((evaluation J C).map f) ≫
        (shortComplexDiagramEvaluationIso F Y).hom =
      (shortComplexDiagramEvaluationIso F X).hom ≫ F.map f :=
  ((ShortComplex.functorEquivalence J C).counitIso.app F).hom.naturality f

omit [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] in
private theorem shortComplexDiagramEvaluationIso_inv_naturality
    (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    F.map f ≫ (shortComplexDiagramEvaluationIso F Y).inv =
      (shortComplexDiagramEvaluationIso F X).inv ≫
        (shortComplexDiagram F).mapNatTrans ((evaluation J C).map f) := by
  rw [Iso.comp_inv_eq, Category.assoc, shortComplexDiagramEvaluationIso_hom_naturality,
    Iso.inv_hom_id_assoc]

omit [HasExactColimitsOfShape J C] in
private theorem mapNatTrans_evaluation_comp_colim
    (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    (shortComplexDiagram F).mapNatTrans ((evaluation J C).map f) ≫
        (shortComplexDiagram F).mapNatTrans (colim.ι Y) =
      (shortComplexDiagram F).mapNatTrans (colim.ι X) := by
  ext <;>
    simp only [ShortComplex.comp_τ₁, ShortComplex.comp_τ₂, ShortComplex.comp_τ₃,
      ShortComplex.mapNatTrans_τ₁, ShortComplex.mapNatTrans_τ₂, ShortComplex.mapNatTrans_τ₃,
      evaluation_map_app, colim.ι_app] <;>
    exact colimit.w _ f

/-- The cocone on `F : J ⥤ ShortComplex C` obtained by applying `colim` to the associated short
complex of diagrams. -/
private noncomputable def shortComplexColimCocone (F : J ⥤ ShortComplex C) : Cocone F where
  pt := (shortComplexDiagram F).map colim
  ι :=
    { app := fun j ↦ (shortComplexDiagramEvaluationIso F j).inv ≫
        (shortComplexDiagram F).mapNatTrans (colim.ι j)
      naturality := fun _ _ f ↦ by
        dsimp
        rw [Category.comp_id, ← Category.assoc,
          shortComplexDiagramEvaluationIso_inv_naturality, Category.assoc,
          mapNatTrans_evaluation_comp_colim] }

/-- The cocone `shortComplexColimCocone F` is colimiting: each of its three components is the
chosen colimit cocone of the corresponding diagram in `C`, up to the identities contributed by the
counit of `ShortComplex.functorEquivalence`. -/
private noncomputable def isColimitShortComplexColimCocone (F : J ⥤ ShortComplex C) :
    IsColimit (shortComplexColimCocone F) :=
  ShortComplex.isColimitOfIsColimitπ _
    (IsColimit.ofIsoColimit (colimit.isColimit (F ⋙ ShortComplex.π₁))
      (Cocone.ext (Iso.refl _) fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm))
    (IsColimit.ofIsoColimit (colimit.isColimit (F ⋙ ShortComplex.π₂))
      (Cocone.ext (Iso.refl _) fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm))
    (IsColimit.ofIsoColimit (colimit.isColimit (F ⋙ ShortComplex.π₃))
      (Cocone.ext (Iso.refl _) fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm))

omit [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] in
private theorem mapHomologyIso_evaluation_naturality
    (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    ShortComplex.homologyMap
          ((shortComplexDiagram F).mapNatTrans ((evaluation J C).map f)) ≫
        ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj Y)).hom =
      ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj X)).hom ≫
        (shortComplexDiagram F).homology.map f := by
  -- The transition map of the homology diagram is the component of `(evaluation J C).map f`.
  have h : ShortComplex.homologyMap
        ((shortComplexDiagram F).mapNatTrans ((evaluation J C).map f)) ≫
      ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj Y)).hom =
      ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj X)).hom ≫
        ((evaluation J C).map f).app (shortComplexDiagram F).homology := by
    rw [NatTrans.app_homology ((evaluation J C).map f) (shortComplexDiagram F)]
    simp
  exact h

/-- The pointwise homology diagram of `F` is the homology of the associated short complex of
diagrams, because evaluation preserves homology. -/
private noncomputable def shortComplexHomologyDiagramIso (F : J ⥤ ShortComplex C) :
    F ⋙ ShortComplex.homologyFunctor C ≅ (shortComplexDiagram F).homology :=
  NatIso.ofComponents
    (fun j ↦ ShortComplex.homologyMapIso (shortComplexDiagramEvaluationIso F j).symm ≪≫
      (shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj j))
    (fun {X Y} f ↦ by
      have h : ShortComplex.homologyMap (F.map f) ≫
            (ShortComplex.homologyMap (shortComplexDiagramEvaluationIso F Y).inv ≫
              ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj Y)).hom) =
          (ShortComplex.homologyMap (shortComplexDiagramEvaluationIso F X).inv ≫
              ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj X)).hom) ≫
            (shortComplexDiagram F).homology.map f := by
        rw [Category.assoc, ← mapHomologyIso_evaluation_naturality, ← Category.assoc,
          ← Category.assoc, ← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp,
          shortComplexDiagramEvaluationIso_inv_naturality]
      exact h)

private theorem shortComplex_mapHomologyIso_colimit (F : J ⥤ ShortComplex C) (j : J) :
    ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj j)).hom ≫
        colimit.ι (shortComplexDiagram F).homology j ≫
          ((shortComplexDiagram F).mapHomologyIso colim).inv =
      ShortComplex.homologyMap ((shortComplexDiagram F).mapNatTrans (colim.ι j)) := by
  -- The middle map is the component at `(shortComplexDiagram F).homology` of the natural
  -- transformation `colim.ι j`, so `NatTrans.app_homology` applies.
  change _ ≫ (colim.ι j).app (shortComplexDiagram F).homology ≫ _ = _
  rw [NatTrans.app_homology (colim.ι j) (shortComplexDiagram F)]
  simp

private theorem shortComplexHomologyColimit_compatibility
    (F : J ⥤ ShortComplex C) (j : J) :
    ((ShortComplex.homologyMap (shortComplexDiagramEvaluationIso F j).inv ≫
            ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj j)).hom) ≫
          colimit.ι (shortComplexDiagram F).homology j) ≫
        ((shortComplexDiagram F).mapHomologyIso colim).inv =
      ShortComplex.homologyMap ((shortComplexDiagramEvaluationIso F j).inv ≫
        (shortComplexDiagram F).mapNatTrans (colim.ι j)) := by
  rw [Category.assoc, Category.assoc, shortComplex_mapHomologyIso_colimit,
    ShortComplex.homologyMap_comp]

/-- Homology of the colimit cocone `shortComplexColimCocone F` is the chosen colimit of the
pointwise homology diagram of `F`. -/
private noncomputable def shortComplexHomologyColimitCoconeIso (F : J ⥤ ShortComplex C) :
    (Cocone.precompose (shortComplexHomologyDiagramIso F).hom).obj
        (colimit.cocone (shortComplexDiagram F).homology) ≅
      (ShortComplex.homologyFunctor C).mapCocone (shortComplexColimCocone F) :=
  Cocone.ext ((shortComplexDiagram F).mapHomologyIso colim).symm
    (fun j ↦ shortComplexHomologyColimit_compatibility F j)

/-- Homology of short complexes preserves colimits of any exact shape. -/
instance shortComplexHomologyFunctor_preservesColimitsOfShape :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor C) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitShortComplexColimCocone F)
      ((IsColimit.equivOfNatIsoOfIso
        (shortComplexHomologyDiagramIso F).symm
        (colimit.cocone (shortComplexDiagram F).homology)
        ((ShortComplex.homologyFunctor C).mapCocone (shortComplexColimCocone F))
        (shortComplexHomologyColimitCoconeIso F)) (colimit.isColimit _))

variable {I D : Type*} [Category D] [HasZeroMorphisms D] [HasColimitsOfShape J D]
  (c : ComplexShape I) (q : I)

/-- Sending a homological complex to its short complex at one degree preserves all existing
colimits. -/
instance homologicalComplexShortComplexFunctor_preservesColimitsOfShape :
    PreservesColimitsOfShape J
      (HomologicalComplex.shortComplexFunctor D c q) where
  preservesColimit {F} := by
    apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    apply ShortComplex.isColimitOfIsColimitπ
    · exact isColimitOfPreserves (HomologicalComplex.eval D c (c.prev q))
        (colimit.isColimit F)
    · exact isColimitOfPreserves (HomologicalComplex.eval D c q)
        (colimit.isColimit F)
    · exact isColimitOfPreserves (HomologicalComplex.eval D c (c.next q))
        (colimit.isColimit F)

/-- Homology in any degree of a homological complex preserves colimits of any exact shape. -/
instance homologicalComplexHomologyFunctor_preservesColimitsOfShape :
    PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor C c q) := by
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso C c q).symm

end TauCeti
