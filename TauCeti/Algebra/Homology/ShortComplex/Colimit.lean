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

This file proves that homology of short complexes of modules, and hence homology of homological
complexes of modules, commutes with integer-indexed colimits. It applies to an arbitrary universe-
zero ring. Mathlib's AB5 instance supplies the exactness of these filtered colimits.

## Main results

* `TauCeti.shortComplexHomologyFunctor_preservesColimitsOfShape`: homology of short complexes
  preserves exact colimits.
* `TauCeti.homologicalComplexShortComplexFunctor_preservesColimitsOfShape`: the short complex
  associated to a homological complex preserves colimits.
* `TauCeti.homologicalComplexHomologyFunctor_preservesColimitsOfShape`: homology of homological
  complexes preserves exact colimits.

## Implementation notes

Mathlib defines both `ShortComplex.colimitCocone F` and the image under `colim` of the short
complex corresponding to `F` componentwise, using the same three chosen colimits and `colimMap`s.
The object comparison below records this intentional definitional identification. Mathlib exposes
no natural isomorphism comparing these two presentations, and replacing the equality by a
reflexive `ShortComplex.isoMk` loses the definitional identification of the chosen cocone legs and
of the associated `HasHomology` instances.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

variable {R : Type} [Ring R]

private abbrev SmallModuleCat (R : Type) [Ring R] := ModuleCat.{0} R

local notation "J" => ℤ
local notation "C" => SmallModuleCat R

private noncomputable abbrev shortComplexDiagram
    (F : J ⥤ ShortComplex C) : ShortComplex (J ⥤ C) :=
  (ShortComplex.functorEquivalence J C).inverse.obj F

private theorem shortComplexColimitCocone_pt_eq (F : J ⥤ ShortComplex C) :
    (ShortComplex.colimitCocone F).pt = (shortComplexDiagram F).map colim :=
  rfl

private theorem shortComplexColimitCocone_ι_app_eq
    (F : J ⥤ ShortComplex C) (j : J) :
    (shortComplexDiagram F).mapNatTrans (colim.ι j) ≫
        eqToHom (shortComplexColimitCocone_pt_eq F).symm =
      (ShortComplex.colimitCocone F).ι.app j := by
  ext <;> rfl

private theorem shortComplex_mapHomologyIso_colimit
    (F : J ⥤ ShortComplex C) (j : J) :
    ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj j)).hom ≫
        colimit.ι (shortComplexDiagram F).homology j ≫
          ((shortComplexDiagram F).mapHomologyIso colim).symm.hom =
      ShortComplex.homologyMap ((shortComplexDiagram F).mapNatTrans (colim.ι j)) := by
  rw [(shortComplexDiagram F).homologyMap_mapNatTrans (colim.ι j)]
  rfl

private theorem shortComplexHomologyDiagram_obj_eq
    (F : J ⥤ ShortComplex C) (j : J) :
    (F ⋙ ShortComplex.homologyFunctor C).obj j =
      ((shortComplexDiagram F).map ((evaluation J C).obj j)).homology :=
  rfl

private noncomputable def shortComplexHomologyDiagramIso
    (F : J ⥤ ShortComplex C) :
    F ⋙ ShortComplex.homologyFunctor C ≅ (shortComplexDiagram F).homology :=
  NatIso.ofComponents
    (fun j ↦ eqToIso (shortComplexHomologyDiagram_obj_eq F j) ≪≫
      (shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj j))
    (fun {X Y} f ↦ by
      let τ := (evaluation J C).map f
      have h : ShortComplex.homologyMap ((shortComplexDiagram F).mapNatTrans τ) ≫
          ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj Y)).hom =
          ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj X)).hom ≫
            τ.app (shortComplexDiagram F).homology := by
        rw [(shortComplexDiagram F).homologyMap_mapNatTrans τ]
        simp
      exact h)

private theorem shortComplexHomologyDiagramIso_hom_app
    (F : J ⥤ ShortComplex C) (j : J) :
    (shortComplexHomologyDiagramIso F).hom.app j =
      eqToHom (shortComplexHomologyDiagram_obj_eq F j) ≫
        ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj j)).hom :=
  rfl

private theorem shortComplexHomologyDiagramIso_colimit
    (F : J ⥤ ShortComplex C) (j : J) :
    (shortComplexHomologyDiagramIso F).hom.app j ≫
        colimit.ι (shortComplexDiagram F).homology j ≫
          ((shortComplexDiagram F).mapHomologyIso colim).symm.hom =
      eqToHom (shortComplexHomologyDiagram_obj_eq F j) ≫
        ShortComplex.homologyMap ((shortComplexDiagram F).mapNatTrans (colim.ι j)) := by
  rw [shortComplexHomologyDiagramIso_hom_app]
  simp only [Category.assoc]
  rw [shortComplex_mapHomologyIso_colimit F j]

private theorem shortComplexHomologyMapCocone_pt_eq (F : J ⥤ ShortComplex C) :
    (ShortComplex.colimitCocone F).pt.homology =
      ((ShortComplex.homologyFunctor C).mapCocone (ShortComplex.colimitCocone F)).pt :=
  rfl

private theorem shortComplexHomologyFunctor_map_eq
    (F : J ⥤ ShortComplex C) (j : J) :
    eqToHom (shortComplexHomologyDiagram_obj_eq F j) ≫
        ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app j) ≫
          eqToHom (shortComplexHomologyMapCocone_pt_eq F) =
      (ShortComplex.homologyFunctor C).map ((ShortComplex.colimitCocone F).ι.app j) :=
  rfl

private noncomputable def shortComplexHomologyColimitPointIso
    (F : J ⥤ ShortComplex C) :
    colimit (shortComplexDiagram F).homology ≅
      ((ShortComplex.homologyFunctor C).mapCocone (ShortComplex.colimitCocone F)).pt :=
  ((shortComplexDiagram F).mapHomologyIso colim).symm ≪≫
    ShortComplex.homologyMapIso (eqToIso (shortComplexColimitCocone_pt_eq F)).symm ≪≫
      eqToIso (shortComplexHomologyMapCocone_pt_eq F)

private theorem shortComplexHomologyColimit_compatibility
    (F : J ⥤ ShortComplex C) (j : J) :
    (shortComplexHomologyDiagramIso F).hom.app j ≫
        colimit.ι (shortComplexDiagram F).homology j ≫
          (shortComplexHomologyColimitPointIso F).hom =
      (ShortComplex.homologyFunctor C).map ((ShortComplex.colimitCocone F).ι.app j) := by
  dsimp only [shortComplexHomologyColimitPointIso, Iso.trans_hom,
    ShortComplex.homologyMapIso_hom, eqToIso.hom]
  slice_lhs 1 3 => rw [shortComplexHomologyDiagramIso_colimit F j]
  rw [ShortComplex.homologyMapIso_hom]
  slice_lhs 2 3 => rw [← ShortComplex.homologyMap_comp]
  have hEq : (eqToIso (shortComplexColimitCocone_pt_eq F)).symm.hom =
      eqToHom (shortComplexColimitCocone_pt_eq F).symm := by
    cases shortComplexColimitCocone_pt_eq F
    rfl
  rw [hEq, shortComplexColimitCocone_ι_app_eq]
  exact shortComplexHomologyFunctor_map_eq F j

private noncomputable def shortComplexHomologyColimitCoconeIso
    (F : J ⥤ ShortComplex C) :
    (Cocone.precompose (shortComplexHomologyDiagramIso F).hom).obj
        (colimit.cocone (shortComplexDiagram F).homology) ≅
      (ShortComplex.homologyFunctor C).mapCocone (ShortComplex.colimitCocone F) := by
  refine Cocone.ext (shortComplexHomologyColimitPointIso F) ?_
  intro j
  exact shortComplexHomologyColimit_compatibility F j

/-- Homology of short complexes of modules over a universe-zero ring preserves integer-indexed
colimits. -/
theorem shortComplexHomologyFunctor_preservesColimitsOfShape :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor (ModuleCat.{0} R)) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone
      (ShortComplex.isColimitColimitCocone F)
      ((IsColimit.equivOfNatIsoOfIso
        (shortComplexHomologyDiagramIso F).symm
        (colimit.cocone (shortComplexDiagram F).homology)
        ((ShortComplex.homologyFunctor C).mapCocone (ShortComplex.colimitCocone F))
        (shortComplexHomologyColimitCoconeIso (R := R) F)) (colimit.isColimit _))

variable {I : Type*} (c : ComplexShape I) (q : I)

/-- Sending a homological complex of modules to its short complex at one degree preserves
integer-indexed colimits. -/
theorem homologicalComplexShortComplexFunctor_preservesColimitsOfShape :
    PreservesColimitsOfShape J
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} R) c q) where
  preservesColimit {F} := by
    apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    apply ShortComplex.isColimitOfIsColimitπ
    · exact isColimitOfPreserves (HomologicalComplex.eval C c (c.prev q)) (colimit.isColimit F)
    · exact isColimitOfPreserves (HomologicalComplex.eval C c q) (colimit.isColimit F)
    · exact isColimitOfPreserves (HomologicalComplex.eval C c (c.next q)) (colimit.isColimit F)

/-- Homology in any degree of a homological complex of modules over a universe-zero ring preserves
integer-indexed colimits. -/
theorem homologicalComplexHomologyFunctor_preservesColimitsOfShape :
    PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) c q) := by
  let _ := shortComplexHomologyFunctor_preservesColimitsOfShape (R := R)
  let _ := homologicalComplexShortComplexFunctor_preservesColimitsOfShape (R := R) c q
  exact preservesColimitsOfShape_of_natIso (HomologicalComplex.homologyFunctorIso C c q).symm

end TauCeti
