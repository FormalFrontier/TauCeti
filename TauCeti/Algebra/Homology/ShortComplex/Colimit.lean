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
complexes of modules, commutes with exact colimits. It also supplies the small-universe AB5
instance needed when the ring and its modules live in unrelated universes.

## Main results

* `TauCeti.moduleCat_ab5OfSize`: small filtered colimits of modules are exact.
* `TauCeti.shortComplexHomologyFunctor_preservesColimitsOfShape`: homology of short complexes of
  modules preserves colimits of any exact shape.
* `TauCeti.homologicalComplexShortComplexFunctor_preservesColimitsOfShape`: the short complex
  associated to a homological complex preserves all existing colimits.
* `TauCeti.homologicalComplexHomologyFunctor_preservesColimitsOfShape`: homology of homological
  complexes of modules preserves colimits of any exact shape.

## Implementation notes

Mathlib defines both `ShortComplex.colimitCocone F` and the image under `colim` of the short
complex corresponding to `F` componentwise, using the same three chosen colimits and `colimMap`s.
The object comparison below records this intentional definitional identification. Mathlib exposes
no natural isomorphism comparing these two presentations, and replacing the equality by a
reflexive `ShortComplex.isoMk` loses the definitional identification of the chosen cocone legs and
of the associated `HasHomology` instances.

Mathlib's AB5 instance for `ModuleCat.{u} R` asks for `R : Type u`. The instance here removes the
corresponding restriction on the module universe for small filtered shapes by transporting
exactness along the forgetful functor to abelian groups.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {R : Type u} [Ring R]

/-- Small filtered colimits of `R`-modules are exact, with no relation imposed between the
universe of the ring and the universe of the modules. -/
instance moduleCat_ab5OfSize : AB5OfSize.{0, 0} (ModuleCat.{v} R) where
  ofShape J _ _ := by
    have : AB5OfSize.{0, 0} AddCommGrpCat.{v} :=
      AB5OfSize_of_univLE.{0, 0, v, v, v, v + 1} _
    exact HasExactColimitsOfShape.domain_of_functor J
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})

variable {J : Type w} [Category.{w} J] [HasColimitsOfShape J (ModuleCat.{v} R)]
  [HasExactColimitsOfShape J (ModuleCat.{v} R)]

private noncomputable abbrev shortComplexDiagram
    (F : J ⥤ ShortComplex (ModuleCat.{v} R)) : ShortComplex (J ⥤ ModuleCat.{v} R) :=
  (ShortComplex.functorEquivalence J (ModuleCat.{v} R)).inverse.obj F

omit [HasExactColimitsOfShape J (ModuleCat.{v} R)] in
private theorem shortComplexColimitCocone_pt_eq (F : J ⥤ ShortComplex (ModuleCat.{v} R)) :
    (ShortComplex.colimitCocone F).pt = (shortComplexDiagram F).map colim :=
  rfl

omit [HasExactColimitsOfShape J (ModuleCat.{v} R)] in
private theorem shortComplexColimitCocone_ι_app_eq
    (F : J ⥤ ShortComplex (ModuleCat.{v} R)) (j : J) :
    (shortComplexDiagram F).mapNatTrans (colim.ι j) ≫
        eqToHom (shortComplexColimitCocone_pt_eq F).symm =
      (ShortComplex.colimitCocone F).ι.app j := by
  ext <;> rfl

private theorem shortComplex_mapHomologyIso_colimit
    (F : J ⥤ ShortComplex (ModuleCat.{v} R)) (j : J) :
    ((shortComplexDiagram F).mapHomologyIso ((evaluation J (ModuleCat.{v} R)).obj j)).hom ≫
        colimit.ι (shortComplexDiagram F).homology j ≫
          ((shortComplexDiagram F).mapHomologyIso colim).symm.hom =
      ShortComplex.homologyMap ((shortComplexDiagram F).mapNatTrans (colim.ι j)) := by
  change _ ≫ (colim.ι j).app (shortComplexDiagram F).homology ≫ _ = _
  rw [NatTrans.app_homology (colim.ι j) (shortComplexDiagram F)]
  simp

omit [HasColimitsOfShape J (ModuleCat.{v} R)]
  [HasExactColimitsOfShape J (ModuleCat.{v} R)] in
private theorem shortComplexHomologyDiagram_obj_eq
    (F : J ⥤ ShortComplex (ModuleCat.{v} R)) (j : J) :
    (F ⋙ ShortComplex.homologyFunctor (ModuleCat.{v} R)).obj j =
      ((shortComplexDiagram F).map ((evaluation J (ModuleCat.{v} R)).obj j)).homology :=
  rfl

private noncomputable def shortComplexHomologyDiagramIso
    (F : J ⥤ ShortComplex (ModuleCat.{v} R)) :
    F ⋙ ShortComplex.homologyFunctor (ModuleCat.{v} R) ≅ (shortComplexDiagram F).homology :=
  NatIso.ofComponents
    (fun j ↦ eqToIso (shortComplexHomologyDiagram_obj_eq F j) ≪≫
      (shortComplexDiagram F).mapHomologyIso ((evaluation J (ModuleCat.{v} R)).obj j))
    (fun {X Y} f ↦ by
      let τ := (evaluation J (ModuleCat.{v} R)).map f
      have h : ShortComplex.homologyMap ((shortComplexDiagram F).mapNatTrans τ) ≫
          ((shortComplexDiagram F).mapHomologyIso ((evaluation J (ModuleCat.{v} R)).obj Y)).hom =
          ((shortComplexDiagram F).mapHomologyIso ((evaluation J (ModuleCat.{v} R)).obj X)).hom ≫
            τ.app (shortComplexDiagram F).homology := by
        rw [NatTrans.app_homology τ (shortComplexDiagram F)]
        simp
      exact h)

omit [HasColimitsOfShape J (ModuleCat.{v} R)]
  [HasExactColimitsOfShape J (ModuleCat.{v} R)] in
private theorem shortComplexHomologyDiagramIso_hom_app
    (F : J ⥤ ShortComplex (ModuleCat.{v} R)) (j : J) :
    (shortComplexHomologyDiagramIso F).hom.app j =
      eqToHom (shortComplexHomologyDiagram_obj_eq F j) ≫
        ((shortComplexDiagram F).mapHomologyIso ((evaluation J (ModuleCat.{v} R)).obj j)).hom :=
  rfl

private theorem shortComplexHomologyDiagramIso_colimit
    (F : J ⥤ ShortComplex (ModuleCat.{v} R)) (j : J) :
    (shortComplexHomologyDiagramIso F).hom.app j ≫
        colimit.ι (shortComplexDiagram F).homology j ≫
          ((shortComplexDiagram F).mapHomologyIso colim).symm.hom =
      eqToHom (shortComplexHomologyDiagram_obj_eq F j) ≫
        ShortComplex.homologyMap ((shortComplexDiagram F).mapNatTrans (colim.ι j)) := by
  rw [shortComplexHomologyDiagramIso_hom_app]
  simp only [Category.assoc]
  rw [shortComplex_mapHomologyIso_colimit F j]

omit [HasExactColimitsOfShape J (ModuleCat.{v} R)] in
private theorem shortComplexHomologyMapCocone_pt_eq
    (F : J ⥤ ShortComplex (ModuleCat.{v} R)) :
    (ShortComplex.colimitCocone F).pt.homology =
      ((ShortComplex.homologyFunctor (ModuleCat.{v} R)).mapCocone
        (ShortComplex.colimitCocone F)).pt :=
  rfl

omit [HasExactColimitsOfShape J (ModuleCat.{v} R)] in
private theorem shortComplexHomologyFunctor_map_eq
    (F : J ⥤ ShortComplex (ModuleCat.{v} R)) (j : J) :
    eqToHom (shortComplexHomologyDiagram_obj_eq F j) ≫
        ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app j) ≫
          eqToHom (shortComplexHomologyMapCocone_pt_eq F) =
      (ShortComplex.homologyFunctor (ModuleCat.{v} R)).map
        ((ShortComplex.colimitCocone F).ι.app j) :=
  rfl

private noncomputable def shortComplexHomologyColimitPointIso
    (F : J ⥤ ShortComplex (ModuleCat.{v} R)) :
    colimit (shortComplexDiagram F).homology ≅
      ((ShortComplex.homologyFunctor (ModuleCat.{v} R)).mapCocone
        (ShortComplex.colimitCocone F)).pt :=
  ((shortComplexDiagram F).mapHomologyIso colim).symm ≪≫
    ShortComplex.homologyMapIso (eqToIso (shortComplexColimitCocone_pt_eq F)).symm ≪≫
      eqToIso (shortComplexHomologyMapCocone_pt_eq F)

private theorem shortComplexHomologyColimit_compatibility
    (F : J ⥤ ShortComplex (ModuleCat.{v} R)) (j : J) :
    (shortComplexHomologyDiagramIso F).hom.app j ≫
        colimit.ι (shortComplexDiagram F).homology j ≫
          (shortComplexHomologyColimitPointIso F).hom =
      (ShortComplex.homologyFunctor (ModuleCat.{v} R)).map
        ((ShortComplex.colimitCocone F).ι.app j) := by
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
    (F : J ⥤ ShortComplex (ModuleCat.{v} R)) :
    (Cocone.precompose (shortComplexHomologyDiagramIso F).hom).obj
        (colimit.cocone (shortComplexDiagram F).homology) ≅
      (ShortComplex.homologyFunctor (ModuleCat.{v} R)).mapCocone
        (ShortComplex.colimitCocone F) := by
  refine Cocone.ext (shortComplexHomologyColimitPointIso F) ?_
  intro j
  exact shortComplexHomologyColimit_compatibility F j

/-- Homology of short complexes of modules preserves colimits of any exact shape. -/
instance shortComplexHomologyFunctor_preservesColimitsOfShape :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor (ModuleCat.{v} R)) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone
      (ShortComplex.isColimitColimitCocone F)
      ((IsColimit.equivOfNatIsoOfIso
        (shortComplexHomologyDiagramIso F).symm
        (colimit.cocone (shortComplexDiagram F).homology)
        ((ShortComplex.homologyFunctor (ModuleCat.{v} R)).mapCocone
          (ShortComplex.colimitCocone F))
        (shortComplexHomologyColimitCoconeIso (R := R) F)) (colimit.isColimit _))

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

/-- Homology in any degree of a homological complex of modules preserves colimits of any exact
shape. -/
instance homologicalComplexHomologyFunctor_preservesColimitsOfShape :
    PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) c q) := by
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso (ModuleCat.{v} R) c q).symm

end TauCeti
