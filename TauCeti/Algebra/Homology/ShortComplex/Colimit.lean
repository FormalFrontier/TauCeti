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
complexes of modules, commutes with integer-indexed colimits. The ring and the modules may live in
unrelated universes. Mathlib's AB5 theorem supplies the exactness of these filtered colimits.

## Main results

* `TauCeti.moduleCat_hasExactColimitsOfShape_int`: integer-indexed colimits of modules are exact.
* `TauCeti.shortComplexHomologyFunctor_preservesColimitsOfShape_int`: homology of short complexes
  preserves exact colimits.
* `TauCeti.homologicalComplexShortComplexFunctor_preservesColimitsOfShape_int`: the short complex
  associated to a homological complex preserves colimits.
* `TauCeti.homologicalComplexHomologyFunctor_preservesColimitsOfShape_int`: homology of homological
  complexes preserves exact colimits.

## Implementation notes

Mathlib defines both `ShortComplex.colimitCocone F` and the image under `colim` of the short
complex corresponding to `F` componentwise, using the same three chosen colimits and `colimMap`s.
The object comparison below records this intentional definitional identification. Mathlib exposes
no natural isomorphism comparing these two presentations, and replacing the equality by a
reflexive `ShortComplex.isoMk` loses the definitional identification of the chosen cocone legs and
of the associated `HasHomology` instances.

Mathlib's AB5 instance for `ModuleCat.{u} R` asks for `R : Type u` and covers only indexing
categories in universe `u`, so it does not apply to the shape `ℤ` for modules in a larger universe.
`moduleCat_hasExactColimitsOfShape_int` lifts both restrictions by transporting exactness along the
forgetful functor to abelian groups. The module category is then spelled out explicitly, because a
`local notation` abbreviation cannot carry the explicit universe argument.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type u} [Ring R]

local notation "J" => ℤ

/-- Integer-indexed colimits of `R`-modules are exact, with no relation imposed between the
universe of the ring and the universe of the modules. -/
instance moduleCat_hasExactColimitsOfShape_int :
    HasExactColimitsOfShape J (ModuleCat.{v} R) := by
  have : AB5OfSize.{0, 0} AddCommGrpCat.{v} := AB5OfSize_of_univLE.{0, 0, v, v, v, v + 1} _
  exact HasExactColimitsOfShape.domain_of_functor J (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})

private noncomputable abbrev shortComplexDiagram
    (F : J ⥤ ShortComplex (ModuleCat.{v} R)) : ShortComplex (J ⥤ (ModuleCat.{v} R)) :=
  (ShortComplex.functorEquivalence J (ModuleCat.{v} R)).inverse.obj F

private theorem shortComplexColimitCocone_pt_eq (F : J ⥤ ShortComplex (ModuleCat.{v} R)) :
    (ShortComplex.colimitCocone F).pt = (shortComplexDiagram F).map colim :=
  rfl

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
  rw [(shortComplexDiagram F).homologyMap_mapNatTrans (colim.ι j)]
  rfl

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
        rw [(shortComplexDiagram F).homologyMap_mapNatTrans τ]
        simp
      exact h)

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

private theorem shortComplexHomologyMapCocone_pt_eq (F : J ⥤ ShortComplex (ModuleCat.{v} R)) :
    (ShortComplex.colimitCocone F).pt.homology =
      ((ShortComplex.homologyFunctor (ModuleCat.{v} R)).mapCocone
        (ShortComplex.colimitCocone F)).pt :=
  rfl

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

/-- Homology of short complexes of modules preserves integer-indexed colimits. -/
theorem shortComplexHomologyFunctor_preservesColimitsOfShape_int :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor (ModuleCat.{v} R)) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone
      (ShortComplex.isColimitColimitCocone F)
      ((IsColimit.equivOfNatIsoOfIso
        (shortComplexHomologyDiagramIso F).symm
        (colimit.cocone (shortComplexDiagram F).homology)
        ((ShortComplex.homologyFunctor (ModuleCat.{v} R)).mapCocone (ShortComplex.colimitCocone F))
        (shortComplexHomologyColimitCoconeIso (R := R) F)) (colimit.isColimit _))

variable {I : Type*} (c : ComplexShape I) (q : I)

/-- Sending a homological complex of modules to its short complex at one degree preserves
integer-indexed colimits. -/
theorem homologicalComplexShortComplexFunctor_preservesColimitsOfShape_int :
    PreservesColimitsOfShape J
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R) c q) where
  preservesColimit {F} := by
    apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    apply ShortComplex.isColimitOfIsColimitπ
    · exact isColimitOfPreserves (HomologicalComplex.eval (ModuleCat.{v} R) c (c.prev q))
        (colimit.isColimit F)
    · exact isColimitOfPreserves (HomologicalComplex.eval (ModuleCat.{v} R) c q)
        (colimit.isColimit F)
    · exact isColimitOfPreserves (HomologicalComplex.eval (ModuleCat.{v} R) c (c.next q))
        (colimit.isColimit F)

/-- Homology in any degree of a homological complex of modules preserves integer-indexed
colimits. -/
theorem homologicalComplexHomologyFunctor_preservesColimitsOfShape_int :
    PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) c q) := by
  let _ := shortComplexHomologyFunctor_preservesColimitsOfShape_int (R := R)
  let _ := homologicalComplexShortComplexFunctor_preservesColimitsOfShape_int (R := R) c q
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso (ModuleCat.{v} R) c q).symm

end TauCeti
