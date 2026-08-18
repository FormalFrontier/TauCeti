/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import TauCeti.LowDimTopology.Plumbing.Filtration.Colimit

/-!
# The lattice-homology weight filtration

The characteristic-weight sublevel complexes form a filtered diagram whose colimit is the full
lattice chain complex. This file passes that presentation through homology: in every cubical degree,
the homology of the full complex is the filtered colimit of the sublevel homology modules. When the
plumbing is negative definite, the sublevel chain groups are finitely generated, so this result is
the bridge from finite sublevel calculations to the untruncated invariant.

The proof uses Mathlib's AB5 theorem for module categories. Exactness of filtered colimits makes
homology commute with the integer-indexed colimit; the private categorical construction below
transports this fact through Mathlib's equivalence between short complexes of diagrams and diagrams
of short complexes.

## Main definitions

* `TauCeti.PlumbingGraph.latticeWeightSublevelHomology`: homology of one weight sublevel.
* `TauCeti.PlumbingGraph.latticeWeightSublevelHomologyFunctor`: the filtered diagram of sublevel
  homology modules.
* `TauCeti.PlumbingGraph.latticeWeightSublevelHomologyCocone`: the canonical cocone into full
  lattice homology.
* `TauCeti.PlumbingGraph.latticeWeightSublevelHomologyCoconeIsColimit`: full lattice homology is
  the colimit of the sublevel homologies.

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L, which asks for
Némethi's lattice homology from lattice points and weight functions and for computations of
concrete negative-definite plumbings. The weight-sublevel presentation follows A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

namespace PlumbingGraph

universe u v

private theorem shortComplexColimitCocone_pt_eq
    (F : ℤ ⥤ ShortComplex (ModuleCat PlumbingCoefficient)) :
    (ShortComplex.colimitCocone F).pt =
      ((ShortComplex.functorEquivalence ℤ
        (ModuleCat PlumbingCoefficient)).inverse.obj F).map
          (colim : (ℤ ⥤ ModuleCat PlumbingCoefficient) ⥤
            ModuleCat PlumbingCoefficient) :=
  rfl

private theorem shortComplexColimitCocone_ι_app_eq
    (F : ℤ ⥤ ShortComplex (ModuleCat PlumbingCoefficient)) (j : ℤ) :
    ((ShortComplex.functorEquivalence ℤ
      (ModuleCat PlumbingCoefficient)).inverse.obj F).mapNatTrans (colim.ι j) ≫
        eqToHom (shortComplexColimitCocone_pt_eq F).symm =
      (ShortComplex.colimitCocone F).ι.app j := by
  ext <;> rfl

private theorem shortComplex_mapHomologyIso_colimit
    (F : ℤ ⥤ ShortComplex (ModuleCat PlumbingCoefficient)) (j : ℤ) :
    let S := (ShortComplex.functorEquivalence ℤ
      (ModuleCat PlumbingCoefficient)).inverse.obj F
    (S.mapHomologyIso ((evaluation ℤ (ModuleCat PlumbingCoefficient)).obj j)).hom ≫
        colimit.ι S.homology j ≫ (S.mapHomologyIso
          (colim : (ℤ ⥤ ModuleCat PlumbingCoefficient) ⥤
            ModuleCat PlumbingCoefficient)).symm.hom =
      ShortComplex.homologyMap (S.mapNatTrans (colim.ι j)) := by
  dsimp only
  rw [((ShortComplex.functorEquivalence ℤ
    (ModuleCat PlumbingCoefficient)).inverse.obj F).homologyMap_mapNatTrans (colim.ι j)]
  rfl

private theorem shortComplexHomologyDiagram_obj_eq
    {J : Type u} [Category.{v} J]
    (F : J ⥤ ShortComplex (ModuleCat PlumbingCoefficient)) (j : J) :
    (F ⋙ ShortComplex.homologyFunctor (ModuleCat PlumbingCoefficient)).obj j =
      (((ShortComplex.functorEquivalence J
        (ModuleCat PlumbingCoefficient)).inverse.obj F).map
          ((evaluation J (ModuleCat PlumbingCoefficient)).obj j)).homology :=
  rfl

private noncomputable def shortComplexHomologyDiagramIso
    {J : Type u} [Category.{v} J]
    (F : J ⥤ ShortComplex (ModuleCat PlumbingCoefficient)) :
    F ⋙ ShortComplex.homologyFunctor (ModuleCat PlumbingCoefficient) ≅
      ((ShortComplex.functorEquivalence J
        (ModuleCat PlumbingCoefficient)).inverse.obj F).homology := by
  let S := (ShortComplex.functorEquivalence J
    (ModuleCat PlumbingCoefficient)).inverse.obj F
  exact NatIso.ofComponents
    (fun j => eqToIso (shortComplexHomologyDiagram_obj_eq F j) ≪≫
      S.mapHomologyIso ((evaluation J (ModuleCat PlumbingCoefficient)).obj j))
    (fun {X Y} f => by
      let τ := (evaluation J (ModuleCat PlumbingCoefficient)).map f
      have h : ShortComplex.homologyMap (S.mapNatTrans τ) ≫
          (S.mapHomologyIso ((evaluation J (ModuleCat PlumbingCoefficient)).obj Y)).hom =
          (S.mapHomologyIso ((evaluation J (ModuleCat PlumbingCoefficient)).obj X)).hom ≫
            τ.app S.homology := by
        rw [S.homologyMap_mapNatTrans τ]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact h)

private theorem shortComplexHomologyDiagramIso_hom_app
    {J : Type u} [Category.{v} J]
    (F : J ⥤ ShortComplex (ModuleCat PlumbingCoefficient)) (j : J) :
    (shortComplexHomologyDiagramIso F).hom.app j =
      eqToHom (shortComplexHomologyDiagram_obj_eq F j) ≫
        (((ShortComplex.functorEquivalence J
          (ModuleCat PlumbingCoefficient)).inverse.obj F).mapHomologyIso
            ((evaluation J (ModuleCat PlumbingCoefficient)).obj j)).hom :=
  rfl

private theorem shortComplexHomologyDiagramIso_colimit
    (F : ℤ ⥤ ShortComplex (ModuleCat PlumbingCoefficient)) (j : ℤ) :
    let S := (ShortComplex.functorEquivalence ℤ
      (ModuleCat PlumbingCoefficient)).inverse.obj F
    (shortComplexHomologyDiagramIso F).hom.app j ≫ colimit.ι S.homology j ≫
        (S.mapHomologyIso (colim : (ℤ ⥤ ModuleCat PlumbingCoefficient) ⥤
          ModuleCat PlumbingCoefficient)).symm.hom =
      eqToHom (shortComplexHomologyDiagram_obj_eq F j) ≫
        ShortComplex.homologyMap (S.mapNatTrans (colim.ι j)) := by
  dsimp only
  rw [shortComplexHomologyDiagramIso_hom_app]
  simp only [Category.assoc]
  rw [shortComplex_mapHomologyIso_colimit F j]

private theorem shortComplexHomologyMapCocone_pt_eq
    (F : ℤ ⥤ ShortComplex (ModuleCat PlumbingCoefficient)) :
    (ShortComplex.colimitCocone F).pt.homology =
      ((ShortComplex.homologyFunctor (ModuleCat PlumbingCoefficient)).mapCocone
        (ShortComplex.colimitCocone F)).pt :=
  rfl

private theorem shortComplexHomologyFunctor_map_eq
    (F : ℤ ⥤ ShortComplex (ModuleCat PlumbingCoefficient)) (j : ℤ) :
    eqToHom (shortComplexHomologyDiagram_obj_eq F j) ≫
        ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app j) ≫
          eqToHom (shortComplexHomologyMapCocone_pt_eq F) =
      (ShortComplex.homologyFunctor (ModuleCat PlumbingCoefficient)).map
        ((ShortComplex.colimitCocone F).ι.app j) := by
  rfl

private noncomputable def shortComplexHomologyColimitPointIso
    (F : ℤ ⥤ ShortComplex (ModuleCat PlumbingCoefficient)) :
    let S := (ShortComplex.functorEquivalence ℤ
      (ModuleCat PlumbingCoefficient)).inverse.obj F
    colimit S.homology ≅
      ((ShortComplex.homologyFunctor (ModuleCat PlumbingCoefficient)).mapCocone
        (ShortComplex.colimitCocone F)).pt :=
  let S := (ShortComplex.functorEquivalence ℤ
    (ModuleCat PlumbingCoefficient)).inverse.obj F
  (S.mapHomologyIso (colim : (ℤ ⥤ ModuleCat PlumbingCoefficient) ⥤
      ModuleCat PlumbingCoefficient)).symm ≪≫
    ShortComplex.homologyMapIso (eqToIso (shortComplexColimitCocone_pt_eq F)).symm ≪≫
      eqToIso (shortComplexHomologyMapCocone_pt_eq F)

private theorem shortComplexHomologyColimit_compatibility
    (F : ℤ ⥤ ShortComplex (ModuleCat PlumbingCoefficient)) (j : ℤ) :
    let S := (ShortComplex.functorEquivalence ℤ
      (ModuleCat PlumbingCoefficient)).inverse.obj F
    (shortComplexHomologyDiagramIso F).hom.app j ≫ colimit.ι S.homology j ≫
        (shortComplexHomologyColimitPointIso F).hom =
      (ShortComplex.homologyFunctor (ModuleCat PlumbingCoefficient)).map
        ((ShortComplex.colimitCocone F).ι.app j) := by
  dsimp only [shortComplexHomologyColimitPointIso, Iso.trans_hom,
    ShortComplex.homologyMapIso_hom, eqToIso.hom]
  slice_lhs 1 3 => rw [shortComplexHomologyDiagramIso_colimit F j]
  rw [ShortComplex.homologyMapIso_hom]
  slice_lhs 2 3 => rw [← ShortComplex.homologyMap_comp]
  have hEq : (eqToIso (shortComplexColimitCocone_pt_eq F)).symm.hom =
      eqToHom (shortComplexColimitCocone_pt_eq F).symm :=
    by
      cases shortComplexColimitCocone_pt_eq F
      rfl
  rw [hEq]
  rw [shortComplexColimitCocone_ι_app_eq]
  exact shortComplexHomologyFunctor_map_eq F j

private noncomputable def shortComplexHomologyColimitCoconeIso
    (F : ℤ ⥤ ShortComplex (ModuleCat PlumbingCoefficient)) :
    (Cocone.precompose (shortComplexHomologyDiagramIso F).hom).obj
        (colimit.cocone
          ((ShortComplex.functorEquivalence ℤ
            (ModuleCat PlumbingCoefficient)).inverse.obj F).homology) ≅
      (ShortComplex.homologyFunctor (ModuleCat PlumbingCoefficient)).mapCocone
        (ShortComplex.colimitCocone F) := by
  refine Cocone.ext (shortComplexHomologyColimitPointIso F) ?_
  intro j
  exact shortComplexHomologyColimit_compatibility F j

private noncomputable instance shortComplexHomologyFunctor_preservesColimitsOfShape_int :
    PreservesColimitsOfShape ℤ
      (ShortComplex.homologyFunctor (ModuleCat.{0} PlumbingCoefficient)) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone
      (ShortComplex.isColimitColimitCocone F)
      ((IsColimit.equivOfNatIsoOfIso
        (shortComplexHomologyDiagramIso F).symm
        (colimit.cocone
          ((ShortComplex.functorEquivalence ℤ
            (ModuleCat PlumbingCoefficient)).inverse.obj F).homology)
        ((ShortComplex.homologyFunctor (ModuleCat PlumbingCoefficient)).mapCocone
          (ShortComplex.colimitCocone F))
        (shortComplexHomologyColimitCoconeIso F))
          (colimit.isColimit _))

private noncomputable instance shortComplexFunctor_preservesColimitsOfShape_int
    (q : ℕ) : PreservesColimitsOfShape ℤ
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} PlumbingCoefficient)
        (ComplexShape.down ℕ) q) where
  preservesColimit {F} := by
    apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    apply ShortComplex.isColimitOfIsColimitπ
    · -- Projecting the associated short complex at its first object is evaluation at `prev q`.
      change IsColimit ((HomologicalComplex.eval (ModuleCat PlumbingCoefficient)
        (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev q)).mapCocone (colimit.cocone F))
      exact isColimitOfPreserves
        (HomologicalComplex.eval (ModuleCat PlumbingCoefficient) (ComplexShape.down ℕ)
          ((ComplexShape.down ℕ).prev q)) (colimit.isColimit F)
    · -- Projecting the associated short complex at its middle object is evaluation at `q`.
      change IsColimit ((HomologicalComplex.eval (ModuleCat PlumbingCoefficient)
        (ComplexShape.down ℕ) q).mapCocone (colimit.cocone F))
      exact isColimitOfPreserves
        (HomologicalComplex.eval (ModuleCat PlumbingCoefficient) (ComplexShape.down ℕ) q)
          (colimit.isColimit F)
    · -- Projecting the associated short complex at its third object is evaluation at `next q`.
      change IsColimit ((HomologicalComplex.eval (ModuleCat PlumbingCoefficient)
        (ComplexShape.down ℕ) ((ComplexShape.down ℕ).next q)).mapCocone (colimit.cocone F))
      exact isColimitOfPreserves
        (HomologicalComplex.eval (ModuleCat PlumbingCoefficient) (ComplexShape.down ℕ)
          ((ComplexShape.down ℕ).next q)) (colimit.isColimit F)

private noncomputable instance homologyFunctor_preservesColimitsOfShape_int (q : ℕ) :
    PreservesColimitsOfShape ℤ
      (HomologicalComplex.homologyFunctor (ModuleCat.{0} PlumbingCoefficient)
        (ComplexShape.down ℕ) q) :=
  preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso
      (ModuleCat PlumbingCoefficient) (ComplexShape.down ℕ) q).symm

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The homology in cubical degree `q` of the characteristic-weight sublevel complex at level
`N`. Each chain group of this complex is finitely generated when the plumbing is negative
definite. -/
noncomputable def latticeWeightSublevelHomology (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) : ModuleCat PlumbingCoefficient :=
  (P.latticeWeightSublevelComplex k N).homology q

/-- Weight-sublevel homology is the canonical homology object of the corresponding sublevel
chain complex. -/
theorem latticeWeightSublevelHomology_def (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    P.latticeWeightSublevelHomology k N q =
      (P.latticeWeightSublevelComplex k N).homology q := (rfl)

/-- The integer-indexed diagram of characteristic-weight sublevel homology modules in cubical
degree `q`. Its transition maps are induced by the inclusions of weight sublevel complexes. -/
noncomputable def latticeWeightSublevelHomologyFunctor (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) : Functor ℤ (ModuleCat PlumbingCoefficient) :=
  P.latticeWeightSublevelFunctor k ⋙
    HomologicalComplex.homologyFunctor (ModuleCat PlumbingCoefficient) (ComplexShape.down ℕ) q

/-- The object at level `N` of the weight-sublevel homology diagram is the homology of the object
at level `N` of the weight-sublevel chain-complex diagram. -/
theorem latticeWeightSublevelHomologyFunctor_obj_eq_homology (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) (N : ℤ) :
    (P.latticeWeightSublevelHomologyFunctor k q).obj N =
      ((P.latticeWeightSublevelFunctor k).obj N).homology q := by
  unfold latticeWeightSublevelHomologyFunctor
  rfl

/-- The object at level `N` of the weight-sublevel homology diagram is the homology of the
level-`N` subcomplex. -/
@[simp]
theorem latticeWeightSublevelHomologyFunctor_obj (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) (N : ℤ) :
    (P.latticeWeightSublevelHomologyFunctor k q).obj N =
      P.latticeWeightSublevelHomology k N q := by
  exact (P.latticeWeightSublevelHomologyFunctor_obj_eq_homology k q N).trans
    ((congrArg (fun C : ChainComplex (ModuleCat PlumbingCoefficient) ℕ ↦ C.homology q)
      (P.latticeWeightSublevelFunctor_obj k N)).trans
        (P.latticeWeightSublevelHomology_def k N q).symm)

/-- The transition map on weight-sublevel homology is induced by the corresponding inclusion of
sublevel chain complexes. -/
theorem latticeWeightSublevelHomologyFunctor_map (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) {N M : ℤ} (f : N ⟶ M) :
    eqToHom (P.latticeWeightSublevelHomologyFunctor_obj_eq_homology k q N).symm ≫
        (P.latticeWeightSublevelHomologyFunctor k q).map f ≫
      eqToHom (P.latticeWeightSublevelHomologyFunctor_obj_eq_homology k q M) =
        HomologicalComplex.homologyMap ((P.latticeWeightSublevelFunctor k).map f) q := by
  exact (conj_eqToHom_iff_heq
    ((P.latticeWeightSublevelHomologyFunctor k q).map f)
    (HomologicalComplex.homologyMap ((P.latticeWeightSublevelFunctor k).map f) q)
    (P.latticeWeightSublevelHomologyFunctor_obj_eq_homology k q N)
    (P.latticeWeightSublevelHomologyFunctor_obj_eq_homology k q M)).2
      (by
        unfold latticeWeightSublevelHomologyFunctor
        rfl)

/-- The canonical cocone from weight-sublevel homology modules to the homology of the full lattice
chain complex. Its legs are the maps on homology induced by inclusion of sublevel complexes. -/
noncomputable def latticeWeightSublevelHomologyCocone (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) :
    Cocone (P.latticeWeightSublevelHomologyFunctor k q) :=
  (HomologicalComplex.homologyFunctor (ModuleCat PlumbingCoefficient)
    (ComplexShape.down ℕ) q).mapCocone (P.latticeWeightSublevelCocone k)

/-- The point of the weight-sublevel homology cocone is the homology of the point of the
weight-sublevel chain-complex cocone. -/
theorem latticeWeightSublevelHomologyCocone_pt_eq_homology (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) :
    (P.latticeWeightSublevelHomologyCocone k q).pt =
      (P.latticeWeightSublevelCocone k).pt.homology q := by
  unfold latticeWeightSublevelHomologyCocone
  rfl

/-- The point of the weight-sublevel homology cocone is the cubical-degree homology of the full
lattice chain complex. -/
@[simp]
theorem latticeWeightSublevelHomologyCocone_pt (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) :
    (P.latticeWeightSublevelHomologyCocone k q).pt = P.latticeChainHomology k q :=
  (P.latticeWeightSublevelHomologyCocone_pt_eq_homology k q).trans
    ((congrArg (fun C : ChainComplex (ModuleCat PlumbingCoefficient) ℕ ↦ C.homology q)
      (P.latticeWeightSublevelCocone_pt k)).trans
        (P.latticeChainHomology_def k q).symm)

/-- The leg at level `N` of the weight-sublevel homology cocone is the homology map induced by the
canonical inclusion into the full lattice chain complex. -/
theorem latticeWeightSublevelHomologyCocone_ι_app (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) (N : ℤ) :
    eqToHom (P.latticeWeightSublevelHomologyFunctor_obj_eq_homology k q N).symm ≫
        (P.latticeWeightSublevelHomologyCocone k q).ι.app N ≫
      eqToHom (P.latticeWeightSublevelHomologyCocone_pt_eq_homology k q) =
        HomologicalComplex.homologyMap ((P.latticeWeightSublevelCocone k).ι.app N) q := by
  exact (conj_eqToHom_iff_heq
    ((P.latticeWeightSublevelHomologyCocone k q).ι.app N)
    (HomologicalComplex.homologyMap ((P.latticeWeightSublevelCocone k).ι.app N) q)
    (P.latticeWeightSublevelHomologyFunctor_obj_eq_homology k q N)
    (P.latticeWeightSublevelHomologyCocone_pt_eq_homology k q)).2
      (by
        unfold latticeWeightSublevelHomologyCocone
        rfl)

/-- Cubical-degree lattice homology is the filtered colimit of the homology modules of the
characteristic-weight sublevel complexes. -/
noncomputable def latticeWeightSublevelHomologyCoconeIsColimit (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) :
    IsColimit (P.latticeWeightSublevelHomologyCocone k q) :=
  isColimitOfPreserves
    (HomologicalComplex.homologyFunctor (ModuleCat PlumbingCoefficient)
      (ComplexShape.down ℕ) q)
    (P.latticeWeightSublevelCoconeIsColimit k)

end PlumbingGraph

end TauCeti
