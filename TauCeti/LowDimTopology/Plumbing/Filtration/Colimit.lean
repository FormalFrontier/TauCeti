/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import TauCeti.Algebra.Category.ModuleCat.DirectedUnion
public import TauCeti.LowDimTopology.Plumbing.Filtration.Basic

/-!
# The lattice chain complex as a filtered colimit

For a plumbing graph `P` and characteristic covector `k`, the characteristic-weight sublevel
complexes form an increasing diagram indexed by `ℤ`. This file compares that diagram with the
untruncated lattice chain complex. The canonical map from each sublevel is inclusion on every
cubical-degree chain group, and these maps form a cocone.

The weight filtration is exhaustive in every cubical degree. We use the universal property of a
directed supremum of submodules to prove that the cocone is a colimit degreewise, then apply
Mathlib's pointwise criterion for colimits of homological complexes. Thus the full lattice chain
complex is canonically the filtered colimit of its weight truncations.

This is the chain-level direct-limit presentation used to pass finite sublevel computations to
the full lattice complex. Passing this colimit through homology is a subsequent step.

## Main definitions

* `TauCeti.PlumbingGraph.latticeWeightSublevelToChainComplex`: inclusion of a weight sublevel into
  the full lattice chain complex.
* `TauCeti.PlumbingGraph.latticeWeightSublevelCocone`: the resulting cocone over all levels.
* `TauCeti.PlumbingGraph.latticeWeightSublevelCoconeIsColimit`: the full lattice chain complex is
  the colimit of its weight sublevels.

## References

This advances `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane L, which asks for
Némethi's lattice homology from lattice points and weight functions. The filtration by
sublevel cubical complexes follows A. Némethi,
[arXiv:0709.0841](https://arxiv.org/abs/0709.0841), Section 3.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

namespace PlumbingGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The inclusion of a characteristic-weight sublevel complex into the untruncated lattice chain
complex. -/
noncomputable def latticeWeightSublevelToChainComplex (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) :
    P.latticeWeightSublevelComplex k N ⟶ P.latticeChainComplex k :=
  ChainComplex.ofHom
    (fun q ↦ eqToHom (P.latticeWeightSublevelComplex_X k N q) ≫
      ModuleCat.ofHom (Submodule.inclusion
        (PlumbingChain.characteristicWeightDegreePart_le_degreePart P k N q)) ≫
      eqToHom (P.latticeChainComplex_X k q).symm)
    (fun q ↦ by
      rw [P.latticeWeightSublevelComplex_d k N q, P.latticeChainComplex_d k q]
      simp only [Category.assoc]
      apply (cancel_epi (eqToHom (P.latticeWeightSublevelComplex_X k N (q + 1)))).2
      simp only [← Category.assoc]
      apply (cancel_mono (eqToHom (P.latticeChainComplex_X k q).symm)).2
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
      exact congrArg ModuleCat.ofHom (P.latticeDifferentialDegree_comp_inclusion k N q))

/-- The component of the sublevel-to-full-complex map is inclusion of the corresponding filtered
degree part. -/
theorem latticeWeightSublevelToChainComplex_f (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ) :
    (P.latticeWeightSublevelToChainComplex k N).f q =
      eqToHom (P.latticeWeightSublevelComplex_X k N q) ≫
        ModuleCat.ofHom (Submodule.inclusion
          (PlumbingChain.characteristicWeightDegreePart_le_degreePart P k N q)) ≫
          eqToHom (P.latticeChainComplex_X k q).symm := by
  unfold latticeWeightSublevelToChainComplex
  rfl

/-- Applied to a chain, the sublevel-to-full-complex map is the inclusion of the filtered degree
part into the cubical-degree part. -/
@[simp]
theorem latticeWeightSublevelToChainComplex_apply (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) (q : ℕ)
    (c : (P.latticeWeightSublevelComplex k N).X q) :
    eqToHom (P.latticeChainComplex_X k q)
        ((P.latticeWeightSublevelToChainComplex k N).f q c) =
      ModuleCat.ofHom (Submodule.inclusion
        (PlumbingChain.characteristicWeightDegreePart_le_degreePart P k N q))
          (eqToHom (P.latticeWeightSublevelComplex_X k N q) c) := by
  rw [← CategoryTheory.comp_apply, latticeWeightSublevelToChainComplex_f]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    CategoryTheory.comp_apply]

/-- Inclusion of weight sublevels into the full lattice complex commutes with increasing the
weight bound. -/
theorem latticeWeightSublevelInclusion_comp_toChainComplex (P : PlumbingGraph V)
    (k : P.characteristicVectors) {N M : ℤ} (hNM : N ≤ M) :
    P.latticeWeightSublevelInclusion k hNM ≫
        P.latticeWeightSublevelToChainComplex k M =
      P.latticeWeightSublevelToChainComplex k N := by
  apply HomologicalComplex.hom_ext
  intro q
  apply (cancel_mono (eqToHom (P.latticeChainComplex_X k q))).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rw [HomologicalComplex.comp_f, latticeWeightSublevelInclusion_f,
    latticeWeightSublevelToChainComplex_f, latticeWeightSublevelToChainComplex_f]
  simp only [Category.assoc]
  simp only [eqToHom_trans, eqToHom_refl, Category.comp_id, eqToHom_trans_assoc,
    Category.id_comp, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply]
  apply Subtype.ext
  rfl

/-- The cocone from all characteristic-weight sublevel complexes to the full lattice chain
complex. -/
noncomputable def latticeWeightSublevelCocone (P : PlumbingGraph V)
    (k : P.characteristicVectors) : Cocone (P.latticeWeightSublevelFunctor k) :=
  Cocone.mk (P.latticeChainComplex k)
    { app := fun N ↦ eqToHom (P.latticeWeightSublevelFunctor_obj k N) ≫
        P.latticeWeightSublevelToChainComplex k N
      naturality := fun N M f ↦ by
        simp only [Functor.const_obj_map]
        rw [← cancel_epi (eqToHom (P.latticeWeightSublevelFunctor_obj k N).symm)]
        rw [reassoc_of% (P.latticeWeightSublevelFunctor_map k f),
          P.latticeWeightSublevelInclusion_comp_toChainComplex k (leOfHom f)]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        exact (Category.comp_id _).symm }

/-- The point of the weight-sublevel cocone is the full lattice chain complex. -/
@[simp]
theorem latticeWeightSublevelCocone_pt (P : PlumbingGraph V)
    (k : P.characteristicVectors) :
    (P.latticeWeightSublevelCocone k).pt = P.latticeChainComplex k :=
  (rfl)

/-- The leg from level `N` of the weight-sublevel cocone is the canonical inclusion into the full
lattice chain complex. -/
@[simp]
theorem latticeWeightSublevelCocone_ι_app (P : PlumbingGraph V)
    (k : P.characteristicVectors) (N : ℤ) :
    (P.latticeWeightSublevelCocone k).ι.app N =
      eqToHom (P.latticeWeightSublevelFunctor_obj k N) ≫
        P.latticeWeightSublevelToChainComplex k N ≫
          eqToHom (P.latticeWeightSublevelCocone_pt k).symm :=
  by
    -- Proof irrelevance makes the final self-transport the identity, and composition with that
    -- identity reduces through the `HomologicalComplex` and `ModuleCat` wrappers.
    rfl

private noncomputable abbrev latticeWeightDegreeFunctor (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) : Functor ℤ (ModuleCat PlumbingCoefficient) :=
  ModuleCat.submoduleFunctor
    (fun N : ℤ ↦ PlumbingChain.characteristicWeightDegreePart P k N q)
    (fun _ _ h ↦ PlumbingChain.characteristicWeightDegreePart_mono P k h q)

private theorem latticeWeightDegreeFunctor_obj_eq (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) (N : ℤ) :
    (P.latticeWeightDegreeFunctor k q).obj N = ModuleCat.of PlumbingCoefficient
      (PlumbingChain.characteristicWeightDegreePart P k N q) :=
  ModuleCat.submoduleFunctor_obj
    (fun N : ℤ ↦ PlumbingChain.characteristicWeightDegreePart P k N q)
    (fun _ _ h ↦ PlumbingChain.characteristicWeightDegreePart_mono P k h q) N

private noncomputable abbrev latticeWeightDegreeCocone (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) : Cocone (P.latticeWeightDegreeFunctor k q) :=
  ModuleCat.submoduleCocone
    (fun N : ℤ ↦ PlumbingChain.characteristicWeightDegreePart P k N q)
    (fun _ _ h ↦ PlumbingChain.characteristicWeightDegreePart_mono P k h q)
    (PlumbingChain.degreePart V q)
    (PlumbingChain.iSup_characteristicWeightDegreePart_eq_degreePart P k q)

private theorem latticeWeightDegreeCocone_pt_eq (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) :
    (P.latticeWeightDegreeCocone k q).pt =
      ModuleCat.of PlumbingCoefficient (PlumbingChain.degreePart V q) :=
  ModuleCat.submoduleCocone_pt
    (fun N : ℤ ↦ PlumbingChain.characteristicWeightDegreePart P k N q)
    (fun _ _ h ↦ PlumbingChain.characteristicWeightDegreePart_mono P k h q)
    (PlumbingChain.degreePart V q)
    (PlumbingChain.iSup_characteristicWeightDegreePart_eq_degreePart P k q)

private theorem latticeWeightDegreeCocone_ι_app_eq (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) (N : ℤ) :
    eqToHom (P.latticeWeightDegreeFunctor_obj_eq k q N).symm ≫
        (P.latticeWeightDegreeCocone k q).ι.app N ≫
      eqToHom (P.latticeWeightDegreeCocone_pt_eq k q) =
        ModuleCat.ofHom (Submodule.inclusion
          (PlumbingChain.characteristicWeightDegreePart_le_degreePart P k N q)) :=
  ModuleCat.submoduleCocone_ι_app
    (fun N : ℤ ↦ PlumbingChain.characteristicWeightDegreePart P k N q)
    (fun _ _ h ↦ PlumbingChain.characteristicWeightDegreePart_mono P k h q)
    (PlumbingChain.degreePart V q)
    (PlumbingChain.iSup_characteristicWeightDegreePart_eq_degreePart P k q) N

private theorem latticeWeightSublevelEval_obj_eq (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) (N : ℤ) :
    ((P.latticeWeightSublevelFunctor k ⋙
      HomologicalComplex.eval (ModuleCat PlumbingCoefficient) (ComplexShape.down ℕ) q).obj N) =
        (P.latticeWeightDegreeFunctor k q).obj N := by
  calc
    _ = ((P.latticeWeightSublevelFunctor k).obj N).X q := rfl
    _ = (P.latticeWeightSublevelComplex k N).X q := congrArg
      (fun C : ChainComplex (ModuleCat PlumbingCoefficient) ℕ ↦ C.X q)
      (P.latticeWeightSublevelFunctor_obj k N)
    _ = ModuleCat.of PlumbingCoefficient
        (PlumbingChain.characteristicWeightDegreePart P k N q) :=
      P.latticeWeightSublevelComplex_X k N q
    _ = _ := (P.latticeWeightDegreeFunctor_obj_eq k q N).symm

private theorem latticeWeightSublevelEval_map (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) {N M : ℤ} (f : N ⟶ M) :
    eqToHom (P.latticeWeightSublevelEval_obj_eq k q N).symm ≫
        ((P.latticeWeightSublevelFunctor k).map f).f q ≫
      eqToHom (P.latticeWeightSublevelEval_obj_eq k q M) =
        (P.latticeWeightDegreeFunctor k q).map f := by
  have hq := congrArg (fun φ ↦ φ.f q) (P.latticeWeightSublevelFunctor_map k f)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f,
    latticeWeightSublevelInclusion_f] at hq
  let inc : ModuleCat.of PlumbingCoefficient
        (PlumbingChain.characteristicWeightDegreePart P k N q) ⟶
      ModuleCat.of PlumbingCoefficient
        (PlumbingChain.characteristicWeightDegreePart P k M q) :=
    ModuleCat.ofHom (Submodule.inclusion
      (PlumbingChain.characteristicWeightDegreePart_mono P k (leOfHom f) q))
  have hmap : ((P.latticeWeightSublevelFunctor k).map f).f q ≍ inc := by
    dsimp only [inc]
    simpa only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] using heq_of_eq hq
  have hdegree : inc ≍ (P.latticeWeightDegreeFunctor k q).map f :=
    (conj_eqToHom_iff_heq
      inc
      ((P.latticeWeightDegreeFunctor k q).map f)
      (P.latticeWeightDegreeFunctor_obj_eq k q N).symm
      (P.latticeWeightDegreeFunctor_obj_eq k q M).symm).1
      (ModuleCat.submoduleFunctor_map
        (fun N : ℤ ↦ PlumbingChain.characteristicWeightDegreePart P k N q)
        (fun _ _ h ↦ PlumbingChain.characteristicWeightDegreePart_mono P k h q) f).symm
  exact ((conj_eqToHom_iff_heq
    ((P.latticeWeightDegreeFunctor k q).map f)
    (((P.latticeWeightSublevelFunctor k).map f).f q)
    (P.latticeWeightSublevelEval_obj_eq k q N).symm
    (P.latticeWeightSublevelEval_obj_eq k q M).symm).2
      (hdegree.symm.trans hmap.symm)).symm

private noncomputable def latticeWeightSublevelEvalIso (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) :
    P.latticeWeightSublevelFunctor k ⋙
        HomologicalComplex.eval (ModuleCat PlumbingCoefficient) (ComplexShape.down ℕ) q ≅
      P.latticeWeightDegreeFunctor k q :=
  NatIso.ofComponents (fun N ↦ eqToIso (P.latticeWeightSublevelEval_obj_eq k q N))
    (fun {N M} f ↦ by
      rw [← cancel_epi (eqToHom (P.latticeWeightSublevelEval_obj_eq k q N).symm)]
      simp only [Functor.comp_map, HomologicalComplex.eval_map, eqToIso.hom]
      rw [P.latticeWeightSublevelEval_map k q f]
      simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp])

private theorem latticeWeightSublevelEvalCocone_pt_eq (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) :
    ((Cocone.precompose (P.latticeWeightSublevelEvalIso k q).inv).obj
      ((HomologicalComplex.eval (ModuleCat PlumbingCoefficient) (ComplexShape.down ℕ) q)
        |>.mapCocone (P.latticeWeightSublevelCocone k))).pt =
      (P.latticeWeightDegreeCocone k q).pt := by
  calc
    _ = ((P.latticeWeightSublevelCocone k).pt).X q := rfl
    _ = (P.latticeChainComplex k).X q := congrArg
      (fun C : ChainComplex (ModuleCat PlumbingCoefficient) ℕ ↦ C.X q)
      (P.latticeWeightSublevelCocone_pt k)
    _ = ModuleCat.of PlumbingCoefficient (PlumbingChain.degreePart V q) :=
      P.latticeChainComplex_X k q
    _ = _ := (P.latticeWeightDegreeCocone_pt_eq k q).symm

private theorem latticeWeightSublevelEvalCocone_ι_app_eq (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) (N : ℤ) :
    eqToHom (P.latticeWeightDegreeFunctor_obj_eq k q N).symm ≫
        ((Cocone.precompose (P.latticeWeightSublevelEvalIso k q).inv).obj
          ((HomologicalComplex.eval (ModuleCat PlumbingCoefficient) (ComplexShape.down ℕ) q)
            |>.mapCocone (P.latticeWeightSublevelCocone k))).ι.app N ≫
      eqToHom ((P.latticeWeightSublevelEvalCocone_pt_eq k q).trans
        (P.latticeWeightDegreeCocone_pt_eq k q)) =
        ModuleCat.ofHom (Submodule.inclusion
          (PlumbingChain.characteristicWeightDegreePart_le_degreePart P k N q)) := by
  let inc : ModuleCat.of PlumbingCoefficient
        (PlumbingChain.characteristicWeightDegreePart P k N q) ⟶
      ModuleCat.of PlumbingCoefficient (PlumbingChain.degreePart V q) :=
    ModuleCat.ofHom (Submodule.inclusion
      (PlumbingChain.characteristicWeightDegreePart_le_degreePart P k N q))
  symm
  apply (conj_eqToHom_iff_heq
    inc
    (((Cocone.precompose (P.latticeWeightSublevelEvalIso k q).inv).obj
      ((HomologicalComplex.eval (ModuleCat PlumbingCoefficient) (ComplexShape.down ℕ) q)
        |>.mapCocone (P.latticeWeightSublevelCocone k))).ι.app N)
    (P.latticeWeightDegreeFunctor_obj_eq k q N).symm
    ((P.latticeWeightSublevelEvalCocone_pt_eq k q).trans
      (P.latticeWeightDegreeCocone_pt_eq k q)).symm).2
  simp only [Cocone.precompose_obj_ι, NatTrans.comp_app, Functor.mapCocone_ι_app,
    Functor.comp_obj, HomologicalComplex.eval_obj, latticeWeightSublevelCocone_ι_app,
    latticeWeightSublevelEvalIso, NatIso.ofComponents_inv_app, eqToIso.inv,
    HomologicalComplex.eval_map, HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f,
    latticeWeightSublevelToChainComplex_f]
  simp only [heq_eqToHom_comp_iff, heq_comp_eqToHom_iff, inc]
  apply heq_of_eq
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

private noncomputable def latticeWeightSublevelEvalCoconeIso (P : PlumbingGraph V)
    (k : P.characteristicVectors) (q : ℕ) :
    (Cocone.precompose (P.latticeWeightSublevelEvalIso k q).inv).obj
        ((HomologicalComplex.eval (ModuleCat PlumbingCoefficient) (ComplexShape.down ℕ) q)
          |>.mapCocone (P.latticeWeightSublevelCocone k)) ≅
      P.latticeWeightDegreeCocone k q :=
  Cocone.ext (eqToIso (P.latticeWeightSublevelEvalCocone_pt_eq k q)) fun N => by
    rw [← cancel_epi (eqToHom (P.latticeWeightDegreeFunctor_obj_eq k q N).symm)]
    rw [← cancel_mono (eqToHom (P.latticeWeightDegreeCocone_pt_eq k q))]
    simp only [Category.assoc]
    rw [P.latticeWeightDegreeCocone_ι_app_eq k q N]
    simpa only [eqToIso.hom, eqToHom_trans] using
      P.latticeWeightSublevelEvalCocone_ι_app_eq k q N

/-- The untruncated lattice chain complex is the colimit of its characteristic-weight sublevel
complexes. -/
noncomputable def latticeWeightSublevelCoconeIsColimit (P : PlumbingGraph V)
    (k : P.characteristicVectors) : IsColimit (P.latticeWeightSublevelCocone k) :=
  HomologicalComplex.isColimitOfEval _ _ fun q ↦
    (IsColimit.equivOfNatIsoOfIso (P.latticeWeightSublevelEvalIso k q)
      ((HomologicalComplex.eval (ModuleCat PlumbingCoefficient) (ComplexShape.down ℕ) q)
        |>.mapCocone (P.latticeWeightSublevelCocone k))
      (P.latticeWeightDegreeCocone k q)
      (P.latticeWeightSublevelEvalCoconeIso k q)).symm
        (ModuleCat.submoduleCoconeIsColimit
          (fun N : ℤ ↦ PlumbingChain.characteristicWeightDegreePart P k N q)
          (fun _ _ h ↦ PlumbingChain.characteristicWeightDegreePart_mono P k h q)
          (PlumbingChain.degreePart V q)
          (PlumbingChain.iSup_characteristicWeightDegreePart_eq_degreePart P k q))

end PlumbingGraph

end TauCeti
