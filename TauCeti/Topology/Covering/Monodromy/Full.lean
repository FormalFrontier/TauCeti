/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Covering.Monodromy.Basic
public import TauCeti.Topology.Homotopy.Monodromy.Full

/-!
# Fullness of covering-space monodromy

When the base is locally path-connected, the monodromy functor from covering spaces to
fundamental-groupoid actions is full. The unbundled construction of the map between total spaces
is proved in `TauCeti.Topology.Homotopy.Monodromy.Full`; this file packages it for bundled covering
spaces.

## Main declaration

* `TauCeti.CoveringSpace.monodromyFunctor_full`: over a locally path-connected base, the
  monodromy functor on covering spaces is full.

## References

This packages the fullness step in the alternative monodromy-functor classification requested by
Stage 2, item 8 of `TauCetiRoadmap/UniversalCovers/README.md`.
-/

public section

open CategoryTheory
universe u

namespace TauCeti.CoveringSpace

variable {X : TopCat.{u}}

/-- Over a locally path-connected base, every natural transformation of monodromy functors is
induced by a map of covering spaces. -/
instance monodromyFunctor_full [LocallyPathConnectedSpace X] : (monodromyFunctor X).Full where
  map_surjective {p q} α := by
    -- Transport across the opaque functor's object equations for the unbundled theorem.
    let α' : p.isCoveringMap_proj.monodromyFunctor ⟶
        q.isCoveringMap_proj.monodromyFunctor :=
      cast (by rw [← monodromyFunctor_obj, ← monodromyFunctor_obj]) α
    have hα' : HEq α' α := cast_heq _ α
    obtain ⟨f, hf, hα⟩ := IsCoveringMap.exists_map_of_monodromyNatTrans
      p.isCoveringMap_proj q.isCoveringMap_proj α'
    let F : p ⟶ q := homMk (TopCat.ofHom f) (by
      ext e
      exact congrFun hf e)
    refine ⟨F, ?_⟩
    have hF : F.hom.left.hom = f := by
      simp only [F, homMk_hom_left, TopCat.hom_ofHom]
    have hmap :
      IsCoveringMap.monodromyNatTrans p.isCoveringMap_proj q.isCoveringMap_proj
          F.hom.left.hom (proj_hom_comp_hom_left_hom F) =
          α' := by
      calc
        IsCoveringMap.monodromyNatTrans p.isCoveringMap_proj q.isCoveringMap_proj
            F.hom.left.hom (proj_hom_comp_hom_left_hom F) =
            IsCoveringMap.monodromyNatTrans p.isCoveringMap_proj q.isCoveringMap_proj f hf := by
          ext ⟨x⟩ e
          obtain ⟨e, he⟩ := e
          rw [IsCoveringMap.monodromyNatTrans_app, IsCoveringMap.monodromyNatTrans_app]
          apply Subtype.ext
          calc
            (IsCoveringMap.fiberMap F.hom.left.hom (proj_hom_comp_hom_left_hom F) x ⟨e, he⟩ :
                (q : TopCat)) = F.hom.left.hom e :=
              IsCoveringMap.fiberMap_apply_coe F.hom.left.hom
                (proj_hom_comp_hom_left_hom F) x ⟨e, he⟩
            _ = f e := congrArg (fun k : C((p : TopCat), (q : TopCat)) ↦ k e) hF
            _ = (IsCoveringMap.fiberMap f hf x ⟨e, he⟩ : (q : TopCat)) :=
              (IsCoveringMap.fiberMap_apply_coe f hf x ⟨e, he⟩).symm
        _ = α' := hα
    exact eq_of_heq ((monodromyFunctor_map F).trans ((heq_of_eq hmap).trans hα'))

end TauCeti.CoveringSpace
