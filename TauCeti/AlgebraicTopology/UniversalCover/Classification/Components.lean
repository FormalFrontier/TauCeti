/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import TauCeti.AlgebraicTopology.PathComponent
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Sigma

/-!
# Covering spaces over a locally path-connected base

Let `X` be locally path-connected and semilocally simply connected, with no connectedness
assumption. Its connected components are open and coincide with its path components, so
`TauCeti.connectedComponentsSigmaHomeomorph` identifies `X` with the disjoint union of the
fibres of `X → ConnectedComponents X`. Each summand satisfies the standing hypotheses for the
universal-cover construction.

The disjoint-union classification in
`TauCeti.AlgebraicTopology.UniversalCover.Classification.Sigma` therefore applies. Composing the
resulting covering projection with the component homeomorphism gives a cover of `X`; monodromy
is transported by `IsCoveringMap.monodromyHomeomorphCompNatIso`. This proves essential
surjectivity over an arbitrary base. Fullness only needs local path-connectedness, and
faithfulness has no hypothesis, so monodromy is an equivalence.

## Main declarations

* `TauCeti.CoveringSpace.exists_monodromyFunctor_iso_of_locallyPathConnectedSpace`: every functor
  from the fundamental groupoid of `X` to types is the monodromy of a covering space.
* `TauCeti.CoveringSpace.monodromyEquivalenceOfLocallyPathConnectedSpace`: **covering spaces over
  a locally path-connected, semilocally simply connected base are equivalent to functors from
  its fundamental groupoid to types.**

## References

This closes the disconnected-cover part of Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`. It consumes the based-path universal-cover
construction adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292), and the
disjoint-union classification already built from it. The mathematical classification follows
Hatcher, *Algebraic Topology*, Section 1.3; no external formalization is copied or adapted here.
-/

public section
noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti.CoveringSpace

variable {X : Type u} [TopologicalSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

private abbrev Component (C : ConnectedComponents X) :=
  (ConnectedComponents.mk ⁻¹' {C} : Set X)

/-- **Every fundamental-groupoid action over a locally path-connected, semilocally simply
connected base is the monodromy of a covering space.** No connectedness hypothesis is imposed on
the base. -/
theorem exists_monodromyFunctor_iso_of_locallyPathConnectedSpace
    (F : FundamentalGroupoid X ⥤ Type u) :
    ∃ p : CoveringSpace (TopCat.of X), Nonempty ((monodromyFunctor (TopCat.of X)).obj p ≅ F) := by
  let h : (Σ C : ConnectedComponents X, Component C) ≃ₜ X :=
    connectedComponentsSigmaHomeomorph
  let hMap : C((Σ C : ConnectedComponents X, Component C), X) := h
  choose q hq using exists_monodromyFunctor_iso_sigma
    (ι := ConnectedComponents X)
    (X := fun C : ConnectedComponents X ↦
      (ConnectedComponents.mk ⁻¹' {C} : Set X))
    (FundamentalGroupoid.map hMap ⋙ F)
  let hp : IsCoveringMap (h ∘ q.proj) := q.isCoveringMap_proj.homeomorph_comp h
  let pMap : TopCat.of ((q : TopCat) : Type u) ⟶ TopCat.of X :=
    TopCat.ofHom ⟨h ∘ q.proj, hp.continuous⟩
  let p : CoveringSpace (TopCat.of X) := mk pMap hp
  refine ⟨p, ⟨?_⟩⟩
  let totalHomeomorph : (p : TopCat) ≃ₜ (q : TopCat) :=
    TopCat.homeoOfIso (eqToIso (mk_coe pMap hp))
  have htotal : (h ∘ q.proj) ∘ totalHomeomorph = p.proj := by
    funext z
    have hproj := DFunLike.congr_fun (congrArg TopCat.Hom.hom (mk_proj pMap hp)) z
    exact hproj.symm
  let qIso : q.isCoveringMap_proj.monodromyFunctor ≅
      FundamentalGroupoid.map hMap ⋙ F :=
    eqToIso (monodromyFunctor_obj q).symm ≪≫ hq.some
  let componentEquivalence :=
    FundamentalGroupoidFunctor.equivOfHomotopyEquiv h.toHomotopyEquiv
  exact eqToIso (monodromyFunctor_obj p) ≪≫
    IsCoveringMap.monodromyNatIso p.isCoveringMap_proj hp totalHomeomorph htotal ≪≫
    q.isCoveringMap_proj.monodromyHomeomorphCompNatIso h ≪≫
    Functor.isoWhiskerLeft (FundamentalGroupoid.map (h.symm : C(X, _))) qIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight componentEquivalence.counitIso F ≪≫
    Functor.leftUnitor F

/-- **Classification of covering spaces over an arbitrary locally path-connected, semilocally
simply connected base.** Monodromy is an equivalence from covering spaces over `X` to functors
from the fundamental groupoid of `X` to types. -/
def monodromyEquivalenceOfLocallyPathConnectedSpace (X : Type u) [TopologicalSpace X]
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] :
    CoveringSpace (TopCat.of X) ≌ (FundamentalGroupoid X ⥤ Type u) :=
  haveI : (monodromyFunctor (TopCat.of X)).Faithful :=
    monodromyFunctor_faithful (TopCat.of X)
  haveI : (monodromyFunctor (TopCat.of X)).Full := monodromyFunctor_full
  haveI : (monodromyFunctor (TopCat.of X)).EssSurj :=
    ⟨fun F ↦ exists_monodromyFunctor_iso_of_locallyPathConnectedSpace F⟩
  haveI : (monodromyFunctor (TopCat.of X)).IsEquivalence := {}
  (monodromyFunctor (TopCat.of X)).asEquivalence

@[simp]
theorem monodromyEquivalenceOfLocallyPathConnectedSpace_functor (X : Type u)
    [TopologicalSpace X] [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] :
    (monodromyEquivalenceOfLocallyPathConnectedSpace X).functor =
      monodromyFunctor (TopCat.of X) :=
  (rfl)

end TauCeti.CoveringSpace
