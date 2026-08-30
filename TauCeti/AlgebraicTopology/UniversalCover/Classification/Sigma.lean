/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.MonodromyEquivalence
public import TauCeti.Topology.Covering.Sigma
public import TauCeti.Topology.Homotopy.Sigma

/-!
# Covering spaces of a disjoint union are classified by their monodromy

Let `X i` be a family of path-connected, locally path-connected, semilocally simply connected
spaces. Their disjoint union is locally path connected but not path connected, so it falls
outside the standing hypotheses of `TauCeti.CoveringSpace.monodromyEquivalence`; this file proves
the classification for it anyway.

Only essential surjectivity has to be redone: monodromy is always faithful, and it is full over
any locally path-connected base. A functor `F` out of the fundamental groupoid of `Σ i, X i`
restricts along the inclusion of each summand, each restriction is the monodromy of a covering
space of that summand, and the disjoint union of those covering spaces is a covering space of
`Σ i, X i` whose monodromy is `F`. The comparison is natural because a path in a disjoint union
stays in the summand it starts in, so every morphism of the fundamental groupoid comes from a
single summand.

## Main declarations

* `TauCeti.sigmaMonodromyNatIso`: summandwise identifications of monodromy assemble into one
  over the disjoint union.
* `TauCeti.CoveringSpace.exists_monodromyFunctor_iso_sigma`: every functor out of the fundamental
  groupoid of a disjoint union is the monodromy of a covering space.
* `TauCeti.CoveringSpace.sigmaMonodromyEquivalence`: **covering spaces of a disjoint union of
  nice spaces are equivalent to functors from its fundamental groupoid to types.**

## References

This is the disconnected case of Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`, whose alternative lens asks for covers in general to
be described as functors out of the fundamental groupoid.
-/

public section
noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti

variable {ι : Type u} {E X : ι → Type u} [∀ i, TopologicalSpace (E i)]
  [∀ i, TopologicalSpace (X i)]

/-- **Summandwise identifications of monodromy assemble over a disjoint union.** If the monodromy
functor of `f i` is isomorphic to the restriction of `G` to the `i`-th summand for every `i`,
then the monodromy functor of the disjoint union of the `f i` is isomorphic to `G`. -/
def sigmaMonodromyNatIso (f : ∀ i, E i → X i)
    (hf : ∀ i, IsCoveringMap (f i)) (G : FundamentalGroupoid (Σ i, X i) ⥤ Type u)
    (e : ∀ i, (hf i).monodromyFunctor ≅
      FundamentalGroupoid.map (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(X i, Σ j, X j)) ⋙ G) :
    (isCoveringMap_sigmaMap f hf).monodromyFunctor ≅ G :=
  NatIso.ofComponents
    (fun z => (sigmaMapFiberEquiv f z.as.1 z.as.2).symm.toIso ≪≫
      (e z.as.1).app (FundamentalGroupoid.mk z.as.2))
    (by
      rintro ⟨⟨i', x⟩⟩ ⟨⟨i, y⟩⟩ m
      obtain rfl : i = i' := sigmaFst_eq_of_quotient m
      obtain ⟨γ, rfl⟩ := exists_quotient_map_sigmaMk_eq m
      refine ConcreteCategory.hom_ext _ _ fun p => ?_
      have h : (sigmaMapFiberEquiv f i y).symm
          ((isCoveringMap_sigmaMap f hf).monodromy
            (γ.map (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(X i, Σ j, X j))) p) =
            (hf i).monodromy γ ((sigmaMapFiberEquiv f i x).symm p) := by
        apply (sigmaMapFiberEquiv f i y).injective
        rw [Equiv.apply_symm_apply, ← monodromy_sigmaMap]
        exact congrArg _ (Equiv.apply_symm_apply (sigmaMapFiberEquiv f i x) p).symm
      exact (congrArg (fun w => (e i).hom.app (FundamentalGroupoid.mk y) w) h).trans
        (NatTrans.naturality_apply (e i).hom γ ((sigmaMapFiberEquiv f i x).symm p)))

variable [∀ i, PathConnectedSpace (X i)] [∀ i, LocallyPathConnectedSpace (X i)]
  [∀ i, SemilocallySimplyConnectedSpace (X i)]

namespace CoveringSpace

/-- **Every functor out of the fundamental groupoid of a disjoint union of nice spaces is the
monodromy of a covering space.** -/
theorem exists_monodromyFunctor_iso_sigma (F : FundamentalGroupoid (Σ i, X i) ⥤ Type u) :
    ∃ p : CoveringSpace (TopCat.of (Σ i, X i)),
      Nonempty ((monodromyFunctor (TopCat.of (Σ i, X i))).obj p ≅ F) := by
  choose q hq using fun i : ι => exists_monodromyFunctor_iso (X := TopCat.of (X i))
    (FundamentalGroupoid.map (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(X i, Σ j, X j)) ⋙ F)
  let f : ∀ i, ((q i : TopCat) : Type u) → X i := fun i => ⇑(q i).proj
  have hf : ∀ i, IsCoveringMap (f i) := fun i => (q i).isCoveringMap_proj
  let p : TopCat.of (Σ i, ((q i : TopCat) : Type u)) ⟶ TopCat.of (Σ i, X i) :=
    TopCat.ofHom ⟨Sigma.map id f, (isCoveringMap_sigmaMap f hf).continuous⟩
  let hp : IsCoveringMap p := isCoveringMap_sigmaMap f hf
  let Q : CoveringSpace (TopCat.of (Σ i, X i)) := mk p hp
  refine ⟨Q, ⟨?_⟩⟩
  let h : (Q : TopCat) ≃ₜ TopCat.of (Σ i, ((q i : TopCat) : Type u)) :=
    TopCat.homeoOfIso (eqToIso (mk_coe p hp))
  have hh : p.hom ∘ h = Q.proj.hom := by
    funext z
    have hproj := DFunLike.congr_fun (congrArg TopCat.Hom.hom (mk_proj p hp)) z
    exact hproj.symm
  exact eqToIso (monodromyFunctor_obj Q) ≪≫
    IsCoveringMap.monodromyNatIso Q.isCoveringMap_proj hp h hh ≪≫
      sigmaMonodromyNatIso f hf F fun i => (hq i).some

/-- **The classification of covering spaces of a disjoint union by fundamental-groupoid
actions.** Over a disjoint union of path-connected, locally path-connected, semilocally simply
connected spaces, monodromy is an equivalence from covering spaces to functors from the
fundamental groupoid to types. -/
def sigmaMonodromyEquivalence (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
    [∀ i, PathConnectedSpace (X i)] [∀ i, LocallyPathConnectedSpace (X i)]
    [∀ i, SemilocallySimplyConnectedSpace (X i)] :
    CoveringSpace (TopCat.of (Σ i, X i)) ≌ (FundamentalGroupoid (Σ i, X i) ⥤ Type u) :=
  haveI : (monodromyFunctor (TopCat.of (Σ i, X i))).Faithful :=
    monodromyFunctor_faithful (TopCat.of (Σ i, X i))
  haveI : (monodromyFunctor (TopCat.of (Σ i, X i))).Full := monodromyFunctor_full
  haveI : (monodromyFunctor (TopCat.of (Σ i, X i))).EssSurj :=
    ⟨fun F => exists_monodromyFunctor_iso_sigma F⟩
  haveI : (monodromyFunctor (TopCat.of (Σ i, X i))).IsEquivalence := {}
  (monodromyFunctor (TopCat.of (Σ i, X i))).asEquivalence

@[simp]
theorem sigmaMonodromyEquivalence_functor (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
    [∀ i, PathConnectedSpace (X i)] [∀ i, LocallyPathConnectedSpace (X i)]
    [∀ i, SemilocallySimplyConnectedSpace (X i)] :
    (sigmaMonodromyEquivalence X).functor = monodromyFunctor (TopCat.of (Σ i, X i)) :=
  (rfl)

end CoveringSpace

end TauCeti
