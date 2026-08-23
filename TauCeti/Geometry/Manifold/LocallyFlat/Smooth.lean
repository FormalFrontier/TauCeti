/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Smooth embeddings are locally flat

Local flatness (`TauCeti.IsLocallyFlat`) was isolated because topological embeddings can be wild:
the Alexander horned sphere is a topologically embedded `2`-sphere that no ambient chart flattens.
Smooth embeddings are never wild, and this file proves it: a `C^n` embedding of manifolds into a
boundaryless ambient manifold is locally flat, the complementary model space of the local flatness
being the complement supplied by the immersion.

The proof is the shrinking argument that the two hypotheses of `Manifold.IsSmoothEmbedding` are
there for. Being an immersion is already a normal-form statement in Mathlib: `f` is an immersion at
`x` when charts `φ` of the domain and `ψ` of the ambient space can be chosen around `x` and `f x`
so that in those charts `f` reads as the standard inclusion `u ↦ (u, 0)`, through a continuous
linear equivalence `(E × F) ≃L[𝕜] E'` of the ambient model space. Transporting `ψ` along that
equivalence gives an ambient chart valued in `E × F` carrying `f '' φ.source` into the standard
slice, so half of a slice chart comes for free. The other half — that the chart sees *nothing but*
the image on the slice — fails for that chart, and is what the shrinking supplies:

* the chart is cut down to the part of its source lying over the target of `φ`, which forces a
  point of the slice to be the image of a point of `φ.source`;
* the chart is cut down again to an open set meeting `Set.range f` only in `f '' φ.source`, which
  is where being a *topological embedding* enters, and without which a point of the slice could be
  the image of a far-away point of the domain. That is exactly what happens for the figure-eight
  immersion `t ↦ (sin 2t, sin t)` of the open interval `(-π, π)` into the plane: it is injective,
  the crossing point of the figure eight being attained only at `t = 0`, but the two ends `t → ±π`
  accumulate at that same crossing point, so no neighbourhood of it in the plane meets the image in
  a single arc, and no chart flattens the image there.

Only the ambient manifold has to be boundaryless, its charts being required to be homeomorphisms
onto open sets of the model space `E'`. The domain need not be: with boundary or corners in the
domain the same argument flattens the image onto `Set.range I ×ˢ {0}`, the standard slice cut down
to the range of the domain's model with corners. That is a slice embedding in the sense of
`TauCeti.IsSliceEmbedding`, and is local flatness exactly when the domain model is boundaryless.
The relative statement is the general one proved here, and local flatness of a smooth embedding is
read off it.

## Main results

* `TauCeti.exists_isSliceChart_of_isEmbedding_of_isImmersionAtOfComplement`: the slice chart at a
  point, the shrinking argument itself and the engine of the file.
* `TauCeti.IsSliceEmbedding.of_isImmersionOfComplement_of_isEmbedding`: a `C^n` immersion that is a
  topological embedding flattens its image onto `Set.range I ×ˢ {0}`, for a boundaryless ambient
  manifold and an arbitrary domain model with corners.
* `TauCeti.IsLocallyFlat.of_isImmersionOfComplement_of_isEmbedding` and
  `TauCeti.IsLocallyFlat.of_isSmoothEmbedding`: between boundaryless manifolds, a `C^n` embedding
  is locally flat, the complementary model being the complement of the immersion.
* `TauCeti.isLocallyClosed_range_of_isSmoothEmbedding`: the image of a `C^n` embedding into a
  boundaryless manifold is locally closed.
* `TauCeti.SmoothEmbedding.isLocallyFlat`: the same for the bundled smooth embeddings that the
  roadmap's geometric knot presentations are built from.
* `TauCeti.isOpenEmbedding_of_isImmersionOfComplement_of_isEmbedding` and
  `TauCeti.isLocallyFlat_subtypeVal`: the codimension-zero end, where local flatness is openness of
  the embedding.

## Implementation notes

The ambient chart produced here is an `OpenPartialHomeomorph N (E × F)` rather than a member of a
prescribed atlas, which is all `TauCeti.IsSliceChart` asks for. It is built from the immersion's
`Manifold.IsImmersionAtOfComplement.codChart`, which does lie in the maximal atlas, by
postcomposing with the homeomorphism `G ≃ₜ E'` of a boundaryless model with corners and with the
immersion's own linear equivalence `(E × F) ≃L[𝕜] E'`, and then restricting to an open set. Both
postcompositions are homeomorphisms, so the result is again a chart of the maximal topological
atlas.

Boundarylessness of the ambient manifold is used only through `ModelWithCorners.toHomeomorph`.
Without it, the ambient chart composed with the model is a `PartialEquiv` whose target is a piece
of a half-space rather than an open set, and the statement to prove would be one about a manifold
with boundary as ambient space, where flatness at a boundary point of the ambient space is a
genuinely different condition.

The immersion hypothesis is taken in the form `Manifold.IsImmersionOfComplement`, which fixes the
complement `F` globally, rather than `Manifold.IsImmersion`, which merely asserts one exists:
`TauCeti.IsLocallyFlat` names its complementary model space, so it needs a complement that does not
vary from point to point. The `Manifold.IsSmoothEmbedding` corollaries pass
`Manifold.IsImmersion.complement` for it.

## References

* R. Daverman and G. Venema, *Embeddings in Manifolds*, AMS Graduate Studies in Mathematics 106
  (2009), Chapter 1, where smooth submanifolds are the motivating example of local flatness.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1, for the local normal form
  of an immersion that Mathlib's `Manifold.IsImmersionAt` takes as its definition.
-/

public section

namespace TauCeti

open Manifold Set Topology

open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N}

/-- **The slice chart of a smooth embedding.** If `f` is a topological embedding and a `C^n`
immersion at `x` with complement `F`, then around `f x` there is a chart of the ambient manifold,
valued in the split model space `E × F`, carrying `Set.range f` exactly onto the slice
`Set.range I ×ˢ {0}`.

This is the content of the file; everything below is a specialisation of it. The immersion normal
form provides a chart in which `f '' h.domChart.source` lies on the slice, and the two restrictions
performed here cut that chart down until nothing else does: first to the part lying over the target
of the domain chart, so that a point of the slice is the image of a point of `h.domChart.source`,
and then to an open set meeting `Set.range f` only in `f '' h.domChart.source`, which exists
because `f` is an embedding. -/
theorem exists_isSliceChart_of_isEmbedding_of_isImmersionAtOfComplement [J.Boundaryless]
    (hf : IsEmbedding f) {x : M} (h : IsImmersionAtOfComplement F I J n f x) :
    ∃ Φ : OpenPartialHomeomorph N (E × F), f x ∈ Φ.source ∧
      IsSliceChart Φ (range I ×ˢ ({0} : Set F)) (range f) := by
  -- The ambient chart of the immersion, read in the splitting `E × F` of the ambient model space.
  set Ψ : OpenPartialHomeomorph N (E × F) :=
    h.codChart.transHomeomorph (J.toHomeomorph.trans h.equiv.toHomeomorph.symm) with hΨ
  have hΨ_apply : ∀ p : N, Ψ p = h.equiv.symm ((h.codChart.extend J) p) := fun p => by
    rw [hΨ, OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
      Homeomorph.trans_apply, ContinuousLinearEquiv.coe_symm_toHomeomorph,
      ModelWithCorners.toHomeomorph_apply, OpenPartialHomeomorph.extend_coe, Function.comp_apply]
  have hextend : ∀ y : M, (h.domChart.extend I) y = I (h.domChart y) := fun y => by
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply]
  -- In this chart the immersion normal form says that `f` is the standard inclusion.
  have key : ∀ y ∈ h.domChart.source, Ψ (f y) = ((h.domChart.extend I) y, 0) := by
    intro y hy
    have hy' : y ∈ (h.domChart.extend I).source := by rwa [h.domChart.extend_source]
    have hwritten := h.writtenInCharts ((h.domChart.extend I).map_source hy')
    simp only [Function.comp_apply, (h.domChart.extend I).left_inv hy'] at hwritten
    rw [hΨ_apply, hwritten, ContinuousLinearEquiv.symm_apply_apply]
  -- Because `f` is an embedding, an open set of `N` cuts `f '' h.domChart.source` out of the image.
  obtain ⟨W, hW, hWf⟩ := hf.isInducing.isOpen_iff.1 h.domChart.open_source
  have hmemW : ∀ y : M, f y ∈ W ↔ y ∈ h.domChart.source := fun y => by rw [← hWf]; exact Iff.rfl
  -- The part of the ambient model space lying over the target of the domain chart.
  have hU : IsOpen (I.symm ⁻¹' h.domChart.target) :=
    h.domChart.open_target.preimage I.continuous_symm
  set V : Set N :=
    (Ψ.source ∩ Ψ ⁻¹' ((I.symm ⁻¹' h.domChart.target) ×ˢ (univ : Set F))) ∩ W
  have hVopen : IsOpen V := (Ψ.isOpen_inter_preimage (hU.prod isOpen_univ)).inter hW
  -- The point `f x` survives both restrictions.
  have hx : x ∈ h.domChart.source := h.mem_domChart_source
  have hfx : f x ∈ Ψ.source := h.mem_codChart_source
  have hfxV : f x ∈ V := by
    refine ⟨⟨hfx, ?_⟩, (hmemW x).2 hx⟩
    rw [mem_preimage, key x hx]
    exact ⟨by rw [mem_preimage, hextend, I.left_inv]; exact h.domChart.map_source hx, mem_univ _⟩
  refine ⟨Ψ.restrOpen V hVopen, ⟨hfx, hfxV⟩, isSliceChart_iff.2 fun p hp => ?_⟩
  rw [OpenPartialHomeomorph.restrOpen_source] at hp
  simp only [OpenPartialHomeomorph.coe_restrOpen]
  constructor
  · -- A point of the image lying in `W` comes from the domain chart, hence lands on the slice.
    rintro ⟨y, rfl⟩
    have hy : y ∈ h.domChart.source := (hmemW y).1 hp.2.2
    rw [key y hy, hextend]
    exact ⟨mem_range_self _, rfl⟩
  · -- Conversely a point of the slice lying over the domain chart's target is such an image.
    intro hps
    have hmem : (Ψ p).1 ∈ (h.domChart.extend I).target := by
      rw [h.domChart.extend_target]
      exact ⟨hp.2.1.2.1, hps.1⟩
    have hys : (h.domChart.extend I).symm (Ψ p).1 ∈ h.domChart.source := by
      rw [← h.domChart.extend_source (I := I)]
      exact (h.domChart.extend I).map_target hmem
    have hfy : Ψ (f ((h.domChart.extend I).symm (Ψ p).1)) = Ψ p := by
      rw [key _ hys, (h.domChart.extend I).right_inv hmem, ← (hps.2 : (Ψ p).2 = 0)]
    exact ⟨_, Ψ.injOn (h.source_subset_preimage_source hys) hp.1 hfy⟩

/-- A `C^n` immersion with complement `F` that is a topological embedding flattens its image onto
the slice `Set.range I ×ˢ {0}` of the split ambient model space `E × F`.

Only the ambient manifold is assumed boundaryless. The domain may have boundary or corners, and
then its model cuts the slice down to `Set.range I ×ˢ {0}`, which is the honest local picture of,
say, a closed half-plane embedded in `ℝ³`. -/
theorem IsSliceEmbedding.of_isImmersionOfComplement_of_isEmbedding [J.Boundaryless]
    (h : IsImmersionOfComplement F I J n f) (hf : IsEmbedding f) :
    IsSliceEmbedding (range I ×ˢ ({0} : Set F)) f :=
  ⟨hf, fun x => exists_isSliceChart_of_isEmbedding_of_isImmersionAtOfComplement hf (h x)⟩

/-- **A smooth embedding of boundaryless manifolds is locally flat**, the complementary model space
of the local flatness being the complement `F` of the immersion. In particular a smooth embedding
is never wild: there is no smooth analogue of the Alexander horned sphere. -/
theorem IsLocallyFlat.of_isImmersionOfComplement_of_isEmbedding [I.Boundaryless] [J.Boundaryless]
    (h : IsImmersionOfComplement F I J n f) (hf : IsEmbedding f) : IsLocallyFlat E F f := by
  rw [isLocallyFlat_iff_isSliceEmbedding]
  have hslice := IsSliceEmbedding.of_isImmersionOfComplement_of_isEmbedding h hf
  rwa [I.range_eq_univ] at hslice

/-- A `C^n` embedding into a boundaryless manifold flattens its image onto `Set.range I ×ˢ {0}`,
the complementary model space being the complement carried by the immersion. -/
theorem IsSliceEmbedding.of_isSmoothEmbedding [J.Boundaryless] (h : IsSmoothEmbedding I J n f) :
    IsSliceEmbedding (range I ×ˢ ({0} : Set h.isImmersion.complement)) f :=
  .of_isImmersionOfComplement_of_isEmbedding h.isImmersion.isImmersionOfComplement_complement
    h.isEmbedding

/-- **A `C^n` embedding of boundaryless manifolds is locally flat.** This is the form the
geometric-topology roadmap asks for: the low-codimension subtleties of topological embeddings are
confined to `TauCeti.IsLocallyFlat`, and everything smooth satisfies it. The complementary model
space is the complement `Manifold.IsImmersion.complement` chosen by the immersion, playing the role
of the normal directions. -/
theorem IsLocallyFlat.of_isSmoothEmbedding [I.Boundaryless] [J.Boundaryless]
    (h : IsSmoothEmbedding I J n f) : IsLocallyFlat E h.isImmersion.complement f :=
  .of_isImmersionOfComplement_of_isEmbedding h.isImmersion.isImmersionOfComplement_complement
    h.isEmbedding

/-- The image of a `C^n` embedding into a boundaryless manifold is locally closed: it is closed in
some open neighbourhood of itself. This is inherited from the slice picture, the slice
`Set.range I ×ˢ {0}` being closed whatever the domain model, and is one of the properties a wild
embedding can fail. -/
theorem isLocallyClosed_range_of_isSmoothEmbedding [J.Boundaryless]
    (h : IsSmoothEmbedding I J n f) : IsLocallyClosed (range f) :=
  (IsSliceEmbedding.of_isSmoothEmbedding h).isLocallyClosed_range
    (I.isClosed_range.prod isClosed_singleton).isLocallyClosed

/-- A bundled smooth embedding of boundaryless manifolds is locally flat. This is the shape layer 4
of the geometric-topology roadmap consumes: a geometric knot presentation is a smooth embedding of
the circle into an ambient manifold, and this says it is in particular a locally flat topological
embedding, so the topological statements about it are not vacuous. -/
theorem SmoothEmbedding.isLocallyFlat [I.Boundaryless] [J.Boundaryless]
    (e : SmoothEmbedding I J n M N) : IsLocallyFlat E e.isImmersion.complement e :=
  IsLocallyFlat.of_isSmoothEmbedding e.isSmoothEmbedding

/-- **Codimension zero.** A `C^n` immersion with trivial complement which is a topological
embedding is an open embedding: with no normal directions left the slice is the whole model space,
so the flattening charts see nothing but the image. -/
theorem isOpenEmbedding_of_isImmersionOfComplement_of_isEmbedding [I.Boundaryless] [J.Boundaryless]
    [Subsingleton F] (h : IsImmersionOfComplement F I J n f) (hf : IsEmbedding f) :
    IsOpenEmbedding f := by
  have hzero : ({0} : Set F) = univ := eq_univ_of_forall fun y => Subsingleton.elim y 0
  have hslice : range I ×ˢ ({0} : Set F) = (univ : Set (E × F)) := by
    rw [I.range_eq_univ, hzero, univ_prod_univ]
  have hemb := IsSliceEmbedding.of_isImmersionOfComplement_of_isEmbedding h hf
  rw [hslice] at hemb
  exact hemb.isOpenEmbedding

/-- The inclusion of an open subset of a boundaryless manifold is locally flat with trivial
complementary model. This is the codimension-zero end of the predicate, and confirms against
`TauCeti.isLocallyFlat_iff_isOpenEmbedding` that the general theorem above is stated with the
conventions that make an open embedding flat rather than merely embedded. -/
theorem isLocallyFlat_subtypeVal (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) [I.Boundaryless]
    [IsManifold I n M] (s : TopologicalSpace.Opens M) :
    IsLocallyFlat E PUnit (Subtype.val : s → M) :=
  IsLocallyFlat.of_isImmersionOfComplement_of_isEmbedding (I := I) (J := I) (n := n)
    (IsImmersionOfComplement.of_opens s) IsEmbedding.subtypeVal

end TauCeti
