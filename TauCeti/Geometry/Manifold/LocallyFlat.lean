/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.LocallyClosed

/-!
# Locally flat embeddings

Topological manifolds admit embeddings that no smooth embedding can imitate: the Alexander horned
sphere is a topologically embedded `2`-sphere in `S³` bounding a non-simply-connected region, and a
wild arc in `ℝ³` is knotted although its domain is an interval. Theorems about topological
manifolds therefore quantify over *locally flat* embeddings, those that in suitable ambient charts
look like a fixed slice of the model space.

This file introduces that notion and the structural API it is used through. The definition is split
into two layers.

* `TauCeti.IsSliceChart φ S A` says that a single chart `φ` of the ambient space flattens the set
  `A` onto the model slice `S`, in the sense that `φ '' (φ.source ∩ A) = φ.target ∩ S`.
* `TauCeti.IsLocallyFlat S f` says that `f` is a topological embedding admitting a slice chart for
  `Set.range f` around every point of its image.

Local flatness is a local condition, so the load-bearing content is not the definition but its
closure properties: restriction to an open subset of the domain, locality, invariance under
homeomorphisms and open embeddings on either side, invariance under a change of model space, and
products. Those are proved here, together with two results that pin the notion down: in codimension
zero (`S = Set.univ`) local flatness is exactly openness of the embedding, and a locally flat
embedding with a closed model slice has locally closed image.

The slice `S` is a parameter rather than a fixed coordinate subspace, deliberately: codimension `0`
(open embeddings), codimension `1` (where collaring lives) and codimension `2` (where knotting
lives) behave very differently, and keeping one predicate for all of them is the point.
`TauCeti.isLocallyFlat_prodMkLeft` records the standard model, the inclusion `X → X × Y`,
`x ↦ (x, c)`, whose slice is `Set.univ ×ˢ {c}`; taking `X = ℝⁿ` and `Y = ℝᵏ` gives the usual
`ℝⁿ ⊆ ℝⁿ⁺ᵏ` picture.

This is layer 2 of the geometric-topology roadmap, the substrate for topologically locally flat
discs (topological sliceness) and for stating the annulus conjecture.

## Main definitions

* `TauCeti.IsSliceChart`: an ambient chart flattening a set onto a model slice.
* `TauCeti.IsLocallyFlat`: a topological embedding that is flat in ambient charts.

## Main results

* `TauCeti.isSliceChart_iff`: a chart is a slice chart iff, on its source, membership in the set is
  read off as membership of the coordinates in the slice.
* `TauCeti.IsLocallyFlat.restrict` and `TauCeti.isLocallyFlat_iff_forall_exists_isOpen`: local
  flatness is a local property of the domain.
* `TauCeti.IsLocallyFlat.comp_isOpenEmbedding`, `TauCeti.IsLocallyFlat.of_comp_isOpenEmbedding`,
  `TauCeti.IsLocallyFlat.codRestrict`, `TauCeti.IsLocallyFlat.homeomorph_comp`,
  `TauCeti.IsLocallyFlat.comp_homeomorph`: invariance under open embeddings and homeomorphisms of
  the ambient space and of the domain.
* `TauCeti.IsLocallyFlat.transHomeomorph`: invariance under a homeomorphic change of model space.
* `TauCeti.IsLocallyFlat.prodMap`: a product of locally flat embeddings is locally flat.
* `TauCeti.isLocallyFlat_univ_iff`: in codimension zero, locally flat means open.
* `TauCeti.IsLocallyFlat.isLocallyClosed_range`: a closed slice forces a locally closed image.

## Implementation notes

No membership in a prescribed atlas is required of the flattening chart: an
`OpenPartialHomeomorph M F` is automatically a chart of the maximal topological atlas of a
topological manifold `M` modelled on `F`, so demanding atlas membership would be redundant there
and would needlessly restrict the definition on ambient spaces that are not manifolds.

A slice chart is only asked to flatten the set *relative to its own target*, that is
`φ '' (φ.source ∩ A) = φ.target ∩ S` rather than `φ.target = F` together with
`φ '' (φ.source ∩ A) = S`. The relative form is the one that is genuinely local, hence the one
closed under restriction; the textbook form is not, since shrinking the source shrinks the target.
For the standard model, a chart in the relative sense can be shrunk to a ball around the point and
rescaled onto `(ℝᵐ, ℝⁿ)`, recovering the textbook form, but that comparison needs the linear
structure and is not formalised here.

Codimension is not baked into the definition; see the module docstring above.

The pair `(F, S)` is the *local model*, and it is an argument of the predicate rather than
something `IsLocallyFlat` picks: `IsLocallyFlat S f` asserts flatness against the model the caller
names, so a statement about locally flat embeddings fixes that model, as
`TauCeti.isLocallyFlat_prodMkLeft` fixes the standard slice `Set.univ ×ˢ {c}`. Degenerate models
are cheap, as they are for `ChartedSpace`: Mathlib's `chartedSpaceSelf` charts every space on itself
through the identity, and in the same way `F = M`, `S = Set.range f` and
`OpenPartialHomeomorph.refl M` flatten any embedding at all. As with `ChartedSpace`, the content
is in the model being the standard one, and the predicate has teeth once it is fixed:
`TauCeti.isLocallyFlat_univ_iff` says that for `S = Set.univ` exactly the open embeddings are
flat, and `TauCeti.IsLocallyFlat.isLocallyClosed_range` rules out an image that is not locally
closed whenever `S` is closed.

Composing two locally flat embeddings `N ↪ M ↪ P` is deliberately absent: it is not a formal
consequence of the definition, because the two flattening charts have to be made compatible before
they can be combined. Only the codimension-zero ambient case is proved here, as
`TauCeti.IsLocallyFlat.comp_isOpenEmbedding` and its converse.

## References

* R. Daverman and G. Venema, *Embeddings in Manifolds*, AMS Graduate Studies in Mathematics 106
  (2009), Chapter 1, for local flatness and wild embeddings.
* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341, for the collaring theorem that local flatness was isolated to prove.
-/

public section

namespace TauCeti

open Set Topology

variable {M N N' P F F' : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace N']
  [TopologicalSpace P] [TopologicalSpace F] [TopologicalSpace F']

/-- `IsSliceChart φ S A` says that the ambient chart `φ` flattens the set `A` onto the model slice
`S`: the chart carries the part of `A` it sees exactly onto the part of `S` in its target. -/
def IsSliceChart (φ : OpenPartialHomeomorph M F) (S : Set F) (A : Set M) : Prop :=
  φ '' (φ.source ∩ A) = φ.target ∩ S

variable {φ : OpenPartialHomeomorph M F} {S : Set F} {A : Set M}

/-- A chart is a slice chart for `A` exactly when, on its source, membership in `A` can be read off
as membership of the coordinates in the slice. This pointwise form is how the predicate is used. -/
theorem isSliceChart_iff :
    IsSliceChart φ S A ↔ ∀ y ∈ φ.source, (y ∈ A ↔ φ y ∈ S) := by
  constructor
  · intro h y hy
    constructor
    · intro hyA
      exact (h ▸ mem_image_of_mem _ ⟨hy, hyA⟩ : φ y ∈ φ.target ∩ S).2
    · intro hyS
      have hmem : φ y ∈ φ.target ∩ S := ⟨φ.map_source hy, hyS⟩
      rw [← h] at hmem
      obtain ⟨z, hz, hzy⟩ := hmem
      exact φ.injOn hz.1 hy hzy ▸ hz.2
  · intro h
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨y, ⟨hy, hyA⟩, rfl⟩
      exact ⟨φ.map_source hy, (h y hy).1 hyA⟩
    · rintro z ⟨hz, hzS⟩
      refine ⟨φ.symm z, ⟨φ.map_target hz, ?_⟩, φ.right_inv hz⟩
      rw [h _ (φ.map_target hz), φ.right_inv hz]
      exact hzS

namespace IsSliceChart

theorem mem_iff (h : IsSliceChart φ S A) {y : M} (hy : y ∈ φ.source) : y ∈ A ↔ φ y ∈ S :=
  isSliceChart_iff.1 h y hy

/-- On the source of a slice chart, the flattened set is cut out by the slice. -/
theorem source_inter_eq (h : IsSliceChart φ S A) : φ.source ∩ A = φ.source ∩ φ ⁻¹' S :=
  Set.ext fun _ => and_congr_right fun hy => h.mem_iff hy

/-- Restricting a slice chart to an open set restricts the flattened set to the same open set. -/
theorem restrOpen (h : IsSliceChart φ S A) {V : Set M} (hV : IsOpen V) :
    IsSliceChart (φ.restrOpen V hV) S (A ∩ V) := by
  refine isSliceChart_iff.2 fun y hy => ?_
  rw [OpenPartialHomeomorph.restrOpen_source] at hy
  simp only [OpenPartialHomeomorph.coe_restrOpen, mem_inter_iff, hy.2, and_true]
  exact h.mem_iff hy.1

/-- Conversely, a chart flattening `A ∩ V` for an open `V` restricts to a chart flattening `A`. -/
theorem of_inter {V : Set M} (h : IsSliceChart φ S (A ∩ V)) (hV : IsOpen V) :
    IsSliceChart (φ.restrOpen V hV) S A := by
  refine isSliceChart_iff.2 fun y hy => ?_
  rw [OpenPartialHomeomorph.restrOpen_source] at hy
  simp only [OpenPartialHomeomorph.coe_restrOpen]
  rw [← h.mem_iff hy.1, mem_inter_iff, and_iff_left hy.2]

/-- Slice charts pull back along any chart of a second ambient space. This is the single
transport lemma behind invariance under open embeddings and homeomorphisms. -/
theorem comp (h : IsSliceChart φ S A) (e : OpenPartialHomeomorph P M) :
    IsSliceChart (e.trans φ) S (e.source ∩ e ⁻¹' A) := by
  refine isSliceChart_iff.2 fun p hp => ?_
  rw [OpenPartialHomeomorph.trans_source] at hp
  rw [OpenPartialHomeomorph.trans_apply, ← h.mem_iff hp.2, mem_inter_iff, mem_preimage,
    and_iff_right hp.1]

/-- Composing a slice chart with a homeomorphism of the model space transports the slice. -/
theorem transHomeomorph (h : IsSliceChart φ S A) (e : F ≃ₜ F') :
    IsSliceChart (φ.trans e.toOpenPartialHomeomorph) (e '' S) A := by
  refine isSliceChart_iff.2 fun y hy => ?_
  rw [OpenPartialHomeomorph.trans_source] at hy
  rw [OpenPartialHomeomorph.trans_apply, h.mem_iff hy.1]
  simp

/-- The product of two slice charts is a slice chart for the product slice. -/
theorem prod {ψ : OpenPartialHomeomorph N F'} {S' : Set F'} {B : Set N}
    (h : IsSliceChart φ S A) (h' : IsSliceChart ψ S' B) :
    IsSliceChart (φ.prod ψ) (S ×ˢ S') (A ×ˢ B) := by
  refine isSliceChart_iff.2 fun p hp => ?_
  rw [OpenPartialHomeomorph.prod_source] at hp
  rw [OpenPartialHomeomorph.prod_apply, mem_prod, mem_prod, h.mem_iff hp.1, h'.mem_iff hp.2]

end IsSliceChart

/-- A chart is a slice chart for the full model space exactly when everything it sees lies in the
set: this is the codimension-zero case. -/
theorem isSliceChart_univ_iff : IsSliceChart φ (univ : Set F) A ↔ φ.source ⊆ A := by
  simp [isSliceChart_iff, subset_def]

/-- A topological embedding `f : N → M` is *locally flat* with model slice `S ⊆ F` if around every
point of its image there is a chart of `M` with values in the model space `F` carrying the image of
`f` onto `S`. For a topological manifold `M` modelled on `F` and a locally flat embedding of an
`n`-manifold in codimension `k`, `S` is a coordinate `ℝⁿ ⊆ ℝⁿ⁺ᵏ`. -/
structure IsLocallyFlat (S : Set F) (f : N → M) : Prop where
  /-- A locally flat map is in particular a topological embedding. -/
  isEmbedding : IsEmbedding f
  /-- Around every point of the image there is a chart flattening the image onto the slice. -/
  exists_isSliceChart : ∀ x : N, ∃ φ : OpenPartialHomeomorph M F,
    f x ∈ φ.source ∧ IsSliceChart φ S (range f)

variable {f : N → M}

namespace IsLocallyFlat

theorem continuous (h : IsLocallyFlat S f) : Continuous f :=
  h.isEmbedding.continuous

theorem injective (h : IsLocallyFlat S f) : Function.Injective f :=
  h.isEmbedding.injective

/-- Local flatness is inherited by the restriction to an open subset of the domain. -/
theorem restrict (h : IsLocallyFlat S f) {U : Set N} (hU : IsOpen U) :
    IsLocallyFlat S (f ∘ ((↑) : U → N)) := by
  obtain ⟨V, hV, rfl⟩ := h.isEmbedding.isInducing.isOpen_iff.1 hU
  have hrange : range (f ∘ ((↑) : (f ⁻¹' V) → N)) = range f ∩ V := by
    rw [range_comp, Subtype.range_coe, image_preimage_eq_inter_range, inter_comm]
  refine ⟨h.isEmbedding.comp IsEmbedding.subtypeVal, fun x => ?_⟩
  obtain ⟨φ, hφx, hφ⟩ := h.exists_isSliceChart x
  refine ⟨φ.restrOpen V hV, ?_, ?_⟩
  · exact ⟨hφx, x.2⟩
  · rw [hrange]
    exact hφ.restrOpen hV

/-- Local flatness is a local property of the domain: if every point of `N` has an open
neighbourhood on which the restriction of `f` is locally flat, then `f` is locally flat. -/
theorem of_forall_exists_isOpen (hf : IsEmbedding f)
    (h : ∀ x : N, ∃ U : Set N, IsOpen U ∧ x ∈ U ∧ IsLocallyFlat S (f ∘ ((↑) : U → N))) :
    IsLocallyFlat S f := by
  refine ⟨hf, fun x => ?_⟩
  obtain ⟨U, hU, hxU, hflat⟩ := h x
  obtain ⟨V, hV, rfl⟩ := hf.isInducing.isOpen_iff.1 hU
  obtain ⟨φ, hφx, hφ⟩ := hflat.exists_isSliceChart ⟨x, hxU⟩
  rw [range_comp, Subtype.range_coe, image_preimage_eq_inter_range, inter_comm] at hφ
  exact ⟨φ.restrOpen V hV, ⟨hφx, hxU⟩, hφ.of_inter hV⟩

/-- Local flatness is invariant under precomposition with a homeomorphism of the domain. -/
theorem comp_homeomorph (h : IsLocallyFlat S f) (e : N' ≃ₜ N) : IsLocallyFlat S (f ∘ e) := by
  refine ⟨h.isEmbedding.comp e.isEmbedding, fun x => ?_⟩
  obtain ⟨φ, hφx, hφ⟩ := h.exists_isSliceChart (e x)
  exact ⟨φ, hφx, by rwa [range_comp, e.surjective.range_eq, image_univ]⟩

/-- Pushing a locally flat embedding forward along an open embedding of the ambient space keeps it
locally flat. Taking `g` the inclusion of an open subset, this is the statement that a locally flat
embedding into an open subset is locally flat into the whole space. -/
theorem comp_isOpenEmbedding {g : M → P} (h : IsLocallyFlat S f) (hg : IsOpenEmbedding g) :
    IsLocallyFlat S (g ∘ f) := by
  refine ⟨hg.isEmbedding.comp h.isEmbedding, fun x => ?_⟩
  have : Nonempty M := ⟨f x⟩
  obtain ⟨φ, hφx, hφ⟩ := h.exists_isSliceChart x
  set e := (hg.toOpenPartialHomeomorph g).symm with he
  have hsource : e.source = range g := by simp [he]
  have hsymm : ∀ y : M, e (g y) = y := fun y => hg.toOpenPartialHomeomorph_left_inv g
  have hset : e.source ∩ e ⁻¹' range f = range (g ∘ f) := by
    ext p
    simp only [hsource, mem_inter_iff, mem_preimage, range_comp]
    constructor
    · rintro ⟨⟨y, rfl⟩, hy⟩
      exact mem_image_of_mem g (by rwa [hsymm] at hy)
    · rintro ⟨y, hy, rfl⟩
      exact ⟨mem_range_self y, by rwa [hsymm]⟩
  refine ⟨e.trans φ, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hsource ▸ mem_range_self (f x),
      by simpa only [mem_preimage, Function.comp_apply, hsymm] using hφx⟩
  · simpa only [hset] using hφ.comp e

/-- Conversely, an embedding that becomes locally flat after an open embedding of the ambient space
was already locally flat. Taking `g` the inclusion of an open subset, this corestricts a locally
flat embedding to an open neighbourhood of its image. -/
theorem of_comp_isOpenEmbedding {g : M → P} (hg : IsOpenEmbedding g)
    (h : IsLocallyFlat S (g ∘ f)) : IsLocallyFlat S f := by
  refine ⟨hg.isEmbedding.of_comp_iff.1 h.isEmbedding, fun x => ?_⟩
  have : Nonempty M := ⟨f x⟩
  obtain ⟨ψ, hψx, hψ⟩ := h.exists_isSliceChart x
  set e := hg.toOpenPartialHomeomorph g with he
  have hsource : e.source = univ := by simp [he]
  have happly : ∀ y : M, e y = g y := fun y => congrFun (hg.toOpenPartialHomeomorph_apply g) y
  have hset : e.source ∩ e ⁻¹' range (g ∘ f) = range f := by
    ext y
    simp only [hsource, univ_inter, mem_preimage, happly, range_comp,
      hg.injective.mem_set_image]
  refine ⟨e.trans ψ, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hsource ▸ mem_univ _,
      by simpa only [mem_preimage, happly, Function.comp_apply] using hψx⟩
  · simpa only [hset] using hψ.comp e

/-- Corestriction: a locally flat embedding whose image lies in an open subset `V` of the ambient
space is locally flat as a map into `V`. -/
theorem codRestrict (h : IsLocallyFlat S f) {V : Set M} (hV : IsOpen V) (hf : ∀ x, f x ∈ V) :
    IsLocallyFlat S (fun x => (⟨f x, hf x⟩ : V)) :=
  of_comp_isOpenEmbedding hV.isOpenEmbedding_subtypeVal h

/-- Local flatness is invariant under a homeomorphism of the ambient space. -/
theorem homeomorph_comp (h : IsLocallyFlat S f) (e : M ≃ₜ P) : IsLocallyFlat S (e ∘ f) :=
  h.comp_isOpenEmbedding e.isOpenEmbedding

/-- Local flatness only depends on the model space up to homeomorphism, the slice being transported
along. -/
theorem transHomeomorph (h : IsLocallyFlat S f) (e : F ≃ₜ F') : IsLocallyFlat (e '' S) f := by
  refine ⟨h.isEmbedding, fun x => ?_⟩
  obtain ⟨φ, hφx, hφ⟩ := h.exists_isSliceChart x
  refine ⟨φ.trans e.toOpenPartialHomeomorph, ?_, hφ.transHomeomorph e⟩
  rw [OpenPartialHomeomorph.trans_source]
  simpa using hφx

/-- A product of locally flat embeddings is locally flat, with the product slice: a product of
slice charts is a slice chart. -/
theorem prodMap {S' : Set F'} {g : N' → P} (h : IsLocallyFlat S f) (h' : IsLocallyFlat S' g) :
    IsLocallyFlat (S ×ˢ S') (Prod.map f g) := by
  refine ⟨h.isEmbedding.prodMap h'.isEmbedding, fun x => ?_⟩
  obtain ⟨φ, hφx, hφ⟩ := h.exists_isSliceChart x.1
  obtain ⟨ψ, hψx, hψ⟩ := h'.exists_isSliceChart x.2
  refine ⟨φ.prod ψ, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.prod_source]
    exact ⟨hφx, hψx⟩
  · rw [range_prodMap]
    exact hφ.prod hψ

/-- A locally flat embedding in codimension zero is an open embedding. -/
theorem isOpenEmbedding (h : IsLocallyFlat (univ : Set F) f) : IsOpenEmbedding f := by
  refine ⟨h.isEmbedding, isOpen_iff_mem_nhds.2 ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨φ, hφx, hφ⟩ := h.exists_isSliceChart x
  exact Filter.mem_of_superset (φ.open_source.mem_nhds hφx) (isSliceChart_univ_iff.1 hφ)

/-- The image of a locally flat embedding is locally closed as soon as the model slice is closed.
This is where the definition has teeth: the image of a wild embedding need not be locally closed in
any chart in this way. -/
theorem isLocallyClosed_range (h : IsLocallyFlat S f) (hS : IsClosed S) :
    IsLocallyClosed (range f) := by
  refine ((isLocallyClosed_tfae (range f)).out 2 0).1 ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨φ, hφx, hφ⟩ := h.exists_isSliceChart x
  refine ⟨φ.source, φ.open_source.mem_nhds hφx, ?_⟩
  have hpre : ((Subtype.val : φ.source → M) ⁻¹' range f) = (fun y : φ.source => φ ↑y) ⁻¹' S := by
    ext y
    exact hφ.mem_iff y.2
  change IsClosed ((Subtype.val : φ.source → M) ⁻¹' range f)
  rw [hpre]
  exact hS.preimage φ.continuousOn.domRestrict

end IsLocallyFlat

/-- Local flatness is exactly a local property of the domain. -/
theorem isLocallyFlat_iff_forall_exists_isOpen :
    IsLocallyFlat S f ↔ IsEmbedding f ∧
      ∀ x : N, ∃ U : Set N, IsOpen U ∧ x ∈ U ∧ IsLocallyFlat S (f ∘ ((↑) : U → N)) :=
  ⟨fun h => ⟨h.isEmbedding, fun x => ⟨univ, isOpen_univ, mem_univ x, h.restrict isOpen_univ⟩⟩,
    fun h => .of_forall_exists_isOpen h.1 h.2⟩

/-- An open embedding into a space charted on `F` is locally flat with the full model space as
slice. -/
theorem isLocallyFlat_univ_of_isOpenEmbedding [ChartedSpace F M] (h : IsOpenEmbedding f) :
    IsLocallyFlat (univ : Set F) f := by
  refine ⟨h.isEmbedding, fun x => ?_⟩
  refine ⟨(chartAt F (f x)).restrOpen (range f) h.isOpen_range,
    ⟨mem_chart_source F (f x), mem_range_self x⟩, ?_⟩
  exact isSliceChart_univ_iff.2 fun _ hy => hy.2

/-- Codimension zero: a map into a space charted on `F` is locally flat with slice the whole model
space exactly when it is an open embedding. -/
theorem isLocallyFlat_univ_iff [ChartedSpace F M] :
    IsLocallyFlat (univ : Set F) f ↔ IsOpenEmbedding f :=
  ⟨IsLocallyFlat.isOpenEmbedding, isLocallyFlat_univ_of_isOpenEmbedding⟩

/-- The standard local model: the inclusion of `F` as the slice `F × {c}` of `F × F'` is locally
flat. With `F = ℝⁿ` and `F' = ℝᵏ` this is the coordinate slice `ℝⁿ ⊆ ℝⁿ⁺ᵏ` that local flatness
is modelled on. -/
theorem isLocallyFlat_prodMkLeft (c : F') :
    IsLocallyFlat ((univ : Set F) ×ˢ ({c} : Set F')) (fun x : F => (x, c)) := by
  have hrange : (range fun x : F => (x, c)) = (univ : Set F) ×ˢ ({c} : Set F') := by
    ext p
    simp [Prod.ext_iff, eq_comm]
  refine ⟨isEmbedding_prodMkLeft c, fun x => ⟨OpenPartialHomeomorph.refl (F × F'), mem_univ _, ?_⟩⟩
  rw [hrange]
  exact isSliceChart_iff.2 fun y _ => Iff.rfl

end TauCeti
