/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.LocallyClosed

/-!
# Locally flat embeddings

Topological manifolds admit embeddings that no smooth embedding can imitate: the Alexander horned
sphere is a topologically embedded `2`-sphere in `S³` bounding a non-simply-connected region, and a
wild arc in `ℝ³` is knotted although its domain is an interval. Theorems about topological
manifolds therefore quantify over *locally flat* embeddings, those that in suitable ambient charts
look like the standard coordinate slice.

This file introduces that notion and the structural API it is used through. The definition is built
in three layers.

* `TauCeti.IsSliceChart φ S A` says that a single chart `φ` of the ambient space flattens the set
  `A` onto the model slice `S`, in the sense that `φ '' (φ.source ∩ A) = φ.target ∩ S`.
* `TauCeti.IsSliceEmbedding S f` says that `f` is a topological embedding admitting a slice chart
  for `Set.range f` around every point of its image. Here `S` is an arbitrary subset of an
  arbitrary model space, so this is *not* local flatness; it is the transport layer on which the
  closure properties are proved, and it is stated relatively so that they can be.
* `TauCeti.IsLocallyFlat F F' f` is local flatness proper: it is `IsSliceEmbedding` for the
  *standard coordinate slice* `F × {0}` of the model space `F × F'`, so ambient charts take values
  in `F × F'` and carry the image of `f` exactly onto the vanishing locus of the last `F'`
  coordinates. With `F = ℝⁿ` and `F' = ℝᵏ` this is the textbook `ℝⁿ × {0} ⊆ ℝⁿ⁺ᵏ`.

Codimension is not baked in: it is the choice of the complementary model `F'`, so codimension `0`
(`F'` a subsingleton, where local flatness is openness of the embedding), codimension `1` (where
collaring lives) and codimension `2` (where knotting lives) are all instances of the one predicate,
which is the point.

Local flatness is a local condition, so the load-bearing content is not the definition but its
closure properties: restriction to an open subset of the domain, locality, invariance under
homeomorphisms and open embeddings on either side, invariance under a change of model space, and
products. Those are proved here, together with two results that pin the notion down: in codimension
zero local flatness is exactly openness of the embedding, and a locally flat embedding has locally
closed image as soon as the origin of the complementary model is closed (on the relative layer, as
soon as the model slice is locally closed).

This is layer 2 of the geometric-topology roadmap, the substrate for topologically locally flat
discs (topological sliceness) and for stating the annulus conjecture.

## Main definitions

* `TauCeti.IsSliceChart`: an ambient chart flattening a set onto a model slice.
* `TauCeti.IsSliceEmbedding`: an embedding flattened onto a given model slice by ambient charts.
* `TauCeti.IsLocallyFlat`: a locally flat embedding, the case of the standard coordinate slice.

## Main results

* `TauCeti.isSliceChart_iff`: a chart is a slice chart iff, on its source, membership in the set is
  read off as membership of the coordinates in the slice.
* `TauCeti.IsSliceChart.exists_target_eq`: a slice chart can be shrunk to have any prescribed open
  subset of its target as its target.
* `TauCeti.isLocallyFlat_iff_isSliceEmbedding`, `TauCeti.isLocallyFlat_iff` and
  `TauCeti.IsLocallyFlat.exists_isSliceChart`: the defining flattening charts, as the slice
  embedding for the standard slice, in pointwise form, and as an eliminator.
* `TauCeti.IsLocallyFlat.restrict` and `TauCeti.IsLocallyFlat.of_forall_exists_isOpen`: local
  flatness is a local property of the domain.
* `TauCeti.IsLocallyFlat.isOpenEmbedding_comp`, `TauCeti.IsLocallyFlat.of_isOpenEmbedding_comp`,
  `TauCeti.IsLocallyFlat.codRestrict`, `TauCeti.IsLocallyFlat.homeomorph_comp`,
  `TauCeti.IsLocallyFlat.comp_isOpenEmbedding`, `TauCeti.IsLocallyFlat.comp_homeomorph`: invariance
  under open embeddings and homeomorphisms of the ambient space and of the domain.
* `TauCeti.IsSliceEmbedding.transHomeomorph`: invariance under a homeomorphic change of model
  space.
* `TauCeti.IsLocallyFlat.comp`: a composite of locally flat embeddings is locally flat, under an
  explicit hypothesis that their flattening charts can be chosen compatibly, and
  `TauCeti.IsLocallyFlat.of_compatible_isSliceChart`, the form of it that assumes only the
  compatible pair of charts.
* `TauCeti.IsLocallyFlat.prodMap`: a product of locally flat embeddings is locally flat.
* `TauCeti.isLocallyFlat_iff_isOpenEmbedding`: in codimension zero, locally flat means open.
* `TauCeti.IsLocallyFlat.isLocallyClosed_range`: a locally flat image is locally closed, as soon as
  the origin of the complementary model is closed.
* `TauCeti.isLocallyFlat_prodMkLeft`: over a domain charted on `F`, the standard model
  `x ↦ (x, 0)` is locally flat.
* `TauCeti.IsLocallyFlat.exists_isOpenEmbedding_prod`: a locally flat embedding with normed
  complementary model has local product neighbourhoods.

## Implementation notes

The relative predicate `IsSliceEmbedding` is deliberately *not* the definition of local flatness,
and is not a substitute for it: its slice is an arbitrary subset of an arbitrary space, so taking
the model space to be `M` itself, the slice to be `Set.range f` and the chart to be
`OpenPartialHomeomorph.refl M` makes every embedding, wild ones included, a slice embedding. It is
the layer on which transport is proved, because the closure properties genuinely need a slice that
varies (a product of standard slices is a standard slice only after a permutation of coordinates,
which is where `IsSliceEmbedding.transHomeomorph` is used). Local flatness is
`IsLocallyFlat F F' f`, which fixes the slice to be the standard one, and that predicate does have
teeth: `TauCeti.isLocallyFlat_iff_isOpenEmbedding` shows that in codimension zero it is equivalent
to openness of the embedding, and `TauCeti.IsLocallyFlat.isLocallyClosed_range` rules out an image
that is not locally closed, which the horned sphere's complement-side wildness aside is already
enough to exclude embeddings no chart can flatten.

No membership in a prescribed atlas is required of the flattening chart: an
`OpenPartialHomeomorph M (F × F')` is automatically a chart of the maximal topological atlas of a
topological manifold `M` modelled on `F × F'`, so demanding atlas membership would be redundant
there and would needlessly restrict the definition on ambient spaces that are not manifolds. The
model-space data enters exactly as it does for `ChartedSpace`, through the codomain of the charts.

A slice chart is only asked to flatten the set *relative to its own target*, that is
`φ '' (φ.source ∩ A) = φ.target ∩ S` rather than `φ.target = F` together with
`φ '' (φ.source ∩ A) = S`. The relative form is the one that is genuinely local, hence the one
closed under restriction; the textbook form is not, since shrinking the source shrinks the target.
For the standard model, a chart in the relative sense can be shrunk to a ball around the point and
rescaled onto `(ℝᵐ, ℝⁿ)`, recovering the textbook form, but that comparison needs the linear
structure and is not formalised here.

Composing two locally flat embeddings `N ↪ M ↪ P` is not a formal consequence of the definition:
the chart of `M` flattening the inner embedding and the chart of `P` flattening the outer one are
chosen independently, and nothing makes them agree. `TauCeti.IsLocallyFlat.comp` therefore carries
that agreement as an explicit hypothesis on charts witnessing the local flatness of the two
factors — the outer chart reads the intermediate coordinates off the inner one along `g` — rather
than assuming the conclusion; the outer chart then flattens the composite, and the complementary
models multiply. Composition comes in two levels, because a witnessing chart can only be referred
to by exhibiting it, so the compatibility hypothesis necessarily re-exhibits the two charts and
thereby already carries the flattening content of the two factors. `TauCeti.IsLocallyFlat.comp` is
the statement in the shape it is used and read, with both factors locally flat;
`TauCeti.IsLocallyFlat.of_compatible_isSliceChart` is what its proof actually consumes, a
compatible pair of charts around each point together with the embedding content of the conclusion
itself, and `comp` is a two-line consequence of it. There the compatibility hypothesis is kept down
to the part not already implied by the rest of it: the outer chart is only asked to detect
`range g` in one direction, the other direction and the fact that the inner chart is a chart around
`f x` both following from the agreement of the two charts together with injectivity of the outer
map. Both are stated only for the standard slice, since the compatibility condition refers to the
splitting `F × F'` of the intermediate model, which the relative layer does not have. The ambient
codimension-zero case needs no such hypothesis and is kept separate, as
`TauCeti.IsLocallyFlat.isOpenEmbedding_comp` and its converse.

## References

* R. Daverman and G. Venema, *Embeddings in Manifolds*, AMS Graduate Studies in Mathematics 106
  (2009), Chapter 1, for local flatness and wild embeddings.
* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341, for the collaring theorem that local flatness was isolated to prove.
-/

public section

namespace TauCeti

open Metric Set Topology

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

/-- On the source of a slice chart, membership in the flattened set is membership of the
coordinates in the model slice. This is the pointwise form of `TauCeti.isSliceChart_iff` in the
shape proofs use it, as an elimination rule at a single point. -/
theorem mem_iff (h : IsSliceChart φ S A) {y : M} (hy : y ∈ φ.source) : y ∈ A ↔ φ y ∈ S :=
  isSliceChart_iff.1 h y hy

/-- On the source of a slice chart, the flattened set is cut out by the slice. -/
theorem source_inter_eq (h : IsSliceChart φ S A) : φ.source ∩ A = φ.source ∩ φ ⁻¹' S :=
  Set.ext fun _ => and_congr_right fun hy => h.mem_iff hy

/-- A slice chart can be shrunk so that its target becomes a prescribed open subset of the old
target, without changing the map. -/
theorem exists_target_eq (h : IsSliceChart φ S A) {T : Set F} (hT : IsOpen T)
    (hTφ : T ⊆ φ.target) :
    ∃ ψ : OpenPartialHomeomorph M F, ⇑ψ = ⇑φ ∧ ψ.source = φ.source ∩ φ ⁻¹' T ∧ ψ.target = T ∧
      IsSliceChart ψ S A := by
  refine ⟨φ.restrOpen (φ.source ∩ φ ⁻¹' T) (φ.isOpen_inter_preimage hT), rfl, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source, inter_eq_right.2 inter_subset_left]
  · ext z
    simp only [OpenPartialHomeomorph.restrOpen_toPartialEquiv, PartialEquiv.restr_target,
      mem_inter_iff, mem_preimage, OpenPartialHomeomorph.coe_toPartialEquiv_symm]
    refine ⟨fun hz => ?_, fun hz => ⟨hTφ hz, φ.map_target (hTφ hz), ?_⟩⟩
    · have := hz.2.2
      rwa [φ.right_inv hz.1] at this
    · rw [φ.right_inv (hTφ hz)]
      exact hz
  · refine isSliceChart_iff.2 fun y hy => ?_
    rw [OpenPartialHomeomorph.restrOpen_source] at hy
    exact h.mem_iff hy.1

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
@[simp]
theorem isSliceChart_univ_iff : IsSliceChart φ (univ : Set F) A ↔ φ.source ⊆ A := by
  simp [isSliceChart_iff, subset_def]

/-- A topological embedding `f : N → M` is a *slice embedding* for the model slice `S ⊆ F` if
around every point of its image there is a chart of `M` with values in the model space `F` carrying
the image of `f` onto `S`.

This is a relative notion: `S` is arbitrary, so it is not local flatness, which is the case of the
standard slice, `TauCeti.IsLocallyFlat`. It is the layer the transport lemmas are proved on, since
they move the slice around. -/
structure IsSliceEmbedding (S : Set F) (f : N → M) : Prop where
  /-- A slice embedding is in particular a topological embedding. -/
  isEmbedding : IsEmbedding f
  /-- Around every point of the image there is a chart flattening the image onto the slice. -/
  exists_isSliceChart : ∀ x : N, ∃ φ : OpenPartialHomeomorph M F,
    f x ∈ φ.source ∧ IsSliceChart φ S (range f)

variable (F F') in
/-- A topological embedding `f : N → M` is *locally flat* with model `F × F'` if around every point
of its image there is a chart of `M` with values in `F × F'` carrying the image of `f` onto the
standard coordinate slice `F × {0}`.

For `M` a topological manifold modelled on `F × F'` and `N` one modelled on `F` this is the usual
condition that `f` looks like `ℝⁿ × {0} ⊆ ℝⁿ⁺ᵏ` in ambient charts; the codimension is the choice of
the complementary model `F'`, and is not otherwise constrained. -/
def IsLocallyFlat [Zero F'] (f : N → M) : Prop :=
  IsSliceEmbedding ((univ : Set F) ×ˢ ({0} : Set F')) f

variable {f : N → M}

namespace IsSliceEmbedding

theorem continuous (h : IsSliceEmbedding S f) : Continuous f :=
  h.isEmbedding.continuous

theorem injective (h : IsSliceEmbedding S f) : Function.Injective f :=
  h.isEmbedding.injective

/-- Being a slice embedding is inherited by the restriction to an open subset of the domain. -/
theorem restrict (h : IsSliceEmbedding S f) {U : Set N} (hU : IsOpen U) :
    IsSliceEmbedding S (f ∘ ((↑) : U → N)) := by
  obtain ⟨V, hV, rfl⟩ := h.isEmbedding.isInducing.isOpen_iff.1 hU
  have hrange : range (f ∘ ((↑) : (f ⁻¹' V) → N)) = range f ∩ V := by
    rw [range_comp, Subtype.range_coe, image_preimage_eq_inter_range, inter_comm]
  refine ⟨h.isEmbedding.comp IsEmbedding.subtypeVal, fun x => ?_⟩
  obtain ⟨φ, hφx, hφ⟩ := h.exists_isSliceChart x
  refine ⟨φ.restrOpen V hV, ?_, ?_⟩
  · exact ⟨hφx, x.2⟩
  · rw [hrange]
    exact hφ.restrOpen hV

/-- Being a slice embedding is a local property of the domain: if every point of `N` has an open
neighbourhood on which the restriction of `f` is a slice embedding, then `f` is one. -/
theorem of_forall_exists_isOpen (hf : IsEmbedding f)
    (h : ∀ x : N, ∃ U : Set N, IsOpen U ∧ x ∈ U ∧ IsSliceEmbedding S (f ∘ ((↑) : U → N))) :
    IsSliceEmbedding S f := by
  refine ⟨hf, fun x => ?_⟩
  obtain ⟨U, hU, hxU, hflat⟩ := h x
  obtain ⟨V, hV, rfl⟩ := hf.isInducing.isOpen_iff.1 hU
  obtain ⟨φ, hφx, hφ⟩ := hflat.exists_isSliceChart ⟨x, hxU⟩
  rw [range_comp, Subtype.range_coe, image_preimage_eq_inter_range, inter_comm] at hφ
  exact ⟨φ.restrOpen V hV, ⟨hφx, hxU⟩, hφ.of_inter hV⟩

/-- Being a slice embedding is invariant under precomposition with a homeomorphism of the
domain. -/
theorem comp_homeomorph (h : IsSliceEmbedding S f) (e : N' ≃ₜ N) : IsSliceEmbedding S (f ∘ e) := by
  refine ⟨h.isEmbedding.comp e.isEmbedding, fun x => ?_⟩
  obtain ⟨φ, hφx, hφ⟩ := h.exists_isSliceChart (e x)
  exact ⟨φ, hφx, by rwa [range_comp, e.surjective.range_eq, image_univ]⟩

/-- Being a slice embedding is invariant under precomposition with an open embedding of the domain:
such a precomposition is a restriction to an open subset, read through the homeomorphism onto its
range. -/
theorem comp_isOpenEmbedding {e : N' → N} (h : IsSliceEmbedding S f) (he : IsOpenEmbedding e) :
    IsSliceEmbedding S (f ∘ e) := by
  have h' := (h.restrict he.isOpen_range).comp_homeomorph he.isEmbedding.toHomeomorph
  simpa [Function.comp_def] using h'

/-- Pushing a slice embedding forward along an open embedding of the ambient space keeps it a slice
embedding. Taking `g` the inclusion of an open subset, this is the statement that a slice embedding
into an open subset is one into the whole space. -/
theorem isOpenEmbedding_comp {g : M → P} (h : IsSliceEmbedding S f) (hg : IsOpenEmbedding g) :
    IsSliceEmbedding S (g ∘ f) := by
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

/-- Conversely, an embedding that becomes a slice embedding after an open embedding of the ambient
space was already one. Taking `g` the inclusion of an open subset, this corestricts a slice
embedding to an open neighbourhood of its image. -/
theorem of_isOpenEmbedding_comp {g : M → P} (hg : IsOpenEmbedding g)
    (h : IsSliceEmbedding S (g ∘ f)) : IsSliceEmbedding S f := by
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

/-- Corestriction: a slice embedding whose image lies in an open subset `V` of the ambient space is
a slice embedding as a map into `V`. -/
theorem codRestrict (h : IsSliceEmbedding S f) {V : Set M} (hV : IsOpen V) (hf : ∀ x, f x ∈ V) :
    IsSliceEmbedding S (fun x => (⟨f x, hf x⟩ : V)) :=
  of_isOpenEmbedding_comp hV.isOpenEmbedding_subtypeVal h

/-- Being a slice embedding is invariant under a homeomorphism of the ambient space. -/
theorem homeomorph_comp (h : IsSliceEmbedding S f) (e : M ≃ₜ P) : IsSliceEmbedding S (e ∘ f) :=
  h.isOpenEmbedding_comp e.isOpenEmbedding

/-- Being a slice embedding only depends on the model space up to homeomorphism, the slice being
transported along. -/
theorem transHomeomorph (h : IsSliceEmbedding S f) (e : F ≃ₜ F') : IsSliceEmbedding (e '' S) f := by
  refine ⟨h.isEmbedding, fun x => ?_⟩
  obtain ⟨φ, hφx, hφ⟩ := h.exists_isSliceChart x
  refine ⟨φ.trans e.toOpenPartialHomeomorph, ?_, hφ.transHomeomorph e⟩
  rw [OpenPartialHomeomorph.trans_source]
  simpa using hφx

/-- A product of slice embeddings is a slice embedding for the product slice: a product of slice
charts is a slice chart. -/
theorem prodMap {S' : Set F'} {g : N' → P} (h : IsSliceEmbedding S f) (h' : IsSliceEmbedding S' g) :
    IsSliceEmbedding (S ×ˢ S') (Prod.map f g) := by
  refine ⟨h.isEmbedding.prodMap h'.isEmbedding, fun x => ?_⟩
  obtain ⟨φ, hφx, hφ⟩ := h.exists_isSliceChart x.1
  obtain ⟨ψ, hψx, hψ⟩ := h'.exists_isSliceChart x.2
  refine ⟨φ.prod ψ, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.prod_source]
    exact ⟨hφx, hψx⟩
  · rw [range_prodMap]
    exact hφ.prod hψ

/-- A slice embedding for the full model space is an open embedding. -/
theorem isOpenEmbedding (h : IsSliceEmbedding (univ : Set F) f) : IsOpenEmbedding f := by
  refine ⟨h.isEmbedding, isOpen_iff_mem_nhds.2 ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨φ, hφx, hφ⟩ := h.exists_isSliceChart x
  exact Filter.mem_of_superset (φ.open_source.mem_nhds hφx) (isSliceChart_univ_iff.1 hφ)

/-- The image of a slice embedding is locally closed as soon as the model slice is. This is where
the definition has teeth: the image of a wild embedding need not be locally closed in any chart in
this way. -/
theorem isLocallyClosed_range (h : IsSliceEmbedding S f) (hS : IsLocallyClosed S) :
    IsLocallyClosed (range f) := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := hS
  refine ((isLocallyClosed_tfae (range f)).out 3 1).1 ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨φ, hφx, hφ⟩ := h.exists_isSliceChart x
  -- Shrink the chart to the part of its source where the open half of the slice already holds;
  -- there the image is cut out by the closed half alone.
  set W := φ.source ∩ φ ⁻¹' U
  have hW : IsOpen W := φ.isOpen_inter_preimage hU
  have hxW : f x ∈ W := ⟨hφx, ((hφ.mem_iff hφx).1 (mem_range_self x)).1⟩
  refine ⟨W, hW.mem_nhds hxW, ?_⟩
  -- `U ↓∩ s` is notation for `Subtype.val ⁻¹' s`, so the goal is literally about that preimage.
  have hpre : ((Subtype.val : W → M) ⁻¹' range f) = (fun y : W => φ ↑y) ⁻¹' Z :=
    Set.ext fun y => (hφ.mem_iff y.2.1).trans (and_iff_right y.2.2)
  rw [hpre]
  exact hZ.preimage (φ.continuousOn.mono inter_subset_left).domRestrict

end IsSliceEmbedding

/-- An open embedding into a space charted on `F` is a slice embedding for the full model space. -/
theorem isSliceEmbedding_univ_of_isOpenEmbedding [ChartedSpace F M] (h : IsOpenEmbedding f) :
    IsSliceEmbedding (univ : Set F) f := by
  refine ⟨h.isEmbedding, fun x => ?_⟩
  refine ⟨(chartAt F (f x)).restrOpen (range f) h.isOpen_range,
    ⟨mem_chart_source F (f x), mem_range_self x⟩, ?_⟩
  exact isSliceChart_univ_iff.2 fun _ hy => hy.2

/-- Codimension zero: a map into a space charted on `F` is a slice embedding for the whole model
space exactly when it is an open embedding. -/
theorem isSliceEmbedding_univ_iff [ChartedSpace F M] :
    IsSliceEmbedding (univ : Set F) f ↔ IsOpenEmbedding f :=
  ⟨IsSliceEmbedding.isOpenEmbedding, isSliceEmbedding_univ_of_isOpenEmbedding⟩

section StandardSlice

variable [Zero F']

namespace IsLocallyFlat

theorem isEmbedding (h : IsLocallyFlat F F' f) : IsEmbedding f :=
  IsSliceEmbedding.isEmbedding h

/-- The defining charts of a locally flat embedding: around every point of the image there is a
chart of the ambient space, with values in `F × F'`, carrying the image onto the standard
coordinate slice. This is the eliminator consumers use to get hold of a flattening chart. -/
theorem exists_isSliceChart (h : IsLocallyFlat F F' f) (x : N) :
    ∃ φ : OpenPartialHomeomorph M (F × F'), f x ∈ φ.source ∧
      IsSliceChart φ ((univ : Set F) ×ˢ ({0} : Set F')) (range f) :=
  IsSliceEmbedding.exists_isSliceChart h x

theorem continuous (h : IsLocallyFlat F F' f) : Continuous f :=
  h.isEmbedding.continuous

theorem injective (h : IsLocallyFlat F F' f) : Function.Injective f :=
  h.isEmbedding.injective

/-- Local flatness is inherited by the restriction to an open subset of the domain. -/
theorem restrict (h : IsLocallyFlat F F' f) {U : Set N} (hU : IsOpen U) :
    IsLocallyFlat F F' (f ∘ ((↑) : U → N)) :=
  IsSliceEmbedding.restrict h hU

/-- Local flatness is a local property of the domain: if every point of `N` has an open
neighbourhood on which the restriction of `f` is locally flat, then `f` is locally flat. -/
theorem of_forall_exists_isOpen (hf : IsEmbedding f)
    (h : ∀ x : N, ∃ U : Set N, IsOpen U ∧ x ∈ U ∧ IsLocallyFlat F F' (f ∘ ((↑) : U → N))) :
    IsLocallyFlat F F' f :=
  IsSliceEmbedding.of_forall_exists_isOpen hf h

/-- Local flatness is invariant under precomposition with a homeomorphism of the domain. -/
theorem comp_homeomorph (h : IsLocallyFlat F F' f) (e : N' ≃ₜ N) : IsLocallyFlat F F' (f ∘ e) :=
  IsSliceEmbedding.comp_homeomorph h e

/-- Local flatness is invariant under precomposition with an open embedding of the domain. -/
theorem comp_isOpenEmbedding {e : N' → N} (h : IsLocallyFlat F F' f) (he : IsOpenEmbedding e) :
    IsLocallyFlat F F' (f ∘ e) :=
  IsSliceEmbedding.comp_isOpenEmbedding h he

/-- Pushing a locally flat embedding forward along an open embedding of the ambient space keeps it
locally flat. Taking `g` the inclusion of an open subset, this is the statement that a locally flat
embedding into an open subset is locally flat into the whole space. -/
theorem isOpenEmbedding_comp {g : M → P} (h : IsLocallyFlat F F' f) (hg : IsOpenEmbedding g) :
    IsLocallyFlat F F' (g ∘ f) :=
  IsSliceEmbedding.isOpenEmbedding_comp h hg

/-- Conversely, an embedding that becomes locally flat after an open embedding of the ambient space
was already locally flat. -/
theorem of_isOpenEmbedding_comp {g : M → P} (hg : IsOpenEmbedding g)
    (h : IsLocallyFlat F F' (g ∘ f)) : IsLocallyFlat F F' f :=
  IsSliceEmbedding.of_isOpenEmbedding_comp hg h

/-- Corestriction: a locally flat embedding whose image lies in an open subset `V` of the ambient
space is locally flat as a map into `V`. -/
theorem codRestrict (h : IsLocallyFlat F F' f) {V : Set M} (hV : IsOpen V) (hf : ∀ x, f x ∈ V) :
    IsLocallyFlat F F' (fun x => (⟨f x, hf x⟩ : V)) :=
  IsSliceEmbedding.codRestrict h hV hf

/-- Local flatness is invariant under a homeomorphism of the ambient space. -/
theorem homeomorph_comp (h : IsLocallyFlat F F' f) (e : M ≃ₜ P) : IsLocallyFlat F F' (e ∘ f) :=
  IsSliceEmbedding.homeomorph_comp h e

/-- The general form of `TauCeti.IsLocallyFlat.comp`: what makes a composite locally flat is a
compatible pair of charts around each point of the domain, and nothing else. It asks for a chart
`ψ` of `P` at `g (f x)` and a flattening chart `φ` of `M` for `f` such that `ψ` reads the
intermediate coordinates off `φ` along `g`, in the sense `ψ (g y) = (φ y, 0)` on the source of `φ`,
such that `ψ` sees no more of `range g` than `φ` charts, and such that on its source `ψ` detects
`range g` from the vanishing of the outer coordinate. That same `ψ` then flattens `g ∘ f`, whose
complementary model is the product of the two complementary models. Since `hcompat` already
supplies every flattening chart the conclusion needs, the only embedding content assumed is what
the conclusion itself carries, that `g ∘ f` is an embedding, together with injectivity of `g`. Only
the stated half of the flattening of `range g` by `ψ` is assumed, the other half being forced by
`hagree` and `hsub`; likewise `f x ∈ φ.source` is not assumed, since `hsub` and injectivity of `g`
already give it. -/
theorem of_compatible_isSliceChart {G' : Type*} [TopologicalSpace G'] [Zero G'] {g : M → P}
    (hgf : IsEmbedding (g ∘ f)) (hg : Function.Injective g)
    (hcompat : ∀ x : N, ∃ ψ : OpenPartialHomeomorph P ((F × F') × G'),
      ∃ φ : OpenPartialHomeomorph M (F × F'), g (f x) ∈ ψ.source ∧
        (∀ p ∈ ψ.source, (ψ p).2 = 0 → p ∈ range g) ∧
        IsSliceChart φ ((univ : Set F) ×ˢ ({0} : Set F')) (range f) ∧
        ψ.source ∩ range g ⊆ g '' φ.source ∧ ∀ y ∈ φ.source, ψ (g y) = (φ y, 0)) :
    IsLocallyFlat F (F' × G') (g ∘ f) := by
  -- In the model `(F × F') × G'` of `P` the composite is flattened onto the iterated slice; the
  -- standard slice of `F × (F' × G')` is that one after reassociating the coordinates.
  have key : IsSliceEmbedding (((univ : Set F) ×ˢ ({0} : Set F')) ×ˢ ({0} : Set G')) (g ∘ f) := by
    refine ⟨hgf, fun x => ?_⟩
    obtain ⟨ψ, φ, hψx, hψ, hφ, hsub, hagree⟩ := hcompat x
    refine ⟨ψ, hψx, isSliceChart_iff.2 fun p hp => ?_⟩
    constructor
    · intro hpf
      obtain ⟨y, hy, rfl⟩ := hsub ⟨hp, range_comp_subset_range f g hpf⟩
      obtain ⟨x', hx'⟩ := hpf
      rw [Function.comp_apply] at hx'
      rw [hagree y hy]
      exact ⟨(hφ.mem_iff hy).1 ⟨x', hg hx'⟩, rfl⟩
    · intro hps
      obtain ⟨y, hy, rfl⟩ := hsub ⟨hp, hψ p hp hps.2⟩
      rw [hagree y hy] at hps
      obtain ⟨x', hx'⟩ := (hφ.mem_iff hy).2 hps.1
      exact ⟨x', by rw [Function.comp_apply, hx']⟩
  have himage : Homeomorph.prodAssoc F F' G' ''
      (((univ : Set F) ×ˢ ({0} : Set F')) ×ˢ ({0} : Set G')) =
      (univ : Set F) ×ˢ ({0} : Set (F' × G')) := by
    rw [Homeomorph.image_eq_preimage_symm]
    ext ⟨a, b, c⟩
    simp [Homeomorph.prodAssoc, Prod.ext_iff]
  have hcomp := key.transHomeomorph (Homeomorph.prodAssoc F F' G')
  rw [himage] at hcomp
  exact hcomp

/-- **Composition of locally flat embeddings**, under an explicit compatibility hypothesis on
their flattening charts. Local flatness of `f : N → M` and of `g : M → P` does not by itself make
`g ∘ f` locally flat, because the chart of `M` flattening `f` and the chart of `P` flattening `g`
are chosen independently and nothing makes them agree; `hcompat` is the hypothesis that charts
witnessing `hf` and `hg` can be chosen coherently around each point of the domain, namely so that
the outer chart reads the intermediate coordinates off the inner one along `g`, in the sense
`ψ (g y) = (φ y, 0)` on the source of `φ`, and sees no more of `range g` than the inner one charts.
The outer chart then flattens the composite, whose complementary model is the product of the two
complementary models.

Only the compatible pair of charts is used, not the two local flatness hypotheses in full; that
sharper form is `TauCeti.IsLocallyFlat.of_compatible_isSliceChart`, from which this is derived. -/
theorem comp {G' : Type*} [TopologicalSpace G'] [Zero G'] {g : M → P}
    (hg : IsLocallyFlat (F × F') G' g) (hf : IsLocallyFlat F F' f)
    (hcompat : ∀ x : N, ∃ ψ : OpenPartialHomeomorph P ((F × F') × G'),
      ∃ φ : OpenPartialHomeomorph M (F × F'), g (f x) ∈ ψ.source ∧ f x ∈ φ.source ∧
        IsSliceChart ψ ((univ : Set (F × F')) ×ˢ ({0} : Set G')) (range g) ∧
        IsSliceChart φ ((univ : Set F) ×ˢ ({0} : Set F')) (range f) ∧
        ψ.source ∩ range g ⊆ g '' φ.source ∧ ∀ y ∈ φ.source, ψ (g y) = (φ y, 0)) :
    IsLocallyFlat F (F' × G') (g ∘ f) :=
  of_compatible_isSliceChart (hg.isEmbedding.comp hf.isEmbedding) hg.injective fun x => by
    obtain ⟨ψ, φ, hψx, -, hψ, hφ, hsub, hagree⟩ := hcompat x
    -- The flattening of `range g` by `ψ` gives in particular the one direction of it that
    -- `of_compatible_isSliceChart` asks for.
    exact ⟨ψ, φ, hψx, fun p hp hp2 => (hψ.mem_iff hp).2 ⟨mem_univ _, hp2⟩, hφ, hsub, hagree⟩

/-- A product of locally flat embeddings is locally flat, the models multiplying: the product of
two standard slices is the standard slice of the product, after the permutation of coordinates
exchanging the two middle factors. -/
theorem prodMap {G G' : Type*} [TopologicalSpace G] [TopologicalSpace G'] [Zero G'] {g : N' → P}
    (h : IsLocallyFlat F F' f) (h' : IsLocallyFlat G G' g) :
    IsLocallyFlat (F × G) (F' × G') (Prod.map f g) := by
  have himage : Homeomorph.prodProdProdComm F F' G G' ''
      (((univ : Set F) ×ˢ ({0} : Set F')) ×ˢ ((univ : Set G) ×ˢ ({0} : Set G'))) =
      (univ : Set (F × G)) ×ˢ ({0} : Set (F' × G')) := by
    rw [Homeomorph.image_eq_preimage_symm]
    ext ⟨⟨a, c⟩, b, d⟩
    simp [Homeomorph.prodProdProdComm, Prod.ext_iff]
  have hprod := (IsSliceEmbedding.prodMap h h').transHomeomorph
    (Homeomorph.prodProdProdComm F F' G G')
  rw [himage] at hprod
  exact hprod

/-- The image of a locally flat embedding is locally closed as soon as the origin of the
complementary model is closed, the standard slice then being closed. This is where the definition
has teeth: the image of a wild embedding need not be locally closed. -/
theorem isLocallyClosed_range (h : IsLocallyFlat F F' f) (h0 : IsClosed ({0} : Set F')) :
    IsLocallyClosed (range f) :=
  IsSliceEmbedding.isLocallyClosed_range h (isClosed_univ.prod h0).isLocallyClosed

end IsLocallyFlat

/-- Local flatness is exactly being a slice embedding for the standard coordinate slice
`F × {0}` of `F × F'`. This is the characterisation to use downstream, where the definition of
`TauCeti.IsLocallyFlat` is not unfolded. -/
theorem isLocallyFlat_iff_isSliceEmbedding :
    IsLocallyFlat F F' f ↔ IsSliceEmbedding ((univ : Set F) ×ˢ ({0} : Set F')) f :=
  Iff.rfl

/-- Local flatness spelled out pointwise: `f` is a topological embedding, and around every point of
its image there is an ambient chart in which the image is exactly the vanishing locus of the
complementary coordinates. -/
theorem isLocallyFlat_iff :
    IsLocallyFlat F F' f ↔ IsEmbedding f ∧ ∀ x : N, ∃ φ : OpenPartialHomeomorph M (F × F'),
      f x ∈ φ.source ∧ ∀ y ∈ φ.source, y ∈ range f ↔ (φ y).2 = 0 := by
  have key : ∀ φ : OpenPartialHomeomorph M (F × F'),
      IsSliceChart φ ((univ : Set F) ×ˢ ({0} : Set F')) (range f) ↔
        ∀ y ∈ φ.source, y ∈ range f ↔ (φ y).2 = 0 := fun φ => by
    rw [isSliceChart_iff]
    simp
  exact ⟨fun h => ⟨h.isEmbedding,
      fun x => (h.exists_isSliceChart x).imp fun φ hφ => ⟨hφ.1, (key φ).1 hφ.2⟩⟩,
    fun h => ⟨h.1, fun x => (h.2 x).imp fun φ hφ => ⟨hφ.1, (key φ).2 hφ.2⟩⟩⟩

/-- Codimension zero: with a trivial complementary model, over a space charted on `F × F'`, locally
flat is exactly open embedding. In particular local flatness is strictly stronger than embedding:
not every embedding is locally flat. -/
theorem isLocallyFlat_iff_isOpenEmbedding [Subsingleton F'] [ChartedSpace (F × F') M] :
    IsLocallyFlat F F' f ↔ IsOpenEmbedding f := by
  have hzero : ({0} : Set F') = univ := eq_univ_of_forall fun x => Subsingleton.elim x 0
  have h0 : ((univ : Set F) ×ˢ ({0} : Set F')) = (univ : Set (F × F')) := by
    rw [hzero, univ_prod_univ]
  rw [IsLocallyFlat, h0]
  exact isSliceEmbedding_univ_iff

/-- The standard local model: over a space `N` charted on `F`, the inclusion of `N` as the slice
`N × {0}` of `N × F'` is locally flat, its flattening charts being the charts of `N` times the
identity. With `N = F = ℝⁿ` and `F' = ℝᵏ` this is the coordinate slice `ℝⁿ × {0} ⊆ ℝⁿ⁺ᵏ` that local
flatness is modelled on. -/
theorem isLocallyFlat_prodMkLeft [ChartedSpace F N] :
    IsLocallyFlat F F' (fun x : N => (x, (0 : F'))) := by
  refine ⟨isEmbedding_prodMkLeft 0, fun x => ⟨(chartAt F x).prod (OpenPartialHomeomorph.refl F'),
    ⟨mem_chart_source F x, mem_univ _⟩, isSliceChart_iff.2 fun p _ => ?_⟩⟩
  simp [Prod.ext_iff, eq_comm]

end StandardSlice

/-!
### Local product neighbourhoods

A flattening chart is already a local trivialisation once its target has been shrunk to a box, so
a locally flat embedding has local product neighbourhoods in any codimension.
-/

section ProductNeighborhood

/-- An open partial homeomorphism turns an open embedding into its target into an open embedding
into its source. This is the transport step of the constructions below. -/
private theorem isOpenEmbedding_symm_comp {X : Type*} [TopologicalSpace X]
    (ψ : OpenPartialHomeomorph M F) {g : X → F} (hg : IsOpenEmbedding g)
    (hgr : range g ⊆ ψ.target) : IsOpenEmbedding (ψ.symm ∘ g) :=
  .of_continuous_injective_isOpenMap
    (ψ.continuousOn_symm.comp_continuous hg.continuous fun q => hgr (mem_range_self q))
    (fun q q' hqq' => hg.injective (ψ.symm.injOn
      (ψ.symm_source ▸ hgr (mem_range_self q)) (ψ.symm_source ▸ hgr (mem_range_self q')) hqq'))
    fun O hO => by
      rw [image_comp]
      exact ψ.isOpen_image_symm_of_subset_target (hg.isOpenMap O hO)
        ((image_subset_range g O).trans hgr)

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A slice chart whose target is a box `u ×ˢ ball 0 r` exhibits its source as a product of the
part of the domain lying under it with the complementary model, the map being the zero slice.
This is the geometric content of the local product statement; the general case reduces to it by
shrinking the chart. -/
private theorem exists_isOpenEmbedding_prod_of_target_eq_prod {ψ : OpenPartialHomeomorph M (F × G)}
    {u : Set F} {r : ℝ} (hu : IsOpen u) (hr : 0 < r) (hψt : ψ.target = u ×ˢ ball (0 : G) r)
    (hψ : IsSliceChart ψ ((univ : Set F) ×ˢ ({0} : Set G)) (range f)) (hf : IsEmbedding f) :
    ∃ b : (f ⁻¹' ψ.source) × G → M,
      IsOpenEmbedding b ∧ ∀ y : (f ⁻¹' ψ.source), b (y, 0) = f y := by
  -- Read the normal factor of the box as the whole complementary model.
  set ρ := OpenPartialHomeomorph.univBall (0 : G) r with hρ
  have hρs : ρ.source = univ := OpenPartialHomeomorph.univBall_source _ _
  have hρr : range ρ = ball (0 : G) r := by
    rw [← image_univ, ← hρs, OpenPartialHomeomorph.image_source_eq_target, hρ,
      OpenPartialHomeomorph.univBall_target _ hr]
  have hρ0 : ρ 0 = 0 := OpenPartialHomeomorph.univBall_apply_zero ..
  -- `σ` presents the source of the chart as a product.
  set j : u × G → F × G := Prod.map ((↑) : u → F) ρ with hj
  have hje : IsOpenEmbedding j :=
    hu.isOpenEmbedding_subtypeVal.prodMap (ρ.isOpenEmbedding hρs)
  have hjr : range j = ψ.target := by
    rw [hj, range_prodMap, Subtype.range_coe, hρr, hψt]
  set σ : u × G → M := ψ.symm ∘ j with hσ
  have hσe : IsOpenEmbedding σ := isOpenEmbedding_symm_comp ψ hje hjr.subset
  -- The zero slice of `σ` and the restriction of `f` are two embeddings with the same image.
  set e₁ : (f ⁻¹' ψ.source) → M := f ∘ ((↑) : (f ⁻¹' ψ.source) → N) with he₁
  set e₂ : u → M := fun v => σ (v, 0) with he₂
  have he₂' : ∀ v : u, e₂ v = ψ.symm ((v : F), (0 : G)) := fun v => by
    simp [he₂, hσ, hj, hρ0]
  have hr₁ : range e₁ = ψ.source ∩ range f := by
    rw [he₁, range_comp, Subtype.range_coe, image_preimage_eq_inter_range]
  have hr₂ : range e₂ = ψ.source ∩ range f := by
    ext m
    constructor
    · rintro ⟨v, rfl⟩
      have hmem : ((v : F), (0 : G)) ∈ ψ.target := by
        rw [hψt]; exact ⟨v.2, mem_ball_self hr⟩
      have hs : ψ.symm ((v : F), (0 : G)) ∈ ψ.source := ψ.map_target hmem
      rw [he₂' v]
      exact ⟨hs, (hψ.mem_iff hs).2 (by rw [ψ.right_inv hmem]; exact ⟨mem_univ _, rfl⟩)⟩
    · rintro ⟨hms, hmr⟩
      have h2 : (ψ m).2 = 0 := ((hψ.mem_iff hms).1 hmr).2
      have h1 : (ψ m).1 ∈ u := by
        have hmt := ψ.map_source hms
        rw [hψt] at hmt
        exact hmt.1
      refine ⟨⟨(ψ m).1, h1⟩, ?_⟩
      have hpair : (((ψ m).1 : F), (0 : G)) = ψ m := by rw [← h2]
      rw [he₂' ⟨(ψ m).1, h1⟩, hpair]
      exact ψ.left_inv hms
  -- Two embeddings with the same image have homeomorphic domains, over the ambient space.
  have hb₁ : IsEmbedding e₁ := hf.comp IsEmbedding.subtypeVal
  have hb₂ : IsEmbedding e₂ := hσe.isEmbedding.comp (isEmbedding_prodMkLeft 0)
  have hkey : ∀ z : range e₂, e₂ (hb₂.toHomeomorph.symm z) = (z : M) := fun z => by
    rw [← Topology.IsEmbedding.toHomeomorph_apply_coe hb₂]
    exact congrArg Subtype.val (hb₂.toHomeomorph.apply_symm_apply z)
  set η : (f ⁻¹' ψ.source) ≃ₜ u :=
    hb₁.toHomeomorph.trans ((Homeomorph.setCongr (hr₁.trans hr₂.symm)).trans hb₂.toHomeomorph.symm)
    with hη
  refine ⟨σ ∘ Prod.map η id, hσe.comp (η.isOpenEmbedding.prodMap IsOpenEmbedding.id), fun y => ?_⟩
  have hy : e₂ (η y) = e₁ y := by
    rw [hη, Homeomorph.trans_apply, Homeomorph.trans_apply, hkey]
    exact Topology.IsEmbedding.toHomeomorph_apply_coe hb₁ y
  simpa [he₁, he₂] using hy

/-- A locally flat embedding has **local product neighbourhoods**: every point of the domain has
an open neighbourhood `U` such that an open subset of the ambient space is a product `U × G`, in
which the map is the zero slice.

The complementary model is only asked to be a real normed space, so this covers every
codimension. What is codimension-sensitive is patching these local products into a global one,
which is not proved here. -/
theorem IsLocallyFlat.exists_isOpenEmbedding_prod (h : IsLocallyFlat F G f) (x : N) :
    ∃ U : Set N, IsOpen U ∧ x ∈ U ∧ ∃ b : U × G → M,
      IsOpenEmbedding b ∧ ∀ y : U, b (y, 0) = f y := by
  obtain ⟨φ, hφx, hφ⟩ := h.exists_isSliceChart x
  -- The chart reads `f x` on the zero slice.
  have hfx : φ (f x) = ((φ (f x)).1, (0 : G)) :=
    Prod.ext rfl ((hφ.mem_iff hφx).1 ⟨x, rfl⟩).2
  -- Shrink the chart until its target is a box.
  obtain ⟨u, w, hu, hw, hxu, h0w, huw⟩ :=
    isOpen_prod_iff.1 φ.open_target _ _ (hfx ▸ φ.map_source hφx)
  obtain ⟨r, hr, hrw⟩ := Metric.isOpen_iff.1 hw 0 h0w
  obtain ⟨ψ, -, hψs, hψt, hψ⟩ :=
    hφ.exists_target_eq (hu.prod isOpen_ball) fun z hz => huw ⟨hz.1, hrw hz.2⟩
  have hψx : f x ∈ ψ.source := by
    rw [hψs]
    exact ⟨hφx, by rw [mem_preimage, hfx]; exact ⟨hxu, mem_ball_self hr⟩⟩
  exact ⟨f ⁻¹' ψ.source, ψ.open_source.preimage h.continuous, hψx,
    exists_isOpenEmbedding_prod_of_target_eq_prod hu hr hψt hψ h.isEmbedding⟩

end ProductNeighborhood

end TauCeti
