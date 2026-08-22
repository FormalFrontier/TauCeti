/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.HasGroupoid
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic

/-!
# Locally flat embeddings are locally bicollared

A locally flat embedding is one that ambient charts flatten onto the standard coordinate slice
(`TauCeti.IsLocallyFlat`). This file extracts from those charts the structure they were isolated
to provide: near each point of the domain, an open neighbourhood of the image that is a *product*,
with the image sitting inside it as the zero slice.

In codimension one that structure is a **bicollar**: an open embedding `b : N × ℝ → M` with
`b (x, 0) = f x`, so that the image is two-sided inside the open set the collar sweeps out. This
is the notion Brown's collaring theorem is about, and the reason local flatness is the hypothesis
under which topological manifolds behave: the Alexander horned sphere is an embedded `2`-sphere in
`S³` that is *not* locally bicollared because it has wild points at which no neighbourhood pair is
homeomorphic to the standard coordinate-slice pair.

The file proves both directions of the comparison.

* **Local flatness gives local bicollars.** The general local-product theorem
  `TauCeti.IsLocallyFlat.exists_isOpenEmbedding_prod` from `LocallyFlat.Basic`, specialised to a
  one-dimensional complementary model, gives `TauCeti.IsLocallyFlat.isLocallyBicollared`.
* **A bicollar is a local flattening.** `TauCeti.IsBicollar.isLocallyFlat` runs the comparison
  backwards: a collared map factors through the standard slice `N → N × ℝ`, which is locally flat
  once `N` is charted on `F`, and local flatness is stable under composing with an open embedding.
  Needing the domain to be charted on `F` is where the "an `(n-1)`-manifold in an `n`-manifold" of
  the informal statement enters.

Together they give `TauCeti.isLocallyFlat_iff_isEmbedding_and_isLocallyBicollared`: over a domain
charted on `F`, a map is locally flat with one-dimensional complementary model exactly when it is
an embedding that is locally bicollared. The embedding hypothesis cannot be dropped: a
figure-eight immersion of a line into the plane is locally bicollared and is not an embedding,
since bicollars only see the domain locally.

This is the codimension-one collaring bullet of layer 2 of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`). What remains of that bullet is its global sphere
conclusion: a locally flat `(n-1)`-sphere in `Sⁿ` is bicollared. That conclusion needs a genuinely
global collaring argument and is not proved here. Positive-codimension normal bundles, the
companion notion, are flagged by the roadmap as a dependency to be taken from elsewhere rather
than built in this layer.

## Main definitions

* `TauCeti.IsBicollar`: an open embedding `N × ℝ → M` whose zero slice is a given map.
* `TauCeti.IsBicollared`: admitting a bicollar.
* `TauCeti.IsLocallyBicollared`: every point of the domain has an open neighbourhood on which the
  restriction is bicollared.

The last two are `def`s whose bodies the module system does not expose, so
`TauCeti.isBicollared_iff` and `TauCeti.isLocallyBicollared_iff` are the only way to introduce or
eliminate them downstream.

## Main results

* `TauCeti.IsLocallyFlat.isLocallyBicollared`: **a locally flat embedding of codimension one is
  locally bicollared.**
* `TauCeti.IsBicollar.isLocallyFlat`, `TauCeti.IsLocallyBicollared.isLocallyFlat` and
  `TauCeti.isLocallyFlat_iff_isEmbedding_and_isLocallyBicollared`: the converse, and the resulting
  characterisation.
* `TauCeti.IsBicollar.range_diff_range_eq_union` and
  `TauCeti.IsBicollar.disjoint_image_Ioi_Iio`: the two sides of a bicollar are disjoint and cover
  the complement of the image inside the collar.
* `TauCeti.IsLocallyBicollared.restrict`, `TauCeti.IsLocallyBicollared.isOpenEmbedding_comp`, and
  `TauCeti.IsLocallyBicollared.comp_homeomorph`: the local predicate's basic closure API.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341, for the global collaring theorem this is the local half of.
* R. Daverman and G. Venema, *Embeddings in Manifolds*, AMS Graduate Studies in Mathematics 106
  (2009), Chapter 2, for bicollars and their role in codimension one.
-/

public section

namespace TauCeti

open Set Topology

variable {M N N' P F F' : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [TopologicalSpace N'] [TopologicalSpace P] [TopologicalSpace F] [TopologicalSpace F']

/-!
### Bicollars
-/

/-- A **bicollar** of a map `f : N → M` is an open embedding `b : N × ℝ → M` whose zero slice is
`f`. It exhibits an open neighbourhood of the image of `f` as a product of `N` with a line, in
which the image is the zero slice; in particular the image is two-sided inside that
neighbourhood. -/
structure IsBicollar (f : N → M) (b : N × ℝ → M) : Prop where
  /-- A bicollar is an open embedding of the product of the domain with a line. -/
  isOpenEmbedding : IsOpenEmbedding b
  /-- The zero slice of a bicollar is the map it collars. -/
  apply_zero (x : N) : b (x, 0) = f x

/-- A map is **bicollared** if it admits a bicollar. -/
def IsBicollared (f : N → M) : Prop := ∃ b : N × ℝ → M, IsBicollar f b

/-- A map is **locally bicollared** if every point of its domain has an open neighbourhood on
which the restriction of the map is bicollared. Unlike being bicollared, this says nothing
globally: it does not even imply that the map is injective. -/
def IsLocallyBicollared (f : N → M) : Prop :=
  ∀ x : N, ∃ U : Set N, IsOpen U ∧ x ∈ U ∧ IsBicollared (f ∘ ((↑) : U → N))

variable {f : N → M} {b : N × ℝ → M}

/-- Being bicollared spelled out: some open embedding of `N × ℝ` has `f` as its zero slice. The
module system does not expose the body of `TauCeti.IsBicollared`, so a downstream file cannot
unfold it; this lemma is how the definition is introduced and eliminated there. -/
theorem isBicollared_iff : IsBicollared f ↔ ∃ b : N × ℝ → M, IsBicollar f b := Iff.rfl

/-- Being locally bicollared spelled out: every point of the domain has an open neighbourhood on
which the restriction of the map is bicollared. The module system does not expose the body of
`TauCeti.IsLocallyBicollared`, so a downstream file cannot unfold it; this lemma is how the
definition is introduced and eliminated there. -/
theorem isLocallyBicollared_iff : IsLocallyBicollared f ↔
    ∀ x : N, ∃ U : Set N, IsOpen U ∧ x ∈ U ∧ IsBicollared (f ∘ ((↑) : U → N)) := Iff.rfl

namespace IsBicollar

/-- A bicollar witnesses that the map it collars is bicollared. -/
theorem isBicollared (h : IsBicollar f b) : IsBicollared f := ⟨b, h⟩

theorem isEmbedding (h : IsBicollar f b) : IsEmbedding f := by
  have hf : f = b ∘ fun x : N => (x, (0 : ℝ)) := funext fun x => (h.apply_zero x).symm
  rw [hf]
  exact h.isOpenEmbedding.isEmbedding.comp (isEmbedding_prodMkLeft 0)

theorem continuous (h : IsBicollar f b) : Continuous f := h.isEmbedding.continuous

theorem injective (h : IsBicollar f b) : Function.Injective f := h.isEmbedding.injective

/-- The image of a collared map lies in the open set its bicollar sweeps out. -/
theorem range_subset_range (h : IsBicollar f b) : range f ⊆ range b := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(x, 0), h.apply_zero x⟩

/-- Read in a bicollar, the collared image is exactly the zero slice. -/
theorem image_prod_singleton_zero (h : IsBicollar f b) :
    b '' (univ ×ˢ ({0} : Set ℝ)) = range f := by
  ext m
  constructor
  · rintro ⟨⟨y, t⟩, ⟨-, (rfl : t = 0)⟩, rfl⟩
    exact ⟨y, (h.apply_zero y).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨(y, 0), ⟨mem_univ _, rfl⟩, h.apply_zero y⟩

/-- A bicollar meets the image of the map it collars only along the zero slice. -/
@[simp]
theorem preimage_range (h : IsBicollar f b) : b ⁻¹' range f = univ ×ˢ ({0} : Set ℝ) := by
  ext ⟨y, t⟩
  simp only [mem_preimage, mem_range, mem_prod, mem_univ, true_and, mem_singleton_iff]
  refine ⟨fun ⟨z, hz⟩ => ?_, fun ht => ⟨y, ht ▸ (h.apply_zero y).symm⟩⟩
  have hb : b (z, 0) = b (y, t) := by rw [h.apply_zero z, ← hz]
  exact ((Prod.ext_iff.1 (h.isOpenEmbedding.injective hb)).2).symm

/-- Inside a bicollar the complement of the collared image splits into the two sides `t > 0` and
`t < 0` of the collar. This is what makes the collar two-sided, and it is exactly what fails for
a wild embedding. -/
theorem range_diff_range_eq_union (h : IsBicollar f b) :
    range b \ range f = b '' (univ ×ˢ Ioi (0 : ℝ)) ∪ b '' (univ ×ˢ Iio (0 : ℝ)) := by
  rw [← h.image_prod_singleton_zero, ← image_univ,
    ← Set.image_sdiff h.isOpenEmbedding.injective, ← image_union, ← prod_union]
  congr 1
  ext ⟨y, t⟩
  simp

/-- The two sides of a bicollar are disjoint. -/
theorem disjoint_image_Ioi_Iio (h : IsBicollar f b) :
    Disjoint (b '' (univ ×ˢ Ioi (0 : ℝ))) (b '' (univ ×ˢ Iio (0 : ℝ))) := by
  refine disjoint_left.2 ?_
  rintro _ ⟨⟨y, t⟩, ht, rfl⟩ ⟨⟨y', t'⟩, ht', heq⟩
  have htt : t' = t := (Prod.ext_iff.1 (h.isOpenEmbedding.injective heq)).2
  have hpos : (0 : ℝ) < t := ht.2
  have hneg : t' < 0 := ht'.2
  rw [htt] at hneg
  exact absurd (hpos.trans hneg) (lt_irrefl 0)

/-- A bicollar restricts to a bicollar over any open subset of the domain. -/
theorem restrict (h : IsBicollar f b) {U : Set N} (hU : IsOpen U) :
    IsBicollar (f ∘ ((↑) : U → N)) (b ∘ Prod.map ((↑) : U → N) id) where
  isOpenEmbedding :=
    h.isOpenEmbedding.comp (hU.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id)
  apply_zero x := h.apply_zero x

/-- Bicollars are carried along by open embeddings of the ambient space. -/
theorem isOpenEmbedding_comp {g : M → P} (h : IsBicollar f b) (hg : IsOpenEmbedding g) :
    IsBicollar (g ∘ f) (g ∘ b) where
  isOpenEmbedding := hg.comp h.isOpenEmbedding
  apply_zero x := congrArg g (h.apply_zero x)

/-- Bicollars are carried along by homeomorphisms of the domain. -/
theorem comp_homeomorph (h : IsBicollar f b) (e : N' ≃ₜ N) :
    IsBicollar (f ∘ e) (b ∘ Prod.map e id) where
  isOpenEmbedding := h.isOpenEmbedding.comp (e.isOpenEmbedding.prodMap IsOpenEmbedding.id)
  apply_zero x := h.apply_zero (e x)

end IsBicollar

/-- The standard local model: the inclusion of `N` as the zero slice of `N × ℝ` is bicollared, by
the identity. -/
theorem isBicollar_prodMkLeft : IsBicollar (fun x : N => (x, (0 : ℝ))) id where
  isOpenEmbedding := IsOpenEmbedding.id
  apply_zero _ := rfl

namespace IsBicollared

theorem isEmbedding (h : IsBicollared f) : IsEmbedding f :=
  let ⟨_, hb⟩ := h; hb.isEmbedding

theorem restrict (h : IsBicollared f) {U : Set N} (hU : IsOpen U) :
    IsBicollared (f ∘ ((↑) : U → N)) :=
  let ⟨_, hb⟩ := h; ⟨_, hb.restrict hU⟩

theorem isOpenEmbedding_comp {g : M → P} (h : IsBicollared f) (hg : IsOpenEmbedding g) :
    IsBicollared (g ∘ f) :=
  let ⟨_, hb⟩ := h; ⟨_, hb.isOpenEmbedding_comp hg⟩

theorem comp_homeomorph (h : IsBicollared f) (e : N' ≃ₜ N) : IsBicollared (f ∘ e) :=
  let ⟨_, hb⟩ := h; ⟨_, hb.comp_homeomorph e⟩

theorem isLocallyBicollared (h : IsBicollared f) : IsLocallyBicollared f :=
  fun _ => ⟨univ, isOpen_univ, mem_univ _, h.restrict isOpen_univ⟩

end IsBicollared

namespace IsLocallyBicollared

/-- Local bicollaring is inherited by the restriction to an open subset of the domain. -/
theorem restrict (h : IsLocallyBicollared f) {U : Set N} (hU : IsOpen U) :
    IsLocallyBicollared (f ∘ ((↑) : U → N)) := by
  intro x
  obtain ⟨V, hV, hxV, hb⟩ := h x
  let W : Set U := ((↑) : U → N) ⁻¹' V
  let R : Set V := ((↑) : V → N) ⁻¹' U
  have hW : IsOpen W := hV.preimage continuous_subtype_val
  have hR : IsOpen R := hU.preimage continuous_subtype_val
  -- `W` and `R` are the two readings of `U ∩ V`, one as a subset of `U` and one as a subset of
  -- `V`; the homeomorphism between them only re-brackets the pair of membership proofs.
  let e : W ≃ₜ R := {
    toFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
    invFun y := ⟨⟨y.1.1, y.2⟩, y.1.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop
  }
  refine ⟨W, hW, hxV, ?_⟩
  -- Both routes out of `W` send `y` to `f y.1.1`: going through `V` reindexes the subtype and
  -- nothing else. Recording that as an equality of functions keeps the reindexing in view.
  have hcomp : ((f ∘ ((↑) : V → N)) ∘ ((↑) : R → V)) ∘ ⇑e = (f ∘ ((↑) : U → N)) ∘ ((↑) : W → U) :=
    funext fun _ => rfl
  exact hcomp ▸ (hb.restrict hR).comp_homeomorph e

/-- Local bicollars are carried along by open embeddings of the ambient space. -/
theorem isOpenEmbedding_comp {g : M → P} (h : IsLocallyBicollared f)
    (hg : IsOpenEmbedding g) : IsLocallyBicollared (g ∘ f) := by
  intro x
  obtain ⟨U, hU, hxU, hb⟩ := h x
  exact ⟨U, hU, hxU, by simpa [Function.comp_def] using hb.isOpenEmbedding_comp hg⟩

/-- Local bicollaring is invariant under homeomorphisms of the domain. -/
theorem comp_homeomorph (h : IsLocallyBicollared f) (e : N' ≃ₜ N) :
    IsLocallyBicollared (f ∘ e) := by
  intro x
  obtain ⟨U, hU, hexU, hb⟩ := h (e x)
  -- `eU` is `e` itself, read as a homeomorphism onto `U` from the part of `N'` it lands in.
  let eU : (e ⁻¹' U) ≃ₜ U := e.subtype fun _ => Iff.rfl
  refine ⟨e ⁻¹' U, hU.preimage e.continuous, hexU, ?_⟩
  -- Composing with `eU` and then including `U` is composing with `e`, on the nose.
  have hcomp : (f ∘ ((↑) : U → N)) ∘ ⇑eU = (f ∘ ⇑e) ∘ ((↑) : (e ⁻¹' U) → N') :=
    funext fun _ => rfl
  exact hcomp ▸ hb.comp_homeomorph eU

end IsLocallyBicollared

/-!
### Local flatness and local bicollaring

A locally flat embedding has local product neighbourhoods by the general theorem in
`LocallyFlat.Basic`. In codimension one those neighbourhoods are bicollars, and the construction
reverses.
-/

/-!
### The codimension-one comparison
-/

/-- **A locally flat embedding of codimension one is locally bicollared.** Each flattening chart,
shrunk to a box, is a bicollar of the part of the map it sees. -/
theorem IsLocallyFlat.isLocallyBicollared (h : IsLocallyFlat F ℝ f) : IsLocallyBicollared f :=
  fun x =>
    let ⟨U, hU, hxU, b, hb, hb0⟩ := h.exists_isOpenEmbedding_prod x
    ⟨U, hU, hxU, b, hb, hb0⟩

/-- A bicollar makes its collared map locally flat, provided the domain is charted on `F`: the
collar is an open embedding of `N × ℝ`, and the standard slice `N → N × ℝ` is locally flat there
by `TauCeti.isLocallyFlat_prodMkLeft`. -/
theorem IsBicollar.isLocallyFlat [ChartedSpace F N] {b : N × ℝ → M} (h : IsBicollar f b) :
    IsLocallyFlat F ℝ f := by
  have hfb : f = b ∘ fun y : N => (y, (0 : ℝ)) := funext fun y => (h.apply_zero y).symm
  rw [hfb]
  exact isLocallyFlat_prodMkLeft.isOpenEmbedding_comp h.isOpenEmbedding

/-- A bicollared map whose domain is charted on `F` is locally flat with one-dimensional
complementary model. -/
theorem IsBicollared.isLocallyFlat [ChartedSpace F N] (h : IsBicollared f) :
    IsLocallyFlat F ℝ f :=
  let ⟨_, hb⟩ := h; hb.isLocallyFlat

/-- A locally bicollared *embedding* whose domain is charted on `F` is locally flat with
one-dimensional complementary model. Being an embedding is a genuine extra hypothesis, since
bicollars are local data on the domain. -/
theorem IsLocallyBicollared.isLocallyFlat [ChartedSpace F N] (h : IsLocallyBicollared f)
    (hf : IsEmbedding f) : IsLocallyFlat F ℝ f := by
  refine IsLocallyFlat.of_forall_exists_isOpen hf fun x => ?_
  obtain ⟨U, hU, hxU, hb⟩ := h x
  let _ : ChartedSpace F U := TopologicalSpace.Opens.instChartedSpace ⟨U, hU⟩
  exact ⟨U, hU, hxU, hb.isLocallyFlat⟩

/-- **Local flatness in codimension one is exactly local bicollaring, for an embedding.** The
embedding hypothesis is not automatic: bicollars are local data, so a non-injective immersion of
a line into the plane is locally bicollared without being an embedding. -/
theorem isLocallyFlat_iff_isEmbedding_and_isLocallyBicollared [ChartedSpace F N] :
    IsLocallyFlat F ℝ f ↔ IsEmbedding f ∧ IsLocallyBicollared f :=
  ⟨fun h => ⟨h.isEmbedding, h.isLocallyBicollared⟩, fun h => h.2.isLocallyFlat h.1⟩

end TauCeti
