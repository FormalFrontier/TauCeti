/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
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
`S³` that is *not* locally bicollared, since the two sides of a bicollar would have to be the two
complementary regions, and one of them is not simply connected.

The file proves both directions of the comparison.

* **Local flatness gives local product neighbourhoods.**
  `TauCeti.IsLocallyFlat.exists_isOpenEmbedding_prod` shrinks a flattening chart until its target
  is a box `u ×ˢ Metric.ball 0 r`, and then re-reads that box as a product with the whole
  complementary model, through Mathlib's homeomorphism between a normed space and a ball. Stating
  it for a general normed complementary model costs nothing: a flattening chart already *is* a
  local trivialisation, and it is only the *global* patching that is codimension-sensitive.
  Specialised to a one-dimensional complementary model this is
  `TauCeti.IsLocallyFlat.isLocallyBicollared`.
* **A bicollar is a local flattening.** `TauCeti.IsBicollar.isLocallyFlat` runs the comparison
  backwards: a collared map factors through the standard slice `N → N × ℝ`, which is locally flat
  once `N` is charted on `F`, and local flatness is stable under composing with an open embedding.
  Needing the domain to be charted on `F` is where the "an `(n-1)`-manifold in an `n`-manifold" of
  the informal statement enters.

Together they give `TauCeti.isLocallyFlat_iff_isLocallyBicollared`: over a domain charted on `F`,
a map is locally flat with one-dimensional complementary model exactly when it is an embedding
that is locally bicollared. The embedding hypothesis cannot be dropped: a figure-eight immersion
of a line into the plane is locally bicollared and is not an embedding, since bicollars only see
the domain locally.

This is the codimension-one collaring bullet of layer 2 of the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`). What remains of that bullet is Brown's global
theorem, that a locally bicollared *closed* subset is bicollared, and its consequence that a
locally flat `(n-1)`-sphere in `Sⁿ` is bicollared; those are genuinely global and are not proved
here. Positive-codimension normal bundles, the companion notion, are flagged by the roadmap as a
dependency to be taken from elsewhere rather than built in this layer, which is why only the local
product statement above is proved in general codimension and only codimension one carries a name.

## Main definitions

* `TauCeti.IsBicollar`: an open embedding `N × ℝ → M` whose zero slice is a given map.
* `TauCeti.IsBicollared`: admitting a bicollar.
* `TauCeti.IsLocallyBicollared`: every point of the domain has an open neighbourhood on which the
  restriction is bicollared.

The last two are `def`s, so `TauCeti.isBicollared_iff` and `TauCeti.isLocallyBicollared_iff` are
what unfolds them downstream.

## Main results

* `TauCeti.IsSliceChart.exists_target_eq`: a slice chart can be shrunk to have any prescribed open
  subset of its target as its target.
* `TauCeti.IsLocallyFlat.exists_isOpenEmbedding_prod`: a locally flat embedding with normed
  complementary model has local product neighbourhoods, in any codimension.
* `TauCeti.IsLocallyFlat.isLocallyBicollared`: **a locally flat embedding of codimension one is
  locally bicollared.**
* `TauCeti.IsBicollar.isLocallyFlat`, `TauCeti.IsLocallyBicollared.isLocallyFlat` and
  `TauCeti.isLocallyFlat_iff_isLocallyBicollared`: the converse, and the resulting
  characterisation.
* `TauCeti.IsBicollar.range_diff_range_eq_union` and
  `TauCeti.IsBicollar.disjoint_image_Ioi_Iio`: the two sides of a bicollar are disjoint and cover
  the complement of the image inside the collar.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341, for the global collaring theorem this is the local half of.
* R. Daverman and G. Venema, *Embeddings in Manifolds*, AMS Graduate Studies in Mathematics 106
  (2009), Chapter 2, for bicollars and their role in codimension one.
-/

public section

namespace TauCeti

open Metric Set Topology

variable {M N N' P F F' : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [TopologicalSpace N'] [TopologicalSpace P] [TopologicalSpace F] [TopologicalSpace F']

/-!
### Shrinking a slice chart

A slice chart flattens a set onto a model slice relative to its own target, so it stays a slice
chart after the target is cut down to any open subset. This is the shrinking step behind every
local product statement below.
-/

/-- A slice chart can be shrunk so that its target becomes a prescribed open subset of the old
target, without changing the map. -/
theorem IsSliceChart.exists_target_eq {φ : OpenPartialHomeomorph M F} {S : Set F} {A : Set M}
    (h : IsSliceChart φ S A) {T : Set F} (hT : IsOpen T) (hTφ : T ⊆ φ.target) :
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

/-- Being bicollared spelled out: some open embedding of `N × ℝ` has `f` as its zero slice. This
is the characterisation to use downstream, where the definition of `TauCeti.IsBicollared` is not
unfolded. -/
theorem isBicollared_iff : IsBicollared f ↔ ∃ b : N × ℝ → M, IsBicollar f b := Iff.rfl

/-- Being locally bicollared spelled out: every point of the domain has an open neighbourhood on
which the restriction of the map is bicollared. This is the characterisation to use downstream,
where the definition of `TauCeti.IsLocallyBicollared` is not unfolded. -/
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

/-!
### Local flatness and local bicollaring

A flattening chart is already a local trivialisation once its target has been shrunk to a box, so
a locally flat embedding has local product neighbourhoods, in any codimension. In codimension one
those neighbourhoods are bicollars, and the construction reverses.
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
theorem isLocallyFlat_iff_isLocallyBicollared [ChartedSpace F N] :
    IsLocallyFlat F ℝ f ↔ IsEmbedding f ∧ IsLocallyBicollared f :=
  ⟨fun h => ⟨h.isEmbedding, h.isLocallyBicollared⟩, fun h => h.2.isLocallyFlat h.1⟩

end TauCeti
