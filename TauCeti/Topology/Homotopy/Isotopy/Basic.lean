/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Basic

/-!
# Isotopy and ambient isotopy

An *isotopy* between two continuous maps is a homotopy whose level-preserving total map
`I × X → I × Y` is a topological embedding, and an *ambient isotopy* of a space `Y` is a
homotopy from the identity of `Y` whose level-preserving total map `I × Y → I × Y` is a
homeomorphism. These are the point-set foundations that the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology`) asks for once, in full generality, before specialising.
The definitions follow Burde--Zieschang, *Knots*, Chapter 1, Definitions 1.1 and 1.2,
generalized to this continuous topological setting. The non-ambient relation is the general
point-set notion of isotopy; later knot-equivalence foundations should use ambient isotopy,
specialized as needed to smooth embeddings `S¹ ↪ M`. Later geometric-topology foundations
specialize these isotopy and ambient-isotopy notions as appropriate for locally flat isotopy,
diffeotopies, and concordance.

## A warning: non-ambient isotopy is degenerate for knots

The non-ambient relation `Isotopy`/`Isotopic` is *not* the right equivalence for classical knot
theory. It records a moving embedded image, but it need not extend to a motion of the ambient
space and therefore need not preserve knot complements. *Ambient* isotopy is the relation with
knot-theoretic content: an ambient isotopy induces a homeomorphism of complements, so knot
invariants must be built on `AmbientIsotopy` and the `AmbientIsotopic` equivalence from
`TauCeti.Topology.Homotopy.AmbientIsotopic.Basic`, not on `Isotopy`/`Isotopic`. See
Burde--Zieschang, *Knots*, Chapter 1 §A, where ambient isotopy (Definition 1.2) is introduced
after the naive isotopy of Definition 1.1.

## Main definitions

* `TauCeti.Isotopy f₀ f₁`: a homotopy from `f₀` to `f₁` whose total level-preserving map is a
  topological embedding.
* `TauCeti.Isotopic f₀ f₁`: the proposition that such an isotopy exists. This is the reusable
  general non-ambient relation; knot-equivalence layers should instead use `AmbientIsotopic` from
  `TauCeti.Topology.Homotopy.AmbientIsotopic.Basic`.
* `TauCeti.AmbientIsotopy Y`: a homotopy of `Y` from the identity whose total
  level-preserving map is a homeomorphism.
* `TauCeti.AmbientIsotopy.trans` / `TauCeti.AmbientIsotopy.symm`: the composition and inverse of
  ambient isotopies, the closure operations that make ambient isotopy an equivalence relation.

## Main results

* `TauCeti.Isotopy.isEmbedding_left` / `isEmbedding_right`: the endpoints of an isotopy are
  embeddings.
* `TauCeti.Isotopy.toHomotopyWith`: an isotopy is, in particular, a Mathlib homotopy through
  embeddings.
* `TauCeti.Isotopic.refl` / `TauCeti.Isotopic.symm` / `TauCeti.Isotopic.trans`: isotopy is
  reflexive on embeddings, symmetric, and transitive.
* `TauCeti.Isotopic.homotopic`: isotopic maps are homotopic.
* `TauCeti.AmbientIsotopy.isotopy` / `TauCeti.AmbientIsotopy.isotopic`: an ambient isotopy
  carries any embedding `f` to the isotopic embedding `Φ.final ∘ f`. This is the "ambient
  isotopy implies isotopy" direction.
* `TauCeti.AmbientIsotopy.final_trans` / `TauCeti.AmbientIsotopy.symm_final_final` /
  `TauCeti.AmbientIsotopy.final_symm_final`: the final maps of the composite and inverse ambient
  isotopies, and that the inverse final map undoes the original on both sides.
-/

public section

namespace TauCeti

open unitInterval ContinuousMap Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem isEmbedding_const_prod (t : I) : IsEmbedding fun x : X => (t, x) :=
  IsEmbedding.of_comp (by fun_prop) continuous_snd (by
    convert (IsEmbedding.id : IsEmbedding (id : X → X)) using 1
    ext x
    rfl)

/-- A map is inducing if its restrictions to the preimages of a closed cover of the codomain are
inducing. (The closedness of the cover in the *codomain* is what makes the gluing work, even
though the analogous statement for an arbitrary closed cover of the domain fails.) -/
private theorem isInducing_of_isClosed_cover {Z W : Type*} [TopologicalSpace Z]
    [TopologicalSpace W] {f : Z → W} (hf : Continuous f) {D₁ D₂ : Set W}
    (h₁ : IsClosed D₁) (h₂ : IsClosed D₂) (hcov : D₁ ∪ D₂ = Set.univ)
    (hi₁ : IsInducing ((f ⁻¹' D₁).domRestrict f)) (hi₂ : IsInducing ((f ⁻¹' D₂).domRestrict f)) :
    IsInducing f := by
  rw [isInducing_iff_nhds]
  intro z
  refine le_antisymm ((hf.tendsto z).le_comap) ?_
  rw [Filter.le_def]
  intro U hU
  rw [Filter.mem_comap]
  have extract : ∀ D : Set W, IsInducing ((f ⁻¹' D).domRestrict f) → f z ∈ D →
      ∃ V ∈ 𝓝 (f z), f ⁻¹' V ∩ f ⁻¹' D ⊆ U := by
    intro D hi hzD
    rw [isInducing_iff_nhds] at hi
    have hUsub : Subtype.val ⁻¹' U ∈ 𝓝 (⟨z, hzD⟩ : f ⁻¹' D) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hU
    rw [hi ⟨z, hzD⟩, Filter.mem_comap] at hUsub
    obtain ⟨V, hV, hVsub⟩ := hUsub
    refine ⟨V, hV, ?_⟩
    rintro y ⟨hyV, hyD⟩
    -- The restricted map applies definitionally to `f y`, so this `show` only changes
    -- `hyV : f y ∈ V` into the preimage-membership type expected by `hVsub`.
    exact hVsub (show ((f ⁻¹' D).domRestrict f) ⟨y, hyD⟩ ∈ V from hyV)
  have wstep : ∀ D : Set W, IsClosed D → IsInducing ((f ⁻¹' D).domRestrict f) →
      ∃ V ∈ 𝓝 (f z), f ⁻¹' V ∩ f ⁻¹' D ⊆ U := by
    intro D hD hi
    by_cases hzD : f z ∈ D
    · exact extract D hi hzD
    · exact ⟨Dᶜ, hD.isOpen_compl.mem_nhds hzD, by rintro y ⟨hyc, hyd⟩; exact absurd hyd hyc⟩
  obtain ⟨V₁, hV₁, hs₁⟩ := wstep D₁ h₁ hi₁
  obtain ⟨V₂, hV₂, hs₂⟩ := wstep D₂ h₂ hi₂
  refine ⟨V₁ ∩ V₂, Filter.inter_mem hV₁ hV₂, ?_⟩
  rw [Set.preimage_inter]
  intro y hy
  have hycov : y ∈ f ⁻¹' D₁ ∪ f ⁻¹' D₂ := by
    rw [← Set.preimage_union, hcov]; exact Set.mem_univ y
  rcases hycov with h | h
  · exact hs₁ ⟨hy.1, h⟩
  · exact hs₂ ⟨hy.2, h⟩

/-- If `e` is an embedding parametrising the preimage `f ⁻¹' D` and `f ∘ e` is inducing, then the
restriction of `f` to `f ⁻¹' D` is inducing. -/
private theorem isInducing_restrict_of_embedding {Z W A : Type*} [TopologicalSpace Z]
    [TopologicalSpace W] [TopologicalSpace A] {f : Z → W} {D : Set W} {e : A → Z}
    (he : IsEmbedding e) (hrange : Set.range e = f ⁻¹' D) (hfe : IsInducing (f ∘ e)) :
    IsInducing ((f ⁻¹' D).domRestrict f) := by
  let φ : A ≃ₜ (f ⁻¹' D) := he.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have hφ_apply (a : A) : (φ a : Z) = e a := by
    simp only [φ, Homeomorph.trans_apply]
    simp [Homeomorph.setCongr]
  have hcomp : (f ⁻¹' D).domRestrict f ∘ φ = f ∘ e := by
    funext a
    exact congrArg f (hφ_apply a)
  have h0 : IsInducing ((f ⁻¹' D).domRestrict f ∘ φ) := hcomp ▸ hfe
  have h2 := h0.comp φ.symm.isInducing
  rwa [Function.comp_assoc, Homeomorph.self_comp_symm, Function.comp_id] at h2

/-- An **isotopy** between `f₀ f₁ : C(X, Y)` is a homotopy whose level-preserving total map
`I × X → I × Y` is a topological embedding.

As an equivalence this non-ambient relation is too coarse for classical knot theory: it need not
extend to a motion of the ambient space and therefore need not preserve knot complements. Use
`AmbientIsotopy`/`AmbientIsotopic` for knot equivalence; see the module docstring and the
Burde--Zieschang reference. -/
structure Isotopy (f₀ f₁ : C(X, Y)) extends Homotopy f₀ f₁ where
  /-- the level-preserving total map of an isotopy is a topological embedding -/
  isEmbedding_total' : IsEmbedding fun p : I × X => (p.1, toFun p)

namespace Isotopy

variable {f₀ f₁ : C(X, Y)}

instance instFunLike : FunLike (Isotopy f₀ f₁) (I × X) Y where
  coe F := F.toFun
  coe_injective F G h := by
    obtain ⟨F, _⟩ := F
    obtain ⟨G, _⟩ := G
    congr
    exact DFunLike.coe_injective h

/-- The level-preserving total map of an isotopy. -/
@[expose] def totalMap (F : Isotopy f₀ f₁) : C(I × X, I × Y) :=
  ⟨fun p => (p.1, F.toHomotopy p), by fun_prop⟩

@[simp]
theorem totalMap_apply (F : Isotopy f₀ f₁) (p : I × X) :
    F.totalMap p = (p.1, F.toHomotopy p) := rfl

@[simp]
theorem apply_zero (F : Isotopy f₀ f₁) (x : X) : F (0, x) = f₀ x :=
  F.map_zero_left x

@[simp]
theorem apply_one (F : Isotopy f₀ f₁) (x : X) : F (1, x) = f₁ x :=
  F.map_one_left x

/-- The level-preserving total map of an isotopy is a topological embedding. -/
theorem isEmbedding_total (F : Isotopy f₀ f₁) : IsEmbedding F.totalMap :=
  F.isEmbedding_total'

/-- Every time-slice of an isotopy is a topological embedding. -/
theorem isEmbedding_apply (F : Isotopy f₀ f₁) (t : I) :
    IsEmbedding fun x => F.toHomotopy (t, x) := by
  let k : Y → I × Y := fun y => (t, y)
  have hk_cont : Continuous k := by fun_prop
  have hcomp : IsEmbedding (k ∘ fun x => F.toHomotopy (t, x)) := by
    convert F.isEmbedding_total.comp (isEmbedding_const_prod (X := X) t) using 1
    ext x <;> rfl
  exact IsEmbedding.of_comp (by fun_prop) hk_cont hcomp

/-- An isotopy is, in particular, a `HomotopyWith` whose slices are embeddings. -/
def toHomotopyWith (F : Isotopy f₀ f₁) :
    HomotopyWith f₀ f₁ fun g : C(X, Y) => IsEmbedding g where
  toHomotopy := F.toHomotopy
  prop' := F.isEmbedding_apply

/-- The map an isotopy starts at is a topological embedding. -/
theorem isEmbedding_left (F : Isotopy f₀ f₁) : IsEmbedding f₀ := by
  simpa using F.isEmbedding_apply 0

/-- The map an isotopy ends at is a topological embedding. -/
theorem isEmbedding_right (F : Isotopy f₀ f₁) : IsEmbedding f₁ := by
  simpa using F.isEmbedding_apply 1

/-- Value of the concatenated homotopy on the first half `[0, 1 / 2]`, with the time parameter
rescaled to `2 * t`. -/
private theorem trans_toHomotopy_apply_of_le (F : Isotopy f₀ f₁) (G : Isotopy f₁ f₂) {t : I} (x : X)
    (h : (t : ℝ) ≤ 1 / 2) : (F.toHomotopy.trans G.toHomotopy) (t, x)
      = F.toHomotopy (⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩, x) := by
  rw [Homotopy.trans_apply, dif_pos h]

/-- Value of the concatenated homotopy on the second half `[1 / 2, 1]`, with the time parameter
rescaled to `2 * t - 1`. -/
private theorem trans_toHomotopy_apply_of_not_le (F : Isotopy f₀ f₁) (G : Isotopy f₁ f₂) {t : I}
    (x : X) (h : ¬ (t : ℝ) ≤ 1 / 2) : (F.toHomotopy.trans G.toHomotopy) (t, x)
      = G.toHomotopy
          (⟨2 * t - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩, x) := by
  rw [Homotopy.trans_apply, dif_neg h]

/-- Halving reparametrisation `s ↦ s / 2 : I → I`, with image the left half `[0, 1 / 2]`. -/
private noncomputable def half (s : I) : I :=
  ⟨(s : ℝ) / 2, by constructor <;> [linarith [s.2.1]; linarith [s.2.2]]⟩

/-- Right-half reparametrisation `s ↦ s / 2 + 1 / 2 : I → I`, with image `[1 / 2, 1]`. -/
private noncomputable def halfRight (s : I) : I :=
  ⟨(s : ℝ) / 2 + 1 / 2, by constructor <;> [linarith [s.2.1]; linarith [s.2.2]]⟩

private theorem coe_half (s : I) : (half s : ℝ) = (s : ℝ) / 2 := rfl
private theorem coe_halfRight (s : I) : (halfRight s : ℝ) = (s : ℝ) / 2 + 1 / 2 := rfl

private theorem injective_half : Function.Injective half := fun a b hab =>
  Subtype.ext (by have := congrArg Subtype.val hab; simp only [coe_half] at this; linarith)

private theorem injective_halfRight : Function.Injective halfRight := fun a b hab =>
  Subtype.ext (by have := congrArg Subtype.val hab; simp only [coe_halfRight] at this; linarith)

private theorem half_left_inv (t : I) (ht : (t : ℝ) ≤ 1 / 2) :
    half (⟨2 * t, ⟨by linarith [t.2.1], by linarith [ht]⟩⟩ : I) = t := by
  apply Subtype.ext
  simp only [coe_half]
  ring

private theorem halfRight_right_inv (t : I) (ht : 1 / 2 ≤ (t : ℝ)) :
    halfRight (⟨2 * t - 1, ⟨by linarith [ht], by linarith [t.2.2]⟩⟩ : I) = t := by
  apply Subtype.ext
  simp only [coe_halfRight]
  ring

private theorem isEmbedding_half : IsEmbedding half :=
  ((Continuous.subtype_mk (by fun_prop) _).isClosedEmbedding injective_half).isEmbedding

private theorem isEmbedding_halfRight : IsEmbedding halfRight :=
  ((Continuous.subtype_mk (by fun_prop) _).isClosedEmbedding injective_halfRight).isEmbedding

private theorem range_half : Set.range half = {t : I | (t : ℝ) ≤ 1 / 2} := by
  ext t
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  refine ⟨?_, fun ht => ⟨⟨2 * t, ⟨by linarith [t.2.1], by linarith⟩⟩, ?_⟩⟩
  · rintro ⟨s, rfl⟩; rw [coe_half]; linarith [s.2.2]
  · exact half_left_inv t ht

private theorem range_halfRight : Set.range halfRight = {t : I | 1 / 2 ≤ (t : ℝ)} := by
  ext t
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  refine ⟨?_, fun ht => ⟨⟨2 * t - 1, ⟨by linarith, by linarith [t.2.2]⟩⟩, ?_⟩⟩
  · rintro ⟨s, rfl⟩; rw [coe_halfRight]; linarith [s.2.1]
  · exact halfRight_right_inv t ht

private theorem trans_half (F : Isotopy f₀ f₁) (G : Isotopy f₁ f₂) (s : I) (x : X) :
    (F.toHomotopy.trans G.toHomotopy) (half s, x) = F.toHomotopy (s, x) := by
  have h : ((half s : I) : ℝ) ≤ 1 / 2 := by rw [coe_half]; linarith [s.2.2]
  rw [trans_toHomotopy_apply_of_le _ _ _ h]
  congr 2
  apply Subtype.ext
  simp only [coe_half]; ring

private theorem trans_halfRight (F : Isotopy f₀ f₁) (G : Isotopy f₁ f₂) (s : I) (x : X) :
    (F.toHomotopy.trans G.toHomotopy) (halfRight s, x) = G.toHomotopy (s, x) := by
  by_cases h : ((halfRight s : I) : ℝ) ≤ 1 / 2
  · have hs0 : (s : ℝ) = 0 := le_antisymm (by rw [coe_halfRight] at h; linarith) s.2.1
    have hs : s = (0 : I) := Subtype.ext (by rw [hs0]; rfl)
    subst hs
    rw [trans_toHomotopy_apply_of_le _ _ _ h]
    have key : (⟨2 * ((halfRight (0 : I)) : ℝ), by simp only [coe_halfRight]; norm_num⟩ : I) = 1 :=
      Subtype.ext (by simp only [coe_halfRight]; norm_num)
    rw [key]
    simp
  · rw [trans_toHomotopy_apply_of_not_le _ _ _ h]
    congr 2
    apply Subtype.ext
    simp only [coe_halfRight]; ring

/-- Concatenate two isotopies: the result follows `F` on `[0, 1 / 2]` and `G` on `[1 / 2, 1]`,
with the time parameter rescaled linearly. The concatenated total map is an embedding because it
is one on each closed half (where it is `F`'s or `G`'s total embedding, reparametrised), and these
glue along the closed cover `{(t, y) | t ≤ 1 / 2}`, `{(t, y) | 1 / 2 ≤ t}` of the codomain. -/
noncomputable def trans {f₂ : C(X, Y)} (F : Isotopy f₀ f₁) (G : Isotopy f₁ f₂) :
    Isotopy f₀ f₂ where
  toHomotopy := F.toHomotopy.trans G.toHomotopy
  isEmbedding_total' := by
    set T : I × X → I × Y := fun p => (p.1, (F.toHomotopy.trans G.toHomotopy) p) with hT
    have hTcont : Continuous T := by fun_prop
    refine ⟨?_, ?_⟩
    · have hfst : Continuous fun q : I × Y => (q.1 : ℝ) := by fun_prop
      set D₁ : Set (I × Y) := {q | (q.1 : ℝ) ≤ 1 / 2} with hD₁def
      set D₂ : Set (I × Y) := {q | 1 / 2 ≤ (q.1 : ℝ)} with hD₂def
      have hcov : D₁ ∪ D₂ = Set.univ := by
        ext q
        simp only [hD₁def, hD₂def, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        exact le_total _ _
      have hrange₁ : Set.range (Prod.map half (id : X → X)) = T ⁻¹' D₁ := by
        rw [Set.range_prodMap, Set.range_id, range_half]; ext ⟨t, x⟩; simp [hT, hD₁def]
      have hTe₁ : T ∘ (Prod.map half (id : X → X))
          = (Prod.map half (id : Y → Y)) ∘ F.totalMap := by
        funext p; obtain ⟨s, x⟩ := p
        simp only [Function.comp_apply, Prod.map_apply, id_eq, hT, totalMap_apply]
        rw [trans_half]
      have hi₁ := isInducing_restrict_of_embedding (isEmbedding_half.prodMap IsEmbedding.id)
        hrange₁ (hTe₁ ▸ (isEmbedding_half.prodMap IsEmbedding.id).isInducing.comp
          F.isEmbedding_total.isInducing)
      have hrange₂ : Set.range (Prod.map halfRight (id : X → X)) = T ⁻¹' D₂ := by
        rw [Set.range_prodMap, Set.range_id, range_halfRight]; ext ⟨t, x⟩; simp [hT, hD₂def]
      have hTe₂ : T ∘ (Prod.map halfRight (id : X → X))
          = (Prod.map halfRight (id : Y → Y)) ∘ G.totalMap := by
        funext p; obtain ⟨s, x⟩ := p
        simp only [Function.comp_apply, Prod.map_apply, id_eq, hT, totalMap_apply]
        rw [trans_halfRight]
      have hi₂ := isInducing_restrict_of_embedding (isEmbedding_halfRight.prodMap IsEmbedding.id)
        hrange₂ (hTe₂ ▸ (isEmbedding_halfRight.prodMap IsEmbedding.id).isInducing.comp
          G.isEmbedding_total.isInducing)
      exact isInducing_of_isClosed_cover hTcont (isClosed_le hfst continuous_const)
        (isClosed_le continuous_const hfst) hcov hi₁ hi₂
    · rintro ⟨t, x⟩ ⟨t', x'⟩ hpp
      have ht : t = t' := congrArg Prod.fst hpp
      subst ht
      have hH : (F.toHomotopy.trans G.toHomotopy) (t, x)
          = (F.toHomotopy.trans G.toHomotopy) (t, x') := congrArg Prod.snd hpp
      by_cases h : (t : ℝ) ≤ 1 / 2
      · rw [trans_toHomotopy_apply_of_le _ _ _ h, trans_toHomotopy_apply_of_le _ _ _ h] at hH
        exact Prod.ext rfl ((F.isEmbedding_apply _).injective hH)
      · rw [trans_toHomotopy_apply_of_not_le _ _ _ h,
          trans_toHomotopy_apply_of_not_le _ _ _ h] at hH
        exact Prod.ext rfl ((G.isEmbedding_apply _).injective hH)

/-- The value of a concatenated isotopy is given by the first isotopy on `[0, 1 / 2]`
and by the second isotopy on `[1 / 2, 1]`, with the time parameter rescaled linearly. -/
theorem trans_apply {f₂ : C(X, Y)} (F : Isotopy f₀ f₁) (G : Isotopy f₁ f₂) (x : I × X) :
    (F.trans G) x =
      if h : (x.1 : ℝ) ≤ 1 / 2 then
        F (⟨2 * x.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
      else
        G (⟨2 * x.1 - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
  Homotopy.trans_apply F.toHomotopy G.toHomotopy x

instance instHomotopyLike : HomotopyLike (Isotopy f₀ f₁) f₀ f₁ where
  map_continuous F := F.continuous_toFun
  map_zero_left F := F.map_zero_left
  map_one_left F := F.map_one_left

end Isotopy

/-- Two maps `f₀ f₁ : C(X, Y)` are **isotopic** if there is an isotopy between them.

Warning: for classical knot theory this non-ambient relation is too coarse: it need not preserve
knot complements, so knot invariants must be built on `AmbientIsotopic`, not on `Isotopic`. -/
@[expose] def Isotopic (f₀ f₁ : C(X, Y)) : Prop :=
  Nonempty (Isotopy f₀ f₁)

namespace Isotopic

variable {f₀ f₁ : C(X, Y)}

/-- An isotopy witnesses that its endpoints are isotopic. -/
theorem of_isotopy (F : Isotopy f₀ f₁) : Isotopic f₀ f₁ := ⟨F⟩

/-- Isotopy is reflexive on embeddings. -/
theorem refl (f : C(X, Y)) (hf : IsEmbedding f) : Isotopic f f :=
  ⟨{ toHomotopy := Homotopy.refl f,
      isEmbedding_total' := IsEmbedding.id.prodMap hf }⟩

/-- Isotopy is symmetric. -/
@[symm]
theorem symm (h : Isotopic f₀ f₁) : Isotopic f₁ f₀ :=
  ⟨{ toHomotopy := h.some.toHomotopy.symm,
      isEmbedding_total' := by
        let e : I × X ≃ₜ I × X :=
          unitInterval.symmHomeomorph.prodCongr (Homeomorph.refl X)
        let e' : I × Y ≃ₜ I × Y :=
          unitInterval.symmHomeomorph.prodCongr (Homeomorph.refl Y)
        convert e'.isEmbedding.comp (h.some.isEmbedding_total.comp e.isEmbedding) using 1
        ext p
        · simp [Function.comp_def, Isotopy.totalMap, e, e', unitInterval.symm_symm]
        · exact congrArg h.some.toHomotopy (by ext <;> simp [e]) }⟩

/-- Isotopy is transitive. -/
@[trans]
theorem trans {f₂ : C(X, Y)} (h₀₁ : Isotopic f₀ f₁) (h₁₂ : Isotopic f₁ f₂) : Isotopic f₀ f₂ :=
  ⟨h₀₁.some.trans h₁₂.some⟩

/-- The left endpoint of an isotopy relation is an embedding. -/
theorem isEmbedding_left (h : Isotopic f₀ f₁) : IsEmbedding f₀ :=
  Isotopy.isEmbedding_left h.some

/-- The right endpoint of an isotopy relation is an embedding. -/
theorem isEmbedding_right (h : Isotopic f₀ f₁) : IsEmbedding f₁ :=
  Isotopy.isEmbedding_right h.some

/-- Isotopic maps are homotopic. -/
theorem homotopic (h : Isotopic f₀ f₁) : Homotopic f₀ f₁ :=
  ⟨h.some.toHomotopy⟩

/-- Isotopic maps are homotopic through embeddings in Mathlib's generic API. -/
theorem homotopicWith (h : Isotopic f₀ f₁) :
    HomotopicWith f₀ f₁ fun g : C(X, Y) => IsEmbedding g :=
  ⟨h.some.toHomotopyWith⟩

end Isotopic

/-- An **ambient isotopy** of `Y` is a homotopy from the identity map of `Y` whose
level-preserving total map is a homeomorphism. The time-`1` map `Φ.final` is the resulting
homeomorphism. -/
structure AmbientIsotopy (Y : Type*) [TopologicalSpace Y] extends C(I × Y, Y) where
  /-- the level-preserving total map of the ambient isotopy is a homeomorphism -/
  isHomeomorph_total' : IsHomeomorph fun p : I × Y => (p.1, toFun p)
  /-- the ambient isotopy starts at the identity of `Y` -/
  map_zero_left' : ∀ y, toFun (0, y) = y

namespace AmbientIsotopy

variable (Φ : AmbientIsotopy Y)

/-- The level-preserving total map of an ambient isotopy. -/
@[expose] def totalMap : C(I × Y, I × Y) :=
  ⟨fun p => (p.1, Φ.toContinuousMap p), by fun_prop⟩

@[simp]
theorem totalMap_apply (p : I × Y) : Φ.totalMap p = (p.1, Φ.toContinuousMap p) := rfl

/-- The level-preserving total map of an ambient isotopy is a homeomorphism. -/
theorem isHomeomorph_total : IsHomeomorph Φ.totalMap :=
  Φ.isHomeomorph_total'

/-- Every time-slice of an ambient isotopy is a self-homeomorphism of `Y`. -/
theorem isHomeomorph_apply (t : I) : IsHomeomorph fun y => Φ.toContinuousMap (t, y) := by
  rw [isHomeomorph_iff_isEmbedding_surjective]
  constructor
  · let k : Y → I × Y := fun y => (t, y)
    have hk_cont : Continuous k := by fun_prop
    have hcomp : IsEmbedding (k ∘ fun y => Φ.toContinuousMap (t, y)) := by
      convert Φ.isHomeomorph_total.isEmbedding.comp (isEmbedding_const_prod (X := Y) t) using 1
      ext y <;> rfl
    exact IsEmbedding.of_comp (by fun_prop) hk_cont hcomp
  · intro y
    rcases Φ.isHomeomorph_total.surjective (t, y) with ⟨p, hp⟩
    refine ⟨p.2, ?_⟩
    have ht : p.1 = t := congrArg Prod.fst hp
    rw [← ht]
    exact congrArg Prod.snd hp

/-- The ambient isotopy starts at the identity of `Y`. -/
@[simp]
theorem map_zero_left (y : Y) : Φ.toContinuousMap (0, y) = y :=
  Φ.map_zero_left' y

/-- The time-`1` homeomorphism produced by an ambient isotopy, as a continuous map. -/
@[expose] def final : C(Y, Y) := ⟨fun y => Φ.toContinuousMap (1, y), by fun_prop⟩

@[simp]
theorem final_apply (y : Y) : Φ.final y = Φ.toContinuousMap (1, y) := rfl

/-- The final map produced by an ambient isotopy is a homeomorphism. -/
theorem isHomeomorph_final : IsHomeomorph Φ.final :=
  Φ.isHomeomorph_apply 1

/-- The time-`t` self-homeomorphism bundled as a `Homeomorph`. -/
@[expose] noncomputable def homeomorph (t : I) : Y ≃ₜ Y :=
  IsHomeomorph.homeomorph (fun y => Φ.toContinuousMap (t, y)) (Φ.isHomeomorph_apply t)

@[simp]
theorem homeomorph_apply (t : I) (y : Y) : Φ.homeomorph t y = Φ.toContinuousMap (t, y) :=
  rfl

/-- The time-`1` homeomorphism produced by an ambient isotopy. -/
@[expose] noncomputable def finalHomeomorph : Y ≃ₜ Y :=
  Φ.homeomorph 1

@[simp]
theorem finalHomeomorph_apply (y : Y) : Φ.finalHomeomorph y = Φ.final y :=
  rfl

/-- The constant ambient isotopy at the identity. -/
@[expose] def refl (Y : Type*) [TopologicalSpace Y] : AmbientIsotopy Y where
  toContinuousMap := ⟨fun p => p.2, by fun_prop⟩
  isHomeomorph_total' := .id
  map_zero_left' _ := rfl

/-- The final map of the constant ambient isotopy is the identity. -/
theorem final_refl (y : Y) : (refl Y).final y = y := rfl

/-- Every time slice of the constant ambient isotopy is the identity homeomorphism. -/
@[simp]
theorem homeomorph_refl (t : I) : (refl Y).homeomorph t = Homeomorph.refl Y := by
  ext y
  rw [homeomorph_apply, Homeomorph.refl_apply]
  rfl

/-- The final homeomorphism of the constant ambient isotopy is the identity. -/
@[simp]
theorem finalHomeomorph_refl : (refl Y).finalHomeomorph = Homeomorph.refl Y := by
  rw [finalHomeomorph, homeomorph_refl]

instance : Inhabited (AmbientIsotopy Y) := ⟨refl Y⟩

private theorem isotopy_totalMap_eq {f : C(X, Y)} :
    (fun p : I × X => (p.1, Φ.toContinuousMap (p.1, f p.2))) =
      Φ.totalMap ∘ Prod.map id f :=
  rfl

/-- An ambient isotopy carries any embedding `f` to the embedding `Φ.final ∘ f` through an
explicit isotopy: at time `t` the embedding is the homeomorphism `Φ t` postcomposed with `f`. -/
@[expose] def isotopy {f : C(X, Y)} (hf : IsEmbedding f) : Isotopy f (Φ.final.comp f) where
  toHomotopy :=
    { toFun := fun p => Φ.toContinuousMap (p.1, f p.2)
      continuous_toFun := by fun_prop
      map_zero_left := fun x => Φ.map_zero_left (f x)
      map_one_left := fun _ => rfl }
  isEmbedding_total' := by
    rw [isotopy_totalMap_eq]
    exact Φ.isHomeomorph_total.isEmbedding.comp (IsEmbedding.id.prodMap hf)

@[simp]
theorem isotopy_apply {f : C(X, Y)} (hf : IsEmbedding f) (t : I) (x : X) :
    Φ.isotopy hf (t, x) = Φ.toContinuousMap (t, f x) :=
  rfl

/-- **Ambient isotopy implies isotopy**: an ambient isotopy of `Y` carries any embedding `f`
into `Y` to the isotopic embedding `Φ.final ∘ f`. -/
theorem isotopic {f : C(X, Y)} (hf : IsEmbedding f) : Isotopic f (Φ.final.comp f) :=
  ⟨Φ.isotopy hf⟩

/-- The level-preserving total map of an ambient isotopy, bundled as a self-homeomorphism of
`I × Y`. -/
@[expose] noncomputable def totalHomeomorph : (I × Y) ≃ₜ (I × Y) :=
  IsHomeomorph.homeomorph Φ.totalMap Φ.isHomeomorph_total

@[simp]
theorem totalHomeomorph_apply (p : I × Y) :
    Φ.totalHomeomorph p = (p.1, Φ.toContinuousMap p) := rfl

/-- The inverse total homeomorphism preserves the time coordinate. -/
theorem totalHomeomorph_symm_fst (p : I × Y) : (Φ.totalHomeomorph.symm p).1 = p.1 := by
  have h := Φ.totalHomeomorph.apply_symm_apply p
  rw [totalHomeomorph_apply] at h
  exact (Prod.ext_iff.mp h).1

/-- **Composition of ambient isotopies**: follow `Φ_t` then `Ψ_t` at each time `t`. -/
@[expose] def trans (Ψ : AmbientIsotopy Y) : AmbientIsotopy Y where
  toContinuousMap := ⟨fun p => Ψ.toContinuousMap (p.1, Φ.toContinuousMap p), by fun_prop⟩
  isHomeomorph_total' := by
    have heq : (fun p : I × Y => (p.1, Ψ.toContinuousMap (p.1, Φ.toContinuousMap p)))
        = ⇑Ψ.totalMap ∘ ⇑Φ.totalMap := by
      funext p
      simp [Function.comp, totalMap_apply]
    rw [heq]
    exact Ψ.isHomeomorph_total.comp Φ.isHomeomorph_total
  map_zero_left' y := by
    -- the composite's `toFun` at time `0` is `Ψ (0, Φ (0, y))`, which both factors fix.
    simp

@[simp]
theorem trans_apply (Ψ : AmbientIsotopy Y) (p : I × Y) :
    (Φ.trans Ψ).toContinuousMap p = Ψ.toContinuousMap (p.1, Φ.toContinuousMap p) := rfl

/-- The final map of the composite ambient isotopy `Φ.trans Ψ` is the composition of the final
maps of `Φ` and `Ψ`: at the endpoint it is `Ψ.final ∘ Φ.final`. -/
@[simp]
theorem final_trans (Ψ : AmbientIsotopy Y) (y : Y) :
    (Φ.trans Ψ).final y = Ψ.final (Φ.final y) := rfl

/-- Every time slice of a composite ambient isotopy is the composite of the corresponding
time slices. -/
@[simp]
theorem homeomorph_trans (Ψ : AmbientIsotopy Y) (t : I) :
    (Φ.trans Ψ).homeomorph t = (Φ.homeomorph t).trans (Ψ.homeomorph t) := by
  ext y
  rw [homeomorph_apply, trans_apply, Homeomorph.trans_apply, homeomorph_apply, homeomorph_apply]

/-- The final homeomorphism of a composite ambient isotopy is the composite of the final
homeomorphisms. -/
@[simp]
theorem finalHomeomorph_trans (Ψ : AmbientIsotopy Y) :
    (Φ.trans Ψ).finalHomeomorph = Φ.finalHomeomorph.trans Ψ.finalHomeomorph := by
  rw [finalHomeomorph, finalHomeomorph, finalHomeomorph, homeomorph_trans]

/-- **Inverse of an ambient isotopy**: undo `Φ_t` at each time `t`. -/
@[expose] noncomputable def symm : AmbientIsotopy Y where
  toContinuousMap := ⟨fun p => (Φ.totalHomeomorph.symm p).2,
    continuous_snd.comp Φ.totalHomeomorph.symm.continuous⟩
  isHomeomorph_total' := by
    have heq : (fun p : I × Y => (p.1, (Φ.totalHomeomorph.symm p).2))
        = ⇑Φ.totalHomeomorph.symm := by
      funext p
      exact Prod.ext (Φ.totalHomeomorph_symm_fst p).symm rfl
    rw [heq]
    exact Φ.totalHomeomorph.symm.isHomeomorph
  map_zero_left' y := by
    have h0 : Φ.totalHomeomorph (0, y) = (0, y) := by
      rw [totalHomeomorph_apply, Φ.map_zero_left]
    have hsymm : Φ.totalHomeomorph.symm (0, y) = (0, y) :=
      Φ.totalHomeomorph.symm_apply_eq.mpr h0.symm
    simp [hsymm]

@[simp]
theorem symm_apply (p : I × Y) :
    Φ.symm.toContinuousMap p = (Φ.totalHomeomorph.symm p).2 := rfl

/-- The inverse ambient isotopy undoes the original: its final map is a left inverse of the
original final map. -/
theorem symm_final_final (y : Y) : Φ.symm.final (Φ.final y) = y := by
  have h1 : Φ.totalHomeomorph (1, y) = (1, Φ.toContinuousMap (1, y)) := by
    rw [totalHomeomorph_apply]
  simp only [final_apply, symm_apply]
  rw [Φ.totalHomeomorph.symm_apply_eq.mpr h1.symm]

/-- The original ambient isotopy undoes its inverse: the original final map is a left inverse of
the inverse final map. -/
theorem final_symm_final (y : Y) : Φ.final (Φ.symm.final y) = y := by
  have hfst : (Φ.totalHomeomorph.symm (1, y)).1 = 1 := Φ.totalHomeomorph_symm_fst (1, y)
  have happ := Φ.totalHomeomorph.apply_symm_apply (1, y)
  rw [totalHomeomorph_apply] at happ
  have hpair : ((1 : I), (Φ.totalHomeomorph.symm (1, y)).2) = Φ.totalHomeomorph.symm (1, y) :=
    Prod.ext hfst.symm rfl
  simp only [final_apply, symm_apply]
  rw [hpair]
  exact (Prod.ext_iff.mp happ).2

/-- Every time slice of the inverse ambient isotopy is the inverse of the corresponding
time slice. -/
@[simp]
theorem homeomorph_symm (t : I) : Φ.symm.homeomorph t = (Φ.homeomorph t).symm := by
  ext y
  symm
  apply (Φ.homeomorph t).symm_apply_eq.mpr
  have hfst : (Φ.totalHomeomorph.symm (t, y)).1 = t := Φ.totalHomeomorph_symm_fst (t, y)
  have happ := Φ.totalHomeomorph.apply_symm_apply (t, y)
  rw [totalHomeomorph_apply] at happ
  have hpair : (t, (Φ.totalHomeomorph.symm (t, y)).2) = Φ.totalHomeomorph.symm (t, y) :=
    Prod.ext hfst.symm rfl
  simp only [homeomorph_apply, symm_apply]
  rw [hpair]
  exact (Prod.ext_iff.mp happ).2.symm

/-- The final homeomorphism of the inverse ambient isotopy is the inverse final homeomorphism. -/
@[simp]
theorem finalHomeomorph_symm : Φ.symm.finalHomeomorph = Φ.finalHomeomorph.symm := by
  rw [finalHomeomorph, finalHomeomorph, homeomorph_symm]

end AmbientIsotopy

end TauCeti
