/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Covering maps of a disjoint union

A family of covering maps `f i : E i → X i` assembles into a single map
`Sigma.map id f : (Σ i, E i) → Σ i, X i`, and this file proves that the assembled map is again a
covering map, identifies its fibres, and computes its monodromy.

Everything is local: the summand `Set.range (Sigma.mk i)` is open in `Σ i, X i`, the assembled
map restricts over it to `f i` up to the two open embeddings, and `IsCoveringMap` is a pointwise
condition, so the summandwise statements glue with no compatibility to check.

## Main declarations

* `TauCeti.isCoveringMap_sigmaMap`: **a disjoint union of covering maps is a covering map.**
* `TauCeti.sigmaMapFiberEquiv`: the fibre of `Sigma.map id f` over `⟨i, x⟩` is the fibre of
  `f i` over `x`.
* `TauCeti.monodromy_sigmaMap`: that identification intertwines the monodromy of `f i` along a
  path with the monodromy of `Sigma.map id f` along its image in `Σ i, X i`.

## References

This supplies the topological half of the disconnected case of Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`, whose classification of covering spaces by functors
out of the fundamental groupoid is currently available only over a path-connected base
(`TauCeti.CoveringSpace.monodromyEquivalence`).
-/

public section

namespace TauCeti

open Topology

variable {ι : Type*} {E X : ι → Type*} [∀ i, TopologicalSpace (E i)]
  [∀ i, TopologicalSpace (X i)] (f : ∀ i, E i → X i)

/-- **A disjoint union of covering maps is a covering map.** -/
theorem isCoveringMap_sigmaMap (hf : ∀ i, IsCoveringMap (f i)) :
    IsCoveringMap (Sigma.map id f) := by
  rintro ⟨i, x⟩
  -- The `i`-th summand of `Σ i, E i` is exactly the part of `Σ i, E i` lying over the `i`-th
  -- summand of `Σ i, X i`.
  have hpre : Sigma.map id f ⁻¹' Set.range (Sigma.mk i) = Set.range (Sigma.mk i) := by
    simpa using (Set.image_sigmaMk_preimage_sigmaMap Function.injective_id f i Set.univ).symm
  have hopen : IsOpen (Sigma.map id f ⁻¹' Set.range (Sigma.mk i)) := by
    rw [hpre]
    exact isOpen_range_sigmaMk
  refine IsCoveringMapOn.of_isCoveringMap_restrictPreimage _ isOpen_range_sigmaMk hopen ?_ _
    ⟨x, rfl⟩
  let hE : (Sigma.map id f ⁻¹' Set.range (Sigma.mk i) : Set (Σ i, E i)) ≃ₜ E i :=
    (Homeomorph.setCongr hpre).trans (IsEmbedding.sigmaMk (σ := E)).toHomeomorph.symm
  let hX : X i ≃ₜ (Set.range (Sigma.mk i) : Set (Σ i, X i)) :=
    (IsEmbedding.sigmaMk (σ := X)).toHomeomorph
  have heq : (Set.range (Sigma.mk i)).restrictPreimage (Sigma.map id f) =
      hX ∘ f i ∘ hE := by
    refine funext fun p ↦ Subtype.ext ?_
    obtain ⟨⟨j, e⟩, hje⟩ := p
    obtain rfl : j = i := by simpa [Sigma.map, eq_comm] using hje
    simp [Set.restrictPreimage, Sigma.map, hE, hX, Homeomorph.setCongr, Set.equivOfEq,
      Equiv.subtypeEquivProp]
  rw [heq]
  exact ((hf i).comp_homeomorph hE).homeomorph_comp hX

/-- **The fibre of a disjoint union of maps over `⟨i, x⟩` is the fibre of the `i`-th map over
`x`**, through the inclusion of the `i`-th summand. -/
noncomputable def sigmaMapFiberEquiv (i : ι) (x : X i) :
    (f i ⁻¹' {x} : Set (E i)) ≃ (Sigma.map id f ⁻¹' {(⟨i, x⟩ : Σ i, X i)} : Set (Σ i, E i)) :=
  (Equiv.Set.image _ _ sigma_mk_injective).trans <| Set.equivOfEq <| by
    simpa using Set.image_sigmaMk_preimage_sigmaMap Function.injective_id f i {x}

omit [(i : ι) → TopologicalSpace (E i)] [(i : ι) → TopologicalSpace (X i)] in
@[simp]
theorem sigmaMapFiberEquiv_apply_coe (i : ι) (x : X i) (e : (f i ⁻¹' {x} : Set (E i))) :
    (sigmaMapFiberEquiv f i x e : Σ i, E i) = ⟨i, (e : E i)⟩ :=
  (rfl)

omit [(i : ι) → TopologicalSpace (E i)] [(i : ι) → TopologicalSpace (X i)] in
/-- The inverse fibre equivalence sends an element in the `i`-th summand back to that element. -/
@[simp]
theorem sigmaMapFiberEquiv_symm_apply_mk (i : ι) (x : X i) (e : E i)
    (he : e ∈ f i ⁻¹' {x}) :
    (sigmaMapFiberEquiv f i x).symm
        ⟨⟨i, e⟩, by simpa [Sigma.map] using he⟩ = ⟨e, he⟩ := by
  apply (sigmaMapFiberEquiv f i x).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  exact (sigmaMapFiberEquiv_apply_coe f i x ⟨e, he⟩).symm

/-- The raw form of `monodromy_sigmaMap`, with the two fibre elements written as explicit pairs
rather than through `sigmaMapFiberEquiv`, so that the lifted path can be rewritten. -/
private theorem monodromy_sigmaMap_aux (hf : ∀ i, IsCoveringMap (f i)) {i : ι} {x y : X i}
    (γ : Path.Homotopic.Quotient x y) (e : (f i ⁻¹' {x} : Set (E i)))
    (he : (⟨i, (e : E i)⟩ : Σ j, E j) ∈ Sigma.map id f ⁻¹' {(⟨i, x⟩ : Σ j, X j)})
    (he' : (⟨i, (((hf i).monodromy γ e : E i))⟩ : Σ j, E j) ∈
      Sigma.map id f ⁻¹' {(⟨i, y⟩ : Σ j, X j)}) :
    (isCoveringMap_sigmaMap f hf).monodromy
        (γ.map (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(X i, Σ j, X j))) ⟨_, he⟩ = ⟨_, he'⟩ := by
  refine (isCoveringMap_sigmaMap f hf).monodromy_eq_of_map_eq
    (((hf i).liftPathQuotient γ e).map (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(E i, Σ j, E j))) ?_
  rw [← Path.Homotopic.Quotient.map_comp]
  -- The composite `Sigma.map id f ∘ Sigma.mk i` reduces to `Sigma.mk i ∘ f i`; spelling the
  -- inclusions as structure literals makes this dependent endpoint equality definitional.
  change ((hf i).liftPathQuotient γ e).map
    ((⟨Sigma.mk i, continuous_sigmaMk⟩ : C(X i, Σ j, X j)).comp ⟨f i, (hf i).continuous⟩) = _
  rw [Path.Homotopic.Quotient.map_comp, (hf i).map_liftPathQuotient]
  exact Path.Homotopic.Quotient.map_cast γ

/-- **Monodromy commutes with the inclusion of a summand.** Transporting a point of the fibre of
`f i` over `x` into the disjoint union and letting the assembled cover transport it along the
image of `γ` gives the same result as transporting along `γ` first. -/
@[simp]
theorem monodromy_sigmaMap (hf : ∀ i, IsCoveringMap (f i)) {i : ι} {x y : X i}
    (γ : Path.Homotopic.Quotient x y) (e : (f i ⁻¹' {x} : Set (E i))) :
    (isCoveringMap_sigmaMap f hf).monodromy
        (γ.map (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(X i, Σ j, X j)))
        (sigmaMapFiberEquiv f i x e) =
      sigmaMapFiberEquiv f i y ((hf i).monodromy γ e) :=
  monodromy_sigmaMap_aux f hf γ e _ _

end TauCeti
