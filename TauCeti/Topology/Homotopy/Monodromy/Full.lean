/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Homotopy.Monodromy.Functoriality

/-!
# Fullness for monodromy natural transformations

When the base is locally path-connected, every natural transformation between the monodromy
functors of two covering maps is induced by a continuous map between their total spaces over the
base.

The map on total spaces is forced pointwise: at `e`, apply the component of the natural
transformation over `p e` to `e` viewed as an element of that fibre. Its continuity is the
topological content. Around `e`, choose a path-connected open set contained in the images of
chosen sheets for both covers. Naturality along paths in that set shows that the forced map agrees
there with the inverse of the target sheet composed with the source projection.

## Main declaration

* `TauCeti.IsCoveringMap.exists_map_of_monodromyNatTrans`: a natural transformation between
  monodromy functors of covering maps is induced by a continuous map over the base.

## References

This is the fullness step in the alternative monodromy-functor classification requested by
Stage 2, item 8 of `TauCetiRoadmap/UniversalCovers/README.md`. The mathematical argument is the
standard local-sheet proof of fullness for the monodromy functor; see A. Hatcher, *Algebraic
Topology*, Section 1.3. It uses Junyan Xu's path-lifting and monodromy API in
`Mathlib/Topology/Homotopy/Lifting.lean`.
-/

public section

open CategoryTheory
open Topology
open unitInterval

universe u v

namespace TauCeti.IsCoveringMap

variable {E F : Type u} {X : Type v}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  {p : E → X} {q : F → X}

/-- Monodromy along a path contained in the base-side domain of a local inverse carries each
endpoint in its sheet to the other endpoint. -/
private theorem monodromy_eq_of_path_in_sheet (hp : _root_.IsCoveringMap p)
    (φ : OpenPartialHomeomorph X E) (hφ : ⇑φ.symm = p) {a b : X} (γ : Path a b)
    (hγ : ∀ t, γ t ∈ φ.source) (e : p ⁻¹' {a}) (z : p ⁻¹' {b})
    (he : (e : E) ∈ φ.target) (hz : (z : E) ∈ φ.target) :
    hp.monodromy (Path.Homotopic.Quotient.mk γ) e = z := by
  have he_base : p e = a := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using e.2
  have hz_base : p z = b := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using z.2
  have key : ∀ w : E, w ∈ φ.target → w = φ (p w) := fun w hw ↦ by
    rw [← congrFun hφ w]
    exact (φ.right_inv hw).symm
  have heq : (e : E) = φ a := (key e he).trans (congrArg φ he_base)
  have hzq : (z : E) = φ b := (key z hz).trans (congrArg φ hz_base)
  let Γ : Path (e : E) z :=
    (γ.map' (φ.continuousOn.mono fun _ hy ↦ by
      obtain ⟨t, rfl⟩ := hy
      exact hγ t)).cast heq hzq
  apply hp.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk Γ)
  -- Expose the projected lift as a path-class equality so `mk_map` and `mk_cast` apply.
  change (Path.Homotopic.Quotient.mk Γ).map ⟨p, hp.continuous⟩ =
    (Path.Homotopic.Quotient.mk γ).cast he_base hz_base
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  exact (congrFun hφ (φ (γ t))).symm.trans (φ.left_inv (hγ t))

/-- The pointwise map of total spaces forced by a natural transformation of monodromy
functors. -/
private noncomputable def mapOfNatTrans (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) (α : hp.monodromyFunctor ⟶ hq.monodromyFunctor) : E → F :=
  fun e ↦ ((α.app (FundamentalGroupoid.mk (p e))) ⟨e, rfl⟩).1

/-- The pointwise map defined by a monodromy transformation lies over the base. -/
private theorem proj_mapOfNatTrans (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) (α : hp.monodromyFunctor ⟶ hq.monodromyFunctor) (e : E) :
    q (mapOfNatTrans hp hq α e) = p e :=
  ((α.app (FundamentalGroupoid.mk (p e))) ⟨e, rfl⟩).2

/-- The defining pointwise equation for the map forced by a monodromy transformation. -/
private theorem mapOfNatTrans_apply (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) (α : hp.monodromyFunctor ⟶ hq.monodromyFunctor) (e : E) :
    α.app (FundamentalGroupoid.mk (p e)) ⟨e, rfl⟩ =
      ⟨mapOfNatTrans hp hq α e, proj_mapOfNatTrans hp hq α e⟩ :=
  rfl

/-- The map forced by a natural transformation of monodromy functors is continuous when the
base is locally path-connected. -/
private theorem continuous_mapOfNatTrans [LocallyPathConnectedSpace X]
    (hp : _root_.IsCoveringMap p) (hq : _root_.IsCoveringMap q)
    (α : hp.monodromyFunctor ⟶ hq.monodromyFunctor) :
    Continuous (mapOfNatTrans hp hq α) := by
  rw [continuous_iff_continuousAt]
  intro e
  -- Choose compatible local sheets around `e` and its forced image.
  let f : E → F := mapOfNatTrans hp hq α
  let φp := hp.isLocalHomeomorph.localInverseAt e
  let φq := hq.isLocalHomeomorph.localInverseAt (f e)
  let x : X := p e
  have heφp : e ∈ φp.target := by
    exact hp.isLocalHomeomorph.self_mem_localInverseAt_target
  have hfeφq : f e ∈ φq.target := by
    exact hq.isLocalHomeomorph.self_mem_localInverseAt_target
  have hφp : ⇑φp.symm = p := by
    exact hp.isLocalHomeomorph.localInverseAt_symm e
  have hφq : ⇑φq.symm = q := by
    exact hq.isLocalHomeomorph.localInverseAt_symm (f e)
  have hqfe : q (f e) = x := proj_mapOfNatTrans hp hq α e
  have hxφp : x ∈ φp.source := by
    exact hp.isLocalHomeomorph.apply_self_mem_localInverseAt_source
  have hxφq : x ∈ φq.source := hqfe ▸
    hq.isLocalHomeomorph.apply_self_mem_localInverseAt_source
  -- Refine their common base-side domain to a path-connected neighborhood of `x`.
  obtain ⟨U, ⟨hUopen, hxU, hUpath⟩, hUsub⟩ :=
    (isOpen_isPathConnected_basis x).mem_iff.mp
      ((φp.open_source.inter φq.open_source).mem_nhds ⟨hxφp, hxφq⟩)
  let V : Set E := φp.target ∩ p ⁻¹' U
  have hVopen : IsOpen V := φp.open_target.inter (hUopen.preimage hp.continuous)
  have heV : e ∈ V := ⟨heφp, hxU⟩
  let g : E → F := fun z ↦ φq (p z)
  have hg : ContinuousAt g e := by
    apply (φq.continuousAt hxφq).comp
    exact hp.continuous.continuousAt
  have hfg : mapOfNatTrans hp hq α =ᶠ[𝓝 e] g := by
    filter_upwards [hVopen.mem_nhds heV] with z hz
    -- Transport from `e` to `z` inside both sheets and compare it by naturality of `α`.
    have hpzU : p z ∈ U := hz.2
    let joined : JoinedIn U x (p z) := hUpath.joinedIn x hxU (p z) hpzU
    let γ : Path x (p z) := joined.somePath
    have hγφp (t : I) : γ t ∈ φp.source := (hUsub (joined.somePath_mem t)).1
    have hγφq (t : I) : γ t ∈ φq.source := (hUsub (joined.somePath_mem t)).2
    let e' : p ⁻¹' {x} := ⟨e, rfl⟩
    let z' : p ⁻¹' {p z} := ⟨z, rfl⟩
    have hpmono : hp.monodromy (Path.Homotopic.Quotient.mk γ) e' = z' :=
      monodromy_eq_of_path_in_sheet hp φp hφp γ hγφp e' z' heφp hz.1
    have hgz : q (g z) = p z := by
      dsimp only [g]
      exact hq.isLocalHomeomorph.apply_localInverseAt_of_mem (hUsub hpzU).2
    let fe' : q ⁻¹' {x} := ⟨f e, hqfe⟩
    let gz' : q ⁻¹' {p z} := ⟨g z, hgz⟩
    have hgzφq : g z ∈ φq.target := by
      dsimp only [g]
      exact φq.map_source (hUsub hpzU).2
    have hqmono : hq.monodromy (Path.Homotopic.Quotient.mk γ) fe' = gz' :=
      monodromy_eq_of_path_in_sheet hq φq hφq γ hγφq fe' gz' hfeφq hgzφq
    have hα := ConcreteCategory.congr_hom
      (α.naturality (Path.Homotopic.Quotient.mk γ)) e'
    rw [_root_.IsCoveringMap.monodromyFunctor_map,
      _root_.IsCoveringMap.monodromyFunctor_map] at hα
    -- The rewrites leave bundled `Type` composites under `ConcreteCategory.hom`, where the
    -- pointwise composition lemmas do not match, so expose their definitionally equal values.
    change α.app (FundamentalGroupoid.mk (p z))
        (hp.monodromy (Path.Homotopic.Quotient.mk γ) e') =
      hq.monodromy (Path.Homotopic.Quotient.mk γ)
        (α.app (FundamentalGroupoid.mk x) e') at hα
    have hαe : α.app (FundamentalGroupoid.mk x) e' = fe' := by
      simpa only [e', fe', f, x] using mapOfNatTrans_apply hp hq α e
    rw [hpmono, hαe, hqmono] at hα
    exact congrArg Subtype.val hα
  exact (continuousAt_congr hfg).mpr hg

/-- Over a locally path-connected base, every natural transformation between the monodromy
functors of two covering maps is induced by a continuous map over the base. -/
theorem exists_map_of_monodromyNatTrans [LocallyPathConnectedSpace X]
    (hp : _root_.IsCoveringMap p) (hq : _root_.IsCoveringMap q)
    (α : hp.monodromyFunctor ⟶ hq.monodromyFunctor) :
    ∃ (f : C(E, F)) (hf : q ∘ f = p), monodromyNatTrans hp hq f hf = α := by
  let f : C(E, F) := ⟨mapOfNatTrans hp hq α, continuous_mapOfNatTrans hp hq α⟩
  have hf : q ∘ f = p := by
    funext e
    exact proj_mapOfNatTrans hp hq α e
  refine ⟨f, hf, ?_⟩
  ext ⟨x⟩ e
  obtain ⟨e, he⟩ := e
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at he
  subst x
  rw [monodromyNatTrans_app]
  have he' : (⟨e, he⟩ : p ⁻¹' {p e}) = ⟨e, rfl⟩ := Subtype.ext rfl
  rw [he']
  have hfiber : fiberMap f hf (p e) ⟨e, rfl⟩ =
      ⟨mapOfNatTrans hp hq α e, proj_mapOfNatTrans hp hq α e⟩ := by
    apply Subtype.ext
    exact fiberMap_apply_coe f hf (p e) ⟨e, rfl⟩
  exact hfiber.trans (mapOfNatTrans_apply hp hq α e).symm

end TauCeti.IsCoveringMap
