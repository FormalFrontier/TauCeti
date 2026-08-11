/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Covering.Monodromy.Basic

/-!
# Fullness of covering-space monodromy

When the base is locally path-connected, every natural transformation between the monodromy
functors of two covering spaces comes from a unique map of covering spaces. Faithfulness was
proved when the monodromy functor was assembled; this file supplies fullness.

The map on total spaces is forced pointwise: at `e`, apply the component of the natural
transformation over `p e` to `e` viewed as an element of that fibre. Its continuity is the
topological content. Around `e`, choose a path-connected open set contained in local sheets for
both covers. Naturality along paths in that set shows that the forced map agrees there with the
inverse of the target sheet followed by the source projection.

## Main declaration

* `TauCeti.CoveringSpace.monodromyFunctor_full`: over a locally path-connected base, the
  monodromy functor on covering spaces is full.

## References

This is the fullness step in the alternative monodromy-functor classification requested by
Stage 2, item 8 of `TauCetiRoadmap/UniversalCovers/README.md`. The mathematical argument is the
standard local-sheet proof of fullness for the monodromy functor; see A. Hatcher, *Algebraic
Topology*, Section 1.3. It uses Mathlib's covering trivializations and path-lifting monodromy.
-/

public section

open CategoryTheory
open Topology
open unitInterval

universe u

namespace TauCeti.CoveringSpace

variable {X : TopCat.{u}}

/-- The pointwise map of total spaces forced by a natural transformation of monodromy
functors. -/
private noncomputable def mapOfNatTrans {p q : CoveringSpace X}
    (α : (monodromyFunctor X).obj p ⟶ (monodromyFunctor X).obj q) :
    ↑(p : TopCat) → ↑(q : TopCat) :=
  fun e ↦ ((α.app (FundamentalGroupoid.mk (p.proj e))) ⟨e, rfl⟩).1

/-- The pointwise map defined by a monodromy transformation lies over the base. -/
private theorem proj_mapOfNatTrans {p q : CoveringSpace X}
    (α : (monodromyFunctor X).obj p ⟶ (monodromyFunctor X).obj q)
    (e : ↑(p : TopCat)) :
    q.proj (mapOfNatTrans α e) = p.proj e :=
  ((α.app (FundamentalGroupoid.mk (p.proj e))) ⟨e, rfl⟩).2

/-- The map forced by a natural transformation of monodromy functors is continuous when the
base is locally path-connected. -/
private theorem continuous_mapOfNatTrans [LocallyPathConnectedSpace X]
    {p q : CoveringSpace X}
    (α : (monodromyFunctor X).obj p ⟶ (monodromyFunctor X).obj q) :
    Continuous (mapOfNatTrans α) := by
  rw [continuous_iff_continuousAt]
  intro e
  let f : ↑(p : TopCat) → ↑(q : TopCat) := mapOfNatTrans α
  let hp := p.isCoveringMap_proj
  let hq := q.isCoveringMap_proj
  obtain ⟨ep, hep, hp_eq⟩ := hp.isLocalHomeomorph e
  obtain ⟨eq, heq, hq_eq⟩ := hq.isLocalHomeomorph (f e)
  let x : X := p.proj e
  have hpe : ep e = x := by
    simpa only [x] using congrFun hp_eq.symm e
  have hqfe : eq (f e) = x := by
    rw [← hq_eq]
    exact proj_mapOfNatTrans α e
  have hxept : x ∈ ep.target := hpe ▸ ep.map_source hep
  have hxeqt : x ∈ eq.target := hqfe ▸ eq.map_source heq
  obtain ⟨U, ⟨hUopen, hxU, hUpath⟩, hUsub⟩ :=
    (isOpen_isPathConnected_basis x).mem_iff.mp
      ((ep.open_target.inter eq.open_target).mem_nhds ⟨hxept, hxeqt⟩)
  let V : Set ↑(p : TopCat) := ep.source ∩ p.proj ⁻¹' U
  have hVopen : IsOpen V := ep.open_source.inter (hUopen.preimage hp.continuous)
  have heV : e ∈ V := by
    refine ⟨hep, ?_⟩
    exact hxU
  let g : ↑(p : TopCat) → ↑(q : TopCat) := fun z ↦ eq.symm (p.proj z)
  have hg : ContinuousAt g e := by
    apply (eq.continuousAt_symm hxeqt).comp
    exact hp.continuous.continuousAt
  have hfg : mapOfNatTrans α =ᶠ[𝓝 e] g := by
    filter_upwards [hVopen.mem_nhds heV] with z hz
    have hpz_eq : ep z = p.proj z := congrFun hp_eq.symm z
    have hpzU : p.proj z ∈ U := hz.2
    let joined : JoinedIn U x (p.proj z) := hUpath.joinedIn x hxU (p.proj z) hpzU
    let γ : Path x (p.proj z) := joined.somePath
    have hγep (t : I) : γ t ∈ ep.target := (hUsub (joined.somePath_mem t)).1
    have hγeq (t : I) : γ t ∈ eq.target := (hUsub (joined.somePath_mem t)).2
    let Γp : Path e z :=
      { toFun := fun t ↦ ep.symm (γ t)
        continuous_toFun := ep.symm.continuousOn.comp_continuous γ.continuous hγep
        source' := by
          dsimp only
          rw [γ.source, ← hpe]
          exact ep.left_inv hep
        target' := by
          dsimp only
          rw [γ.target, ← hpz_eq]
          exact ep.left_inv hz.1 }
    have hΓp_map : Γp.map hp.continuous = γ := by
      ext t
      exact (congrFun hp_eq (ep.symm (γ t))).trans (ep.right_inv (hγep t))
    let e' : p.proj.hom ⁻¹' {x} := ⟨e, rfl⟩
    let z' : p.proj.hom ⁻¹' {p.proj z} := ⟨z, rfl⟩
    have hpmono : hp.monodromy (Path.Homotopic.Quotient.mk γ) e' = z' := by
      apply hp.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk Γp)
      rw [← Path.Homotopic.Quotient.mk_map, hΓp_map]
      rfl
    let Γq : Path (f e) (g z) :=
      { toFun := fun t ↦ eq.symm (γ t)
        continuous_toFun := eq.symm.continuousOn.comp_continuous γ.continuous hγeq
        source' := by
          dsimp only [g]
          rw [γ.source, ← hqfe]
          exact eq.left_inv heq
        target' := by
          dsimp only [g]
          rw [γ.target] }
    have hfe : q.proj (f e) = x := proj_mapOfNatTrans α e
    have hgz : q.proj (g z) = p.proj z := by
      -- Unfold the local comparison map while keeping the chosen sheet inverse opaque.
      change q.proj (eq.symm (p.proj z)) = p.proj z
      rw [congrFun hq_eq (eq.symm (p.proj z)), eq.right_inv (hUsub hpzU).2]
    let fe' : q.proj.hom ⁻¹' {x} := ⟨f e, hfe⟩
    let gz' : q.proj.hom ⁻¹' {p.proj z} := ⟨g z, hgz⟩
    have hΓq_map : Γq.map hq.continuous = γ.cast hfe hgz := by
      ext t
      exact (congrFun hq_eq (eq.symm (γ t))).trans (eq.right_inv (hγeq t))
    have hqmono : hq.monodromy (Path.Homotopic.Quotient.mk γ) fe' = gz' := by
      apply hq.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk Γq)
      rw [← Path.Homotopic.Quotient.mk_map, hΓq_map,
        Path.Homotopic.Quotient.mk_cast]
    have hα := ConcreteCategory.congr_hom
      (α.naturality (Path.Homotopic.Quotient.mk γ)) e'
    -- Naturality is packaged through composition in `Type`; expose its pointwise transport
    -- equation so the two locally constructed lifted paths can rewrite it.
    change α.app (FundamentalGroupoid.mk (p.proj z))
        (hp.monodromy (Path.Homotopic.Quotient.mk γ) e') =
      hq.monodromy (Path.Homotopic.Quotient.mk γ)
        (α.app (FundamentalGroupoid.mk x) e') at hα
    have hαe : α.app (FundamentalGroupoid.mk x) e' = fe' := Subtype.ext rfl
    rw [hpmono, hαe, hqmono] at hα
    -- Read the resulting equality of fibre elements on their underlying total-space points.
    change f z = g z
    exact congrArg Subtype.val hα
  exact (continuousAt_congr hfg).mpr hg

/-- Over a locally path-connected base, every natural transformation of monodromy functors is
induced by a map of covering spaces. -/
instance monodromyFunctor_full [LocallyPathConnectedSpace X] : (monodromyFunctor X).Full where
  map_surjective {p q} α := by
    -- Use the object formula of the assembled monodromy functor in the transformation's type.
    change p.isCoveringMap_proj.monodromyFunctor ⟶
      q.isCoveringMap_proj.monodromyFunctor at α
    let f : (p : TopCat) ⟶ (q : TopCat) :=
      TopCat.ofHom ⟨mapOfNatTrans α, continuous_mapOfNatTrans α⟩
    let F : p ⟶ q := homMk f (by
      ext e
      exact proj_mapOfNatTrans α e)
    refine ⟨F, ?_⟩
    -- Expose the morphism part of the assembled functor; the remaining equality is exactly the
    -- component formula for `monodromyNatTrans`.
    change IsCoveringMap.monodromyNatTrans p.isCoveringMap_proj q.isCoveringMap_proj
      F.hom.left.hom (proj_hom_comp_hom_left_hom F) = α
    ext ⟨x⟩ e
    obtain ⟨e, he⟩ := e
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at he
    subst x
    rw [IsCoveringMap.monodromyNatTrans_app]
    apply Subtype.ext
    -- The categorical component above is the restriction of `F.hom.left`; expose its value
    -- before identifying the constructed morphism with the forced pointwise map.
    erw [IsCoveringMap.fiberMap_apply_coe]
    have hF : F.hom.left = f := by
      dsimp only [F]
      exact homMk_hom_left _ _
    rw [hF]
    dsimp only [f]
    rfl

end TauCeti.CoveringSpace
