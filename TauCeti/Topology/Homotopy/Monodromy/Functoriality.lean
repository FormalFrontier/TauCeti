/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Lifting

/-!
# Functoriality of covering-space monodromy

A continuous map between two covering spaces over the same base carries lifts of a path to
lifts of that path. Consequently it intertwines transport between fibres and induces a natural
transformation between the two monodromy functors. An isomorphism of covers induces a natural
isomorphism.

These constructions are the morphism-level input for the alternative classification of covers
as functors from the fundamental groupoid in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
item 8. Mathlib supplies the object-level functor `IsCoveringMap.monodromyFunctor`; this file
packages its functoriality in the covering map.

## Main declarations

* `TauCeti.IsCoveringMap.fiberMap_monodromy`: a map of covers intertwines monodromy transport
  on their fibres.
* `TauCeti.IsCoveringMap.monodromyNatTrans`: a map of covers induces a natural transformation
  between their monodromy functors.
* `TauCeti.IsCoveringMap.monodromyNatIso`: an isomorphism of covers induces a natural
  isomorphism between their monodromy functors.

## References

The proof uses Junyan Xu's path-lifting and monodromy API in
`Mathlib/Topology/Homotopy/Lifting.lean`. No Mathlib code is vendored.
-/

public section

open CategoryTheory
open unitInterval

namespace TauCeti

namespace IsCoveringMap

universe u v

variable {E F G : Type u} {X : Type v}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
  {p : E → X} {q : F → X} {r : G → X}

/-- The restriction of a map over `X` to the fibre over `x`. -/
def fiberMap (f : C(E, F)) (hf : q ∘ f = p) (x : X) :
    p ⁻¹' {x} → q ⁻¹' {x} :=
  fun e ↦ ⟨f e, by
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    have he : p e = x := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using e.2
    simpa only [Function.comp_apply] using (congrFun hf e).trans he⟩

/-- On underlying points, restriction to a fibre applies the original map. -/
@[simp]
theorem fiberMap_apply_coe (f : C(E, F)) (hf : q ∘ f = p) (x : X) (e : p ⁻¹' {x}) :
    (fiberMap f hf x e : F) = f e :=
  (rfl)

/-- Restricting the identity map to a fibre gives the identity. -/
@[simp]
theorem fiberMap_id_apply (x : X) (e : p ⁻¹' {x}) :
    fiberMap (p := p) (q := p) (ContinuousMap.id E) rfl x e = e := by
  apply Subtype.ext
  rfl

/-- Restriction to a fibre respects composition of maps over the base. -/
theorem fiberMap_comp_apply (f : C(E, F)) (g : C(F, G))
    (hf : q ∘ f = p) (hg : r ∘ g = q) (x : X) (e : p ⁻¹' {x}) :
    fiberMap (g.comp f) (by
      funext z
      exact (congrFun hg (f z)).trans (congrFun hf z)) x e =
      fiberMap g hg x (fiberMap f hf x e) := by
  apply Subtype.ext
  rfl

variable [TopologicalSpace X]

/-- A map between covering spaces over the same base intertwines monodromy along every path. -/
@[simp]
theorem fiberMap_monodromy (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) (f : C(E, F)) (hf : q ∘ f = p)
    {x y : X} (a : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    fiberMap f hf y (hp.monodromy a e) = hq.monodromy a (fiberMap f hf x e) := by
  symm
  let Γ := hp.liftPathQuotient a e
  let q' : C(F, X) := ⟨q, hq.continuous⟩
  let p' : C(E, X) := ⟨p, hp.continuous⟩
  have hcomp : q'.comp f = p' := by
    ext z
    exact congrFun hf z
  apply hq.monodromy_eq_of_map_eq (Γ.map f)
  -- Expose the mapped lifted path so the commuting triangle can rewrite its composite map.
  change (Γ.map f).map q' = _
  rw [← Path.Homotopic.Quotient.map_comp]
  convert hp.map_liftPathQuotient a e using 2
  all_goals grind

/-- A continuous map of covering spaces over `X` induces a natural transformation between
their monodromy functors. Its component over `x` is the restriction of `f` to the fibre over
`x`. -/
def monodromyNatTrans (hp : _root_.IsCoveringMap p) (hq : _root_.IsCoveringMap q)
    (f : C(E, F)) (hf : q ∘ f = p) : hp.monodromyFunctor ⟶ hq.monodromyFunctor where
  app x := ↾(fiberMap f hf x.as)
  naturality {x y} a := by
    ext e
    -- The naturality square in `Type` unfolds pointwise to monodromy equivariance.
    change fiberMap f hf y.as (hp.monodromy a e) =
      hq.monodromy a (fiberMap f hf x.as e)
    exact fiberMap_monodromy hp hq f hf a e

/-- On a fibre, the natural transformation induced by a map of covers applies that map to the
underlying point. -/
@[simp]
theorem monodromyNatTrans_app (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) (f : C(E, F)) (hf : q ∘ f = p)
    (x : X) :
    (monodromyNatTrans hp hq f hf).app (FundamentalGroupoid.mk x) =
      ↾(fiberMap f hf x) :=
  (rfl)

/-- The natural transformation induced by a map over the base depends only on that map, not on
the proof that it lies over the base. -/
theorem monodromyNatTrans_congr (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) {f g : C(E, F)} (hf : q ∘ f = p) (hg : q ∘ g = p)
    (h : f = g) : monodromyNatTrans hp hq f hf = monodromyNatTrans hp hq g hg := by
  subst g
  rfl

/-- The identity map of a cover induces the identity natural transformation. -/
@[simp]
theorem monodromyNatTrans_id (hp : _root_.IsCoveringMap p) :
    monodromyNatTrans hp hp (ContinuousMap.id E) rfl = 𝟙 hp.monodromyFunctor := by
  ext x e
  apply Subtype.ext
  rfl

/-- Composition of maps of covers induces vertical composition of their monodromy natural
transformations. -/
theorem monodromyNatTrans_comp (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) (hr : _root_.IsCoveringMap r)
    (f : C(E, F)) (g : C(F, G)) (hf : q ∘ f = p) (hg : r ∘ g = q) :
    monodromyNatTrans hp hr (g.comp f) (by
      funext z
      exact (congrFun hg (f z)).trans (congrFun hf z)) =
      monodromyNatTrans hp hq f hf ≫ monodromyNatTrans hq hr g hg := by
  ext x e
  apply Subtype.ext
  rfl

/-- An isomorphism of covering spaces over `X` induces a natural isomorphism between their
monodromy functors. Its forward and inverse transformations are the ones induced by the
homeomorphism and its inverse, so its component over `x` is the restriction of the
homeomorphism to the fibre over `x`. -/
noncomputable def monodromyNatIso (hp : _root_.IsCoveringMap p) (hq : _root_.IsCoveringMap q)
    (h : E ≃ₜ F) (hh : q ∘ h = p) : hp.monodromyFunctor ≅ hq.monodromyFunctor where
  hom := monodromyNatTrans hp hq (h : C(E, F)) hh
  inv := monodromyNatTrans hq hp (h.symm : C(F, E)) ((Equiv.comp_symm_eq h.toEquiv q p).2 hh.symm)
  hom_inv_id := by
    ext x e
    apply Subtype.ext
    exact h.symm_apply_apply _
  inv_hom_id := by
    ext x f
    apply Subtype.ext
    exact h.apply_symm_apply _

/-- The forward natural transformation of the monodromy isomorphism is the canonical
transformation induced by the homeomorphism. -/
@[simp]
theorem monodromyNatIso_hom (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) (h : E ≃ₜ F) (hh : q ∘ h = p) :
    (monodromyNatIso hp hq h hh).hom =
      monodromyNatTrans hp hq (h : C(E, F)) hh :=
  (rfl)

/-- The inverse natural transformation of the monodromy isomorphism is induced by the inverse
homeomorphism. -/
@[simp]
theorem monodromyNatIso_inv (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) (h : E ≃ₜ F) (hh : q ∘ h = p) :
    (monodromyNatIso hp hq h hh).inv =
      monodromyNatTrans hq hp (h.symm : C(F, E))
        ((Equiv.comp_symm_eq h.toEquiv q p).2 hh.symm) :=
  (rfl)

end IsCoveringMap

end TauCeti
