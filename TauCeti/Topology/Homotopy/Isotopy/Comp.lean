/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Isotopy.Basic

/-!
# Naturality of isotopy under composition with embeddings

An isotopy is a homotopy through topological embeddings. This file records that the isotopy
relation is *natural*: composing on either side with a
topological embedding carries an isotopy to an isotopy, and so an isotopy relation to an
isotopy relation. These are the closure properties the geometric-topology roadmap
(`TauCetiRoadmap/GeometricTopology/README.md`) asks the general isotopy notion to carry
before specialising to smooth embeddings `S¹ ↪ M`: they mirror, for `TauCeti.Isotopy`, the
composition lemmas Mathlib provides for `IsEmbedding` (`Topology.IsEmbedding.comp`) and for
homotopy (`ContinuousMap.Homotopy.comp`, `ContinuousMap.Homotopy.compContinuousMap`), which
this file reuses for the underlying homotopies.

The two-sided generality (an embedding on either side, not merely a homeomorphism) is what
the roadmap's layer-2 closure properties for locally flat embeddings will consume: a
submanifold inclusion postcomposes, a chart or open embedding precomposes, and the isotopy
survives both.

## Main definitions

* `TauCeti.Isotopy.postcomp`: postcomposing an isotopy `f₀ ≈ f₁` with an embedding `g`
  yields an isotopy `g ∘ f₀ ≈ g ∘ f₁`.
* `TauCeti.Isotopy.precomp`: precomposing an isotopy `f₀ ≈ f₁` with an embedding `e` yields
  an isotopy `f₀ ∘ e ≈ f₁ ∘ e`.

## Main results

* `TauCeti.Isotopic.postcomp` / `TauCeti.Isotopic.precomp`: the same closure on the isotopy
  *relation*.
* `TauCeti.Isotopic.postcomp_precomp`: the two-sided form, composing with an embedding on
  each side.
* `TauCeti.Isotopic.postcomp_homeomorph` / `TauCeti.Isotopic.precomp_homeomorph`: the common
  special case where the composing map is a homeomorphism (an ambient homeomorphism on the
  codomain, or a change of source coordinates).
-/

public section

namespace TauCeti

open unitInterval ContinuousMap Topology

variable {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

namespace Isotopy

variable {f₀ f₁ : C(X, Y)}

/-- Postcompose an isotopy `f₀ ≈ f₁` with a topological embedding `g : Y ↪ Z` to get an
isotopy `g ∘ f₀ ≈ g ∘ f₁`. -/
def postcomp (F : Isotopy f₀ f₁) (g : C(Y, Z)) (hg : IsEmbedding g) :
    Isotopy (g.comp f₀) (g.comp f₁) where
  toHomotopy := (Homotopy.refl g).comp F.toHomotopy
  prop' := fun t => hg.comp (F.isEmbedding_apply t)

@[simp]
theorem postcomp_apply (F : Isotopy f₀ f₁) (g : C(Y, Z)) (hg : IsEmbedding g) (p : I × X) :
    F.postcomp g hg p = g (F p) := (rfl)

/-- Precompose an isotopy `f₀ ≈ f₁` with a topological embedding `e : W ↪ X` to get an
isotopy `f₀ ∘ e ≈ f₁ ∘ e`. -/
def precomp (F : Isotopy f₀ f₁) (e : C(W, X)) (he : IsEmbedding e) :
    Isotopy (f₀.comp e) (f₁.comp e) where
  toHomotopy := F.toHomotopy.compContinuousMap e
  prop' := fun t => (F.isEmbedding_apply t).comp he

@[simp]
theorem precomp_apply (F : Isotopy f₀ f₁) (e : C(W, X)) (he : IsEmbedding e) (p : I × W) :
    F.precomp e he p = F (p.1, e p.2) := (rfl)

end Isotopy

namespace Isotopic

variable {f₀ f₁ : C(X, Y)}

/-- Postcompose an isotopy relation with a topological embedding: if `f₀ ≈ f₁` and `g` is an
embedding, then `g ∘ f₀ ≈ g ∘ f₁`. -/
theorem postcomp (h : Isotopic f₀ f₁) (g : C(Y, Z)) (hg : IsEmbedding g) :
    Isotopic (g.comp f₀) (g.comp f₁) :=
  of_isotopy ((isotopic_def.mp h).some.postcomp g hg)

/-- Precompose an isotopy relation with a topological embedding: if `f₀ ≈ f₁` and `e` is an
embedding, then `f₀ ∘ e ≈ f₁ ∘ e`. -/
theorem precomp (h : Isotopic f₀ f₁) (e : C(W, X)) (he : IsEmbedding e) :
    Isotopic (f₀.comp e) (f₁.comp e) :=
  of_isotopy ((isotopic_def.mp h).some.precomp e he)

/-- The two-sided form: an isotopy relation survives composing with an embedding on each
side. -/
theorem postcomp_precomp (h : Isotopic f₀ f₁) (g : C(Y, Z)) (hg : IsEmbedding g) (e : C(W, X))
    (he : IsEmbedding e) : Isotopic (g.comp (f₀.comp e)) (g.comp (f₁.comp e)) :=
  (h.precomp e he).postcomp g hg

/-- Postcomposing an isotopy relation with a homeomorphism of the codomain. -/
theorem postcomp_homeomorph (h : Isotopic f₀ f₁) (e : Y ≃ₜ Z) :
    Isotopic ((e : C(Y, Z)).comp f₀) ((e : C(Y, Z)).comp f₁) :=
  h.postcomp _ e.isEmbedding

/-- Precomposing an isotopy relation with a homeomorphism of the source. -/
theorem precomp_homeomorph (h : Isotopic f₀ f₁) (e : W ≃ₜ X) :
    Isotopic (f₀.comp (e : C(W, X))) (f₁.comp (e : C(W, X))) :=
  h.precomp _ e.isEmbedding

end Isotopic

end TauCeti
