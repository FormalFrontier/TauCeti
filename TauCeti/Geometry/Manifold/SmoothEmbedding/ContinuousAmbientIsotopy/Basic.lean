/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Topology.Homotopy.AmbientIsotopic.Basic

/-!
# Continuous ambient isotopy of bundled smooth embeddings

The geometric-topology roadmap treats geometric knot presentations as smooth embeddings,
and asks that isotopy and ambient isotopy be defined generally before being specialised.
`TauCeti.AmbientIsotopic` already gives the point-set ambient-isotopy relation for continuous
maps. This file connects that relation to the bundled smooth embeddings of
`TauCeti.Geometry.Manifold.SmoothEmbedding.Basic`.

The relation here does not assert that the ambient isotopy is smooth in time or in the ambient
variable. It is the continuous ambient-isotopy relation on the underlying maps of two bundled
smooth embeddings, which is the topological relation later smooth-knot and concordance files can
specialise further when they need differentiable isotopies. Because the smooth and topological
ambient-isotopy relations genuinely differ in high dimensions, the name says `Continuous`: this
is not a smooth ambient isotopy of the embeddings, only continuous ambient isotopy of their
underlying maps.

## Main definitions

* `TauCeti.SmoothEmbedding.ContinuousAmbientIsotopic`: two bundled smooth embeddings are
  continuously ambient isotopic when their underlying continuous maps are ambient isotopic.
* `TauCeti.SmoothEmbedding.ContinuousAmbientIsotopic.setoid`: continuous ambient isotopy as a
  setoid on bundled smooth embeddings.

The source for the topological ambient-isotopy notion is Burde--Zieschang, *Knots*, Chapter 1,
Definition 1.2, via the existing `TauCeti.Topology.Homotopy.Isotopy.Basic` and
`TauCeti.Topology.Homotopy.AmbientIsotopic.Basic` files.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff
open ContinuousMap

namespace SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω}

variable {f g h : SmoothEmbedding I J n M N}

/-- Two bundled smooth embeddings are continuously ambient isotopic when their underlying
continuous maps are ambient isotopic. This is the continuous topological relation, not a smooth
ambient isotopy. -/
def ContinuousAmbientIsotopic (f g : SmoothEmbedding I J n M N) : Prop :=
  TauCeti.AmbientIsotopic f.toContinuousMap g.toContinuousMap

/-- Continuous ambient isotopy of bundled smooth embeddings is witnessed by an ambient isotopy
whose final homeomorphism postcomposes the first underlying continuous map to the second. -/
theorem continuousAmbientIsotopic_def :
    ContinuousAmbientIsotopic f g ↔
      ∃ Φ : TauCeti.AmbientIsotopy N, Φ.final.comp f.toContinuousMap = g.toContinuousMap :=
  TauCeti.ambientIsotopic_def

namespace ContinuousAmbientIsotopic

/-- An ambient isotopy whose final map carries `f` to `g` witnesses continuous ambient isotopy of
the two bundled smooth embeddings. -/
theorem of_ambientIsotopy (Φ : TauCeti.AmbientIsotopy N)
    (hΦ : Φ.final.comp f.toContinuousMap = g.toContinuousMap) : ContinuousAmbientIsotopic f g :=
  continuousAmbientIsotopic_def.mpr ⟨Φ, hΦ⟩

/-- A symmetric form of `SmoothEmbedding.ContinuousAmbientIsotopic.of_ambientIsotopy`, useful when
the endpoint equation is oriented as `g = Φ.final ∘ f`. -/
theorem of_eq_final_comp (Φ : TauCeti.AmbientIsotopy N)
    (hΦ : g.toContinuousMap = Φ.final.comp f.toContinuousMap) : ContinuousAmbientIsotopic f g :=
  of_ambientIsotopy Φ hΦ.symm

/-- Continuous ambient isotopy of bundled smooth embeddings is reflexive. -/
@[refl]
theorem refl (f : SmoothEmbedding I J n M N) : ContinuousAmbientIsotopic f f :=
  TauCeti.AmbientIsotopic.refl f.toContinuousMap

/-- Continuous ambient isotopy of bundled smooth embeddings is symmetric. -/
@[symm]
theorem symm (hfg : ContinuousAmbientIsotopic f g) : ContinuousAmbientIsotopic g f :=
  TauCeti.AmbientIsotopic.symm hfg

/-- Continuous ambient isotopy of bundled smooth embeddings is transitive. -/
@[trans]
theorem trans (hfg : ContinuousAmbientIsotopic f g) (hgh : ContinuousAmbientIsotopic g h) :
    ContinuousAmbientIsotopic f h :=
  TauCeti.AmbientIsotopic.trans hfg hgh

/-- Continuously ambient isotopic bundled smooth embeddings have isotopic underlying continuous
maps. -/
theorem isotopic (hfg : ContinuousAmbientIsotopic f g) :
    Isotopic f.toContinuousMap g.toContinuousMap :=
  TauCeti.AmbientIsotopic.isotopic hfg f.isEmbedding

/-- Continuous ambient isotopy is an equivalence relation on bundled smooth embeddings. -/
theorem equivalence :
    Equivalence (ContinuousAmbientIsotopic (I := I) (J := J) (n := n) (M := M) (N := N)) :=
  ⟨refl, fun hfg => hfg.symm, fun hfg hgh => hfg.trans hgh⟩

/-- The continuous-ambient-isotopy equivalence relation on bundled smooth embeddings, packaged as
a `Setoid`. -/
def setoid (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H') (n : ℕ∞ω)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (N : Type*) [TopologicalSpace N] [ChartedSpace H' N] :
    Setoid (SmoothEmbedding I J n M N) where
  r := ContinuousAmbientIsotopic
  iseqv := equivalence

@[simp]
theorem setoid_r_iff {f g : SmoothEmbedding I J n M N} :
    (setoid I J n M N).r f g ↔ ContinuousAmbientIsotopic f g :=
  Iff.rfl

end ContinuousAmbientIsotopic

end SmoothEmbedding

end TauCeti
