/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.AmbientIsotopic.Basic
public import TauCeti.Topology.Homotopy.AmbientIsotopyConj

/-!
# Naturality of ambient isotopy under coordinate changes

The geometric-topology roadmap asks for isotopy and ambient isotopy to be defined once, in full
generality, before specialising to locally flat embeddings, diffeotopies, knots, and concordance.
`TauCeti.AmbientIsotopic` is the general point-set ambient-isotopy relation on continuous maps,
and `TauCeti.AmbientIsotopy.transport` transports a witnessing ambient isotopy across a
homeomorphism of ambient spaces. This file records the corresponding relation-level API.

Precomposition is available for any continuous map of source spaces, because an ambient isotopy
acts only on the codomain. Postcomposition is stated for a homeomorphism of ambient spaces; the
witness is the transported ambient isotopy.

## Main results

* `TauCeti.AmbientIsotopic.precomp`: ambient isotopy survives precomposition by a continuous map.
* `TauCeti.AmbientIsotopic.postcomp_homeomorph`: ambient isotopy survives postcomposition by a
  homeomorphism of ambient spaces.
* `TauCeti.AmbientIsotopic.postcomp_homeomorph_precomp`: the combined change-of-coordinates form.
-/

public section

namespace TauCeti

open unitInterval ContinuousMap Topology

variable {W X Y Z : Type*} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

namespace AmbientIsotopic

variable {f g : C(X, Y)}

/-- Ambient isotopy survives precomposition by any continuous source map. If an ambient isotopy
of `Y` carries `f` to `g`, the same ambient isotopy carries `f ∘ e` to `g ∘ e`. -/
theorem precomp (hfg : AmbientIsotopic f g) (e : C(W, X)) :
    AmbientIsotopic (f.comp e) (g.comp e) := by
  obtain ⟨Φ, hΦ⟩ := ambientIsotopic_def.mp hfg
  refine ambientIsotopic_def.mpr ⟨Φ, ?_⟩
  ext w
  exact congr_fun (congrArg DFunLike.coe hΦ) (e w)

/-- Ambient isotopy survives postcomposition by a homeomorphism of ambient spaces. The witnessing
ambient isotopy is obtained by transporting the original one across the homeomorphism. -/
theorem postcomp_homeomorph (hfg : AmbientIsotopic f g) (h : Y ≃ₜ Z) :
    AmbientIsotopic ((h : C(Y, Z)).comp f) ((h : C(Y, Z)).comp g) := by
  obtain ⟨Φ, hΦ⟩ := ambientIsotopic_def.mp hfg
  refine ambientIsotopic_def.mpr ⟨Φ.transport h, ?_⟩
  ext x
  have hx : Φ.final (f x) = g x := congr_fun (congrArg DFunLike.coe hΦ) x
  simpa [AmbientIsotopy.final_transport] using congrArg h hx

/-- The two-sided coordinate-change form: precompose the source by any continuous map and
postcompose the ambient space by a homeomorphism. -/
theorem postcomp_homeomorph_precomp (hfg : AmbientIsotopic f g) (h : Y ≃ₜ Z) (e : C(W, X)) :
    AmbientIsotopic ((h : C(Y, Z)).comp (f.comp e)) ((h : C(Y, Z)).comp (g.comp e)) :=
  (hfg.precomp e).postcomp_homeomorph h

end AmbientIsotopic

end TauCeti
