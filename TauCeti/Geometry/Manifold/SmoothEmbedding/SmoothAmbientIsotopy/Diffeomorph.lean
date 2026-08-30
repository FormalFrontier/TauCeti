/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Manifold.SmoothEmbedding.SmoothAmbientIsotopy.Basic

/-!
# Diffeomorphism actions and smooth ambient isotopy

This file connects composition of bundled smooth embeddings with diffeomorphisms to smooth ambient
isotopy. Transport by the final map of a diffeotopy is smoothly ambient isotopic to the original
embedding, while reparametrising two smoothly ambient-isotopic embeddings by the same source
diffeomorphism preserves the relation.

These are the compatibility results needed by Layer 4 of the GeometricTopology roadmap, in the
milestone “equivalence in each presentation.”

## Main results

* `TauCeti.SmoothEmbedding.smoothAmbientIsotopic_transDiffeomorph_final`: transport along the final
  map of a diffeotopy is a smooth ambient isotopy.
* `TauCeti.SmoothEmbedding.SmoothAmbientIsotopic.compDiffeomorph`: reparametrisation preserves
  smooth ambient isotopy.
-/

public section

noncomputable section

namespace TauCeti

open scoped Manifold ContDiff

namespace SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f g : SmoothEmbedding I J n M N}

/-- **Transport along a diffeotopy is an ambient isotopy.** An embedding and its transport by the
time-one map of a diffeotopy of the ambient manifold are smoothly ambient isotopic: the diffeotopy
itself is the witness. So the ambient `Diff`-action of `TauCeti.SmoothEmbedding.instMulActionDiff`
preserves the equivalence class of an embedding whenever the acting diffeomorphism is diffeotopic
to the identity — for knot presentations, that is exactly ambient isotopy of knots. -/
theorem smoothAmbientIsotopic_transDiffeomorph_final [IsManifold J n N]
    (f : SmoothEmbedding I J n M N) (Φ : Diffeotopy J n N) :
    f.SmoothAmbientIsotopic (f.transDiffeomorph Φ.final) := by
  apply SmoothAmbientIsotopic.of_diffeotopy Φ
  intro x
  rw [transDiffeomorph_apply]

/-- Reparametrising two embeddings by the same diffeomorphism of the source preserves smooth
ambient isotopy: the witnessing diffeotopy of the ambient manifold is unchanged. -/
theorem SmoothAmbientIsotopic.compDiffeomorph [IsManifold I n M']
    (hfg : f.SmoothAmbientIsotopic g) (e : M' ≃ₘ^n⟮I, I⟯ M) :
    (f.compDiffeomorph e).SmoothAmbientIsotopic (g.compDiffeomorph e) := by
  obtain ⟨Φ, hΦ⟩ := smoothAmbientIsotopic_def.mp hfg
  apply SmoothAmbientIsotopic.of_diffeotopy Φ
  intro x
  rw [compDiffeomorph_apply, compDiffeomorph_apply]
  exact hΦ (e x)

end SmoothEmbedding

end TauCeti
