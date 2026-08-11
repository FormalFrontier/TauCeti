/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# A distance-preserving map fixing the origin preserves the inner product

Mathlib knows that a *linear* isometry preserves the inner product
(`LinearIsometry.inner_map_map`), and, through the Mazur--Ulam theorem
(`IsometryEquiv.toRealLinearIsometryEquivOfMapZero`), that a *surjective* isometry of normed spaces
fixing the origin is linear. Between real inner product spaces neither hypothesis is needed, and
neither is a globally defined map: on any set `s` containing the origin, a map that fixes the
origin and preserves distances between points of `s` already preserves the inner product on `s`.

The reason is polarisation. The three quantities `‖x‖`, `‖y‖`, `‖x - y‖` determine `⟪x, y⟫_ℝ`
through `norm_sub_sq_real`, and all three are preserved: the two norms because `0 ∈ s` is a fixed
point, so `‖g z‖ = ‖g z - g 0‖ = ‖z - 0‖`, and the third by hypothesis. Nothing about linearity,
surjectivity, or continuity enters, and the conclusion is available point by point on `s` rather
than only after an extension.

## Main results

* `TauCeti.norm_map_of_dist_map_eq` — such a map preserves norms.
* `TauCeti.real_inner_map_map_of_dist_map_eq` — such a map preserves the real inner product.

The consumer is `TauCeti/Analysis/Complex/Isometry.lean`, which classifies the distance-preserving
self-maps of a disc of `ℂ` about the origin. There the map is given only on an open ball, and is
assumed neither linear nor bijective; Mazur--Ulam asks for an isometric equivalence of the whole
space, so none of its hypotheses are on hand, and this polarisation is what replaces it.

The argument is adapted from the proofs of
`TauCeti.norm_map_of_pseudoHyperbolicExpr_map_eq` and
`TauCeti.real_inner_map_map_of_pseudoHyperbolicExpr_map_eq` in
`TauCeti/Analysis/Complex/Conformal/Poincare/Isometry/Classification.lean`, as merged in
TauCeti#1502, with the unit disc of `ℂ` relaxed to an arbitrary set `s` containing the origin.
-/

public section

namespace TauCeti

open RealInnerProductSpace

section Normed

variable {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] {s : Set E} {g : E → F}

/-- **A distance-preserving map fixing the origin preserves norms.** The norm is the distance to
the origin, which is a fixed point lying in `s`. Only the metric structure is involved, so this
step asks for no inner product. -/
theorem norm_map_of_dist_map_eq (h0 : (0 : E) ∈ s) (hg0 : g 0 = 0)
    (hg : ∀ z ∈ s, ∀ w ∈ s, dist (g z) (g w) = dist z w) {z : E} (hz : z ∈ s) :
    ‖g z‖ = ‖z‖ := by
  simpa [hg0] using hg z hz 0 h0

end Normed

section InnerProduct

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {s : Set E} {g : E → F}

/-- **A distance-preserving map fixing the origin preserves the real inner product.** Polarisation:
by `norm_sub_sq_real` the inner product `⟪z, w⟫_ℝ` is determined by the three quantities `‖z‖`,
`‖w‖` and `‖z - w‖`, and `g` preserves all three — the first two by
`TauCeti.norm_map_of_dist_map_eq`, the third by hypothesis.

Neither linearity nor surjectivity of `g` is assumed, and `g` need only be distance-preserving
between points of `s`; the conclusion is correspondingly restricted to `s`. -/
theorem real_inner_map_map_of_dist_map_eq (h0 : (0 : E) ∈ s) (hg0 : g 0 = 0)
    (hg : ∀ z ∈ s, ∀ w ∈ s, dist (g z) (g w) = dist z w) {z w : E} (hz : z ∈ s) (hw : w ∈ s) :
    ⟪g z, g w⟫ = ⟪z, w⟫ := by
  have hnz := norm_map_of_dist_map_eq h0 hg0 hg hz
  have hnw := norm_map_of_dist_map_eq h0 hg0 hg hw
  have hsub : ‖g z - g w‖ = ‖z - w‖ := by
    simpa only [dist_eq_norm] using hg z hz w hw
  have h1 := norm_sub_sq_real (g z) (g w)
  have h2 := norm_sub_sq_real z w
  rw [hsub, hnz, hnw] at h1
  linarith

end InnerProduct

end TauCeti
