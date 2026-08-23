/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope

/-!
# Elementary facts about `dslope`

Divided-slope facts that need no differentiability, collected for the Schwarz-lemma consumers.
Away from its base point `dslope` is the plain difference quotient, so these are statements about
a normed field and its norm, with no calculus in them.

## Main results

* `TauCeti.norm_dslope_eq_one_of_norm_sub_map_eq`: a map that moves two points exactly as far
  apart as they already are has unimodular difference quotient between them. This is the
  hypothesis the equality case of Schwarz's lemma
  (`Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div`) takes, and the two Tau Ceti consumers of
  that equality case — the Schwarz--Pick rigidity theorem and the classification of the disc
  rotations — reach it by exactly this route, at base point `0`.
-/

public section

namespace TauCeti

/-- **A map preserving the distance between two points has unit difference quotient between
them.** For `y ≠ x` with `‖g y - g x‖ = ‖y - x‖`, the difference quotient `dslope g x y` is
unimodular.

No differentiability is involved: away from the base point `dslope` is the plain difference
quotient. -/
lemma norm_dslope_eq_one_of_norm_sub_map_eq {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {g : 𝕜 → E} {x y : 𝕜} (hxy : y ≠ x)
    (hnorm : ‖g y - g x‖ = ‖y - x‖) : ‖dslope g x y‖ = 1 := by
  rw [dslope_of_ne _ hxy, slope_def_module, norm_smul, norm_inv, hnorm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))]

end TauCeti
