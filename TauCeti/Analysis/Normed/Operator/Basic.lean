/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Basic facts about bounded operators

This file records a shared uniform-bound lemma for continuous linear maps. It lets an evaluation
`T i (g i)` pass to the limit when the operators `T i` are eventually uniformly bounded, their
values at the limiting argument converge, and the arguments `g i` converge. In particular, it
supplies the common continuity step for
`StronglyContinuousSemigroup.tendsto_realOperator_apply` and
`StronglyContinuousGroup.tendsto_apply`.
-/

public section

open scoped Topology
open Filter

namespace TauCeti

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

namespace ContinuousLinearMap

/-- If `T i` is eventually uniformly bounded, `T i z` tends to `w`, and `g i` tends to `z`, then
the moving evaluations `T i (g i)` tend to `w`. -/
theorem tendsto_apply_of_eventually_norm_le {ι : Type*} {l : Filter ι}
    {T : ι → X →L[𝕜] Y} {C : ℝ} {g : ι → X} {z : X} {w : Y}
    (hT : ∀ᶠ i in l, ‖T i‖ ≤ C) (hz : Tendsto (fun i => T i z) l (𝓝 w))
    (hg : Tendsto g l (𝓝 z)) : Tendsto (fun i => T i (g i)) l (𝓝 w) := by
  have hmove : Tendsto (fun i => T i (g i - z)) l (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun i => C * ‖g i - z‖) ?_ ?_
    · filter_upwards [hT] with i hi
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
    · simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hg).const_mul C
  have hsplit : ∀ i, T i (g i) = T i (g i - z) + T i z := fun i => by
    rw [← ContinuousLinearMap.map_add, sub_add_cancel]
  simpa using (hmove.add hz).congr fun i => (hsplit i).symm

end ContinuousLinearMap

end TauCeti

end
