/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
-- Proof-only: the interior branch closes through `not_isLocalMax_of_laplacian_add_fderiv_pos` and
-- `laplacian_add_fderiv_add_const_smul`. Neither occurs in the statement below, so this import is
-- not public and importing this module does not pull in the drift maximum principle.
import TauCeti.Analysis.InnerProductSpace.Laplacian.DriftMaximumPrinciple

/-!
# The maximizer step shared by the lower-order weak maximum principles

Both lower-order weak maximum principles — for `-Δ + c` in
`TauCeti.Analysis.InnerProductSpace.Laplacian.ZerothOrderMaximumPrinciple` and for
`-Δ - b·∇ + c` in `TauCeti.Analysis.InnerProductSpace.Laplacian.LowerOrderMaximumPrinciple` —
perturb a subsolution by a barrier, take a maximizer of the perturbation over the compact set, and
then argue that the frontier bound already holds at that maximizer. Only the last step is common:
the two differ in how they produce the maximizer and in which barrier they use.

This module holds that step, stated once for the operator `Δ + b·∇` with an arbitrary barrier. The
`-Δ + c` principle runs it at `b = 0` with the quadratic barrier `‖·‖²`.

It is a support module: `TauCeti.le_of_isMaxOn_add_smul` is support API for those two proofs rather
than a result the roadmap asks for. Both principles import this module non-publicly, so neither
re-exports it and nothing downstream of either principle sees the step in its interface.
-/

public section

noncomputable section

namespace TauCeti

open InnerProductSpace Laplacian Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The maximizer step of the lower-order weak maximum principles.** Let `z` be a maximizer of
`f + ε • w` over `K`. If `f z ≤ m` whenever `z` is a frontier point, and, whenever `z` is interior
and `f z` exceeds `m`, the operator `Δ + ∇_v` is nonnegative on `f` at `z` while the barrier `w` is
`C²` and strictly positive under that operator at `z`, then `f z ≤ m`.

The direction is a single vector `v`, and the regularity and operator-sign hypotheses `hcd`,
`hLf0`, `hwcd`, `hwpos` are asked for at `z` alone and only when `z` is interior. A caller holding
the usual `∀ x ∈ interior K` form instantiates it at `z`, as `fun h => hcd h`; a caller with a drift
field `b` passes `b z`. -/
theorem le_of_isMaxOn_add_smul {K : Set E} {f w : E → ℝ} {v : E} {m ε : ℝ} {z : E}
    (hε : 0 < ε) (hcd : z ∈ interior K → ContDiffAt ℝ 2 f z)
    (hLf0 : z ∈ interior K → m < f z → 0 ≤ Δ f z + fderiv ℝ f z v)
    (hbdry : z ∈ frontier K → f z ≤ m) (hzK : z ∈ K)
    (hwcd : z ∈ interior K → ContDiffAt ℝ 2 w z)
    (hwpos : z ∈ interior K → 0 < Δ w z + fderiv ℝ w z v)
    (hzmax : IsMaxOn (fun y => f y + ε • w y) K z) :
    f z ≤ m := by
  by_cases hzint : z ∈ interior K
  · -- Interior: the operator is nonnegative on `f` at `z`, so the perturbed sum is strictly
    -- positive there and `z` cannot be a local maximum.
    by_contra hn
    have hpos : 0 < Δ (fun y => f y + ε • w y) z +
        fderiv ℝ (fun y => f y + ε • w y) z v := by
      rw [laplacian_add_fderiv_add_const_smul f w v ε z (hcd hzint) (hwcd hzint)]
      nlinarith [mul_pos hε (hwpos hzint), hLf0 hzint (not_le.mp hn)]
    exact not_isLocalMax_of_laplacian_add_fderiv_pos
      ((hcd hzint).add ((hwcd hzint).const_smul ε)) hpos
      (hzmax.isLocalMax (mem_interior_iff_mem_nhds.mp hzint))
  · exact hbdry ⟨subset_closure hzK, hzint⟩

end TauCeti

end

end
