/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.LinearPMap
public import TauCeti.LinearAlgebra.LinearPMap.SmulSub

/-!
# Shifts of a partial linear map on a normed space

For a partial linear map `A` on a normed space and a scalar `c`, this file studies the shift
`x ↦ c • x - A x` (bundled as `LinearPMap.smulSub` in `TauCeti.LinearAlgebra.LinearPMap.SmulSub`)
under a lower bound.  A shift bounded below by a multiple of `‖x‖` is injective; a shift bounded
below by a multiple of the graph norm `max ‖x‖ ‖A x‖` of a closed `A` has closed range, because it
is then an antilipschitz map on the complete graph of `A`.  These are the common cores of the
injectivity of `λ - A` for a dissipative `A` and of the closed-range property of the nonreal
shifts of a closed symmetric `A`.

## Main results

* `LinearPMap.smul_sub_injective_of_norm_le`: a shift bounded below by a multiple of `‖x‖` is
  injective.
* `LinearPMap.graphSmulSub`: the shift as a continuous linear map on the graph of `A`, with
  `graphSmulSub_apply` and `range_graphSmulSub`.
* `LinearPMap.isClosed_range_smul_sub_of_graph_norm_le`: a shift of a closed partial linear map
  that is bounded below by a multiple of the graph norm has closed range.
-/

public section

open scoped NNReal

namespace LinearPMap

section Injective

variable {𝕜 E : Type*} [CommRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]

/-- A shift `x ↦ c • x - A x` dominating `K * ‖x‖` for some `K > 0` is injective, being
antilipschitz. -/
theorem smul_sub_injective_of_norm_le {A : E →ₗ.[𝕜] E} {c : 𝕜} {K : ℝ} (hK : 0 < K)
    (h : ∀ x : A.domain, K * ‖(x : E)‖ ≤ ‖c • (x : E) - A x‖) :
    Function.Injective fun x : A.domain => c • (x : E) - A x := fun x y hxy =>
  (AddMonoidHomClass.antilipschitz_of_bound (A.smulSub c) (K := K⁻¹.toNNReal) fun x => by
    rw [A.smulSub_apply, Real.coe_toNNReal _ (inv_nonneg.mpr hK.le), le_inv_mul_iff₀ hK]
    exact h x).injective (by rwa [A.smulSub_apply, A.smulSub_apply])

end Injective

section Graph

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The shift `x ↦ c • x - A x`, as a continuous linear map on the graph of `A`. -/
def graphSmulSub (A : E →ₗ.[𝕜] E) (c : 𝕜) : A.graph →L[𝕜] E :=
  ((c • ContinuousLinearMap.fst 𝕜 E E) - ContinuousLinearMap.snd 𝕜 E E).domRestrict A.graph

@[simp]
theorem graphSmulSub_apply (A : E →ₗ.[𝕜] E) (c : 𝕜) (z : A.graph) :
    A.graphSmulSub c z = c • (z : E × E).1 - (z : E × E).2 :=
  (rfl)

/-- The range of the graph shift is the range of the shift. -/
theorem range_graphSmulSub (A : E →ₗ.[𝕜] E) (c : 𝕜) :
    Set.range (A.graphSmulSub c) = Set.range fun x : A.domain => c • (x : E) - A x := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨x, hx1, hx2⟩ := A.mem_graph_iff.mp z.property
    exact ⟨x, by rw [graphSmulSub_apply, ← hx1, ← hx2]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⟨((x : E), A x), A.mem_graph_iff.mpr ⟨x, rfl, rfl⟩⟩, rfl⟩

/-- A lower bound for the shift in terms of the graph norm `max ‖x‖ ‖A x‖` is a lower bound for the
graph shift in terms of the norm of the graph. -/
theorem norm_le_mul_norm_graphSmulSub {A : E →ₗ.[𝕜] E} {c : 𝕜} {K : ℝ≥0}
    (hbound : ∀ x : A.domain, max ‖(x : E)‖ ‖A x‖ ≤ K * ‖c • (x : E) - A x‖) (z : A.graph) :
    ‖(z : E × E)‖ ≤ K * ‖A.graphSmulSub c z‖ := by
  obtain ⟨u, hu1, hu2⟩ := A.mem_graph_iff.mp z.property
  rw [Prod.norm_def]
  calc
    max ‖(z : E × E).1‖ ‖(z : E × E).2‖ = max ‖(u : E)‖ ‖A u‖ := by rw [← hu1, ← hu2]
    _ ≤ K * ‖c • (u : E) - A u‖ := hbound u
    _ = K * ‖A.graphSmulSub c z‖ := by rw [graphSmulSub_apply, ← hu1, ← hu2]

/-- **A shift bounded below in the graph norm has closed range.** If `A` is closed and
`max ‖x‖ ‖A x‖ ≤ K * ‖c • x - A x‖` on the domain, then the range of `x ↦ c • x - A x` is closed:
the graph shift is an antilipschitz map on the complete graph of `A`. -/
theorem isClosed_range_smul_sub_of_graph_norm_le [CompleteSpace E] {A : E →ₗ.[𝕜] E}
    (hcl : A.IsClosed) {c : 𝕜} {K : ℝ≥0}
    (hbound : ∀ x : A.domain, max ‖(x : E)‖ ‖A x‖ ≤ K * ‖c • (x : E) - A x‖) :
    _root_.IsClosed (Set.range fun x : A.domain => c • (x : E) - A x) := by
  let _ : CompleteSpace A.graph := hcl.completeSpace_coe
  rw [← A.range_graphSmulSub c]
  exact ((A.graphSmulSub c).antilipschitz_of_bound
    (norm_le_mul_norm_graphSmulSub hbound)).isClosed_range (A.graphSmulSub c).uniformContinuous

end Graph

end LinearPMap

end
