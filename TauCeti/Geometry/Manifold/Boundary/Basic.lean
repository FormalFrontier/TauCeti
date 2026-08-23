/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Chart-independent detection of manifold boundary points

This file restates Mathlib's chart-independence results for interior and boundary points against
the range of a model with corners. This is the form used when computing the boundary of a concrete
model.
-/

public section

open Set Topology

open scoped Manifold

namespace TauCeti.ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : WithTop ℕ∞} [IsManifold I k M]
  {e : OpenPartialHomeomorph M H} {x : M}

/-- A point of a `C^k` manifold, `k ≠ 0`, is an interior point exactly when any chart of the
atlas containing it in its source reads it inside the interior of the range of the model. -/
theorem isInteriorPoint_iff_mem_interior_range (hk : k ≠ 0) (he : e ∈ atlas H M)
    (hx : x ∈ e.source) : I.IsInteriorPoint x ↔ I (e x) ∈ interior (range I) := by
  rw [I.isInteriorPoint_iff_of_mem_atlas hk he hx]
  exact ⟨fun h ↦ e.interior_extend_target_subset_interior_range h,
    fun h ↦ e.mem_interior_extend_target (e.map_source hx) h⟩

/-- A point of a `C^k` manifold, `k ≠ 0`, is a boundary point exactly when any chart of the
atlas containing it in its source reads it on the frontier of the range of the model. -/
theorem isBoundaryPoint_iff_mem_frontier_range (hk : k ≠ 0) (he : e ∈ atlas H M)
    (hx : x ∈ e.source) : I.IsBoundaryPoint x ↔ I (e x) ∈ frontier (range I) := by
  rw [I.isBoundaryPoint_iff_not_isInteriorPoint,
    isInteriorPoint_iff_mem_interior_range hk he hx, I.isClosed_range.frontier_eq]
  simp

end TauCeti.ModelWithCorners
