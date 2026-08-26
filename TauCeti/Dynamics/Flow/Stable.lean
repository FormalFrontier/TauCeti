/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Stable and unstable sets of a flow

For a real flow `φ`, the stable set of `x` consists of the points whose trajectories converge to
`x` as time tends to `+∞`; the unstable set uses time tending to `-∞`.  These are the underlying
sets which the stable-manifold theorem identifies locally as smooth manifolds near a hyperbolic
fixed point.

Both sets are invariant under the entire flow.  Moreover, either set can be nonempty only when
its limiting point is fixed by the flow.  Time reversal exchanges the two constructions.

## Main declarations

* `Flow.stableSet`: points converging to a given point in forward time.
* `Flow.unstableSet`: points converging to a given point in backward time.
* `Flow.isInvariant_stableSet` and `Flow.isInvariant_unstableSet`: invariance
  under time translation.
* `Flow.fixed_of_mem_stableSet` and `Flow.fixed_of_mem_unstableSet`: a limiting
  point of a trajectory is fixed.
* `Flow.stableSet_reverse` and `Flow.unstableSet_reverse`: time reversal exchanges
  stable and unstable sets.
-/

public section

open Filter Set Topology

namespace Flow

variable {α : Type*} [TopologicalSpace α]

/-- The **stable set** of `x` under a real flow `φ`: the points whose trajectories converge to
`x` as time tends to `+∞`. -/
def stableSet (φ : _root_.Flow ℝ α) (x : α) : Set α :=
  {y | Tendsto (fun t ↦ φ t y) atTop (𝓝 x)}

/-- The **unstable set** of `x` under a real flow `φ`: the points whose trajectories converge to
`x` as time tends to `-∞`. -/
def unstableSet (φ : _root_.Flow ℝ α) (x : α) : Set α :=
  {y | Tendsto (fun t ↦ φ t y) atBot (𝓝 x)}

/-- Membership in a stable set means convergence of the trajectory in forward time. -/
@[simp]
theorem mem_stableSet {φ : _root_.Flow ℝ α} {x y : α} :
    y ∈ stableSet φ x ↔ Tendsto (fun t ↦ φ t y) atTop (𝓝 x) :=
  Iff.rfl

/-- Membership in an unstable set means convergence of the trajectory in backward time. -/
@[simp]
theorem mem_unstableSet {φ : _root_.Flow ℝ α} {x y : α} :
    y ∈ unstableSet φ x ↔ Tendsto (fun t ↦ φ t y) atBot (𝓝 x) :=
  Iff.rfl

/-- The stable set of a point is invariant under every time map of the flow. -/
theorem isInvariant_stableSet (φ : _root_.Flow ℝ α) (x : α) :
    IsInvariant φ (stableSet φ x) := by
  intro t y hy
  rw [mem_stableSet] at hy ⊢
  simpa only [Function.comp_def, ← φ.map_add, id_eq] using
    hy.comp (tendsto_atTop_add_const_right atTop t tendsto_id)

/-- The unstable set of a point is invariant under every time map of the flow. -/
theorem isInvariant_unstableSet (φ : _root_.Flow ℝ α) (x : α) :
    IsInvariant φ (unstableSet φ x) := by
  intro t y hy
  rw [mem_unstableSet] at hy ⊢
  simpa only [Function.comp_def, ← φ.map_add, id_eq] using
    hy.comp (tendsto_atBot_add_const_right atBot t tendsto_id)

/-- If some trajectory converges to `x` in forward time, then `x` is fixed by every time map of
the flow. -/
theorem fixed_of_mem_stableSet [T2Space α] {φ : _root_.Flow ℝ α} {x y : α}
    (hy : y ∈ stableSet φ x) (t : ℝ) :
    φ t x = x := by
  rw [mem_stableSet] at hy
  have hleft : Tendsto (fun u ↦ φ t (φ u y)) atTop (𝓝 (φ t x)) :=
    (φ.continuous_toFun t).continuousAt.tendsto.comp hy
  have hright : Tendsto (fun u ↦ φ t (φ u y)) atTop (𝓝 x) := by
    simpa only [Function.comp_def, ← φ.map_add, add_comm, id_eq] using
      hy.comp (tendsto_atTop_add_const_right atTop t tendsto_id)
  exact tendsto_nhds_unique hleft hright

/-- If some trajectory converges to `x` in backward time, then `x` is fixed by every time map of
the flow. -/
theorem fixed_of_mem_unstableSet [T2Space α] {φ : _root_.Flow ℝ α} {x y : α}
    (hy : y ∈ unstableSet φ x) (t : ℝ) :
    φ t x = x := by
  rw [mem_unstableSet] at hy
  have hleft : Tendsto (fun u ↦ φ t (φ u y)) atBot (𝓝 (φ t x)) :=
    (φ.continuous_toFun t).continuousAt.tendsto.comp hy
  have hright : Tendsto (fun u ↦ φ t (φ u y)) atBot (𝓝 x) := by
    simpa only [Function.comp_def, ← φ.map_add, add_comm, id_eq] using
      hy.comp (tendsto_atBot_add_const_right atBot t tendsto_id)
  exact tendsto_nhds_unique hleft hright

/-- A point belongs to its stable set exactly when it is fixed by the flow. -/
@[simp 1200]
theorem self_mem_stableSet_iff [T2Space α] {φ : _root_.Flow ℝ α} {x : α} :
    x ∈ stableSet φ x ↔ ∀ t, φ t x = x := by
  refine ⟨fun hx t ↦ fixed_of_mem_stableSet hx t, fun hx ↦ ?_⟩
  rw [mem_stableSet]
  simpa only [hx] using (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ x) atTop (𝓝 x))

/-- A point belongs to its unstable set exactly when it is fixed by the flow. -/
@[simp 1200]
theorem self_mem_unstableSet_iff [T2Space α] {φ : _root_.Flow ℝ α} {x : α} :
    x ∈ unstableSet φ x ↔ ∀ t, φ t x = x := by
  refine ⟨fun hx t ↦ fixed_of_mem_unstableSet hx t, fun hx ↦ ?_⟩
  rw [mem_unstableSet]
  simpa only [hx] using (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ x) atBot (𝓝 x))

/-- Time reversal is an involution. -/
@[simp]
theorem reverse_reverse {τ : Type*} [TopologicalSpace τ] [SubtractionCommMonoid τ]
    [ContinuousNeg τ] (φ : _root_.Flow τ α) : φ.reverse.reverse = φ :=
  _root_.Flow.ext fun t _ ↦ by simp only [_root_.Flow.reverse_apply, neg_neg]

/-- Time reversal exchanges stable and unstable sets. -/
@[simp]
theorem stableSet_reverse (φ : _root_.Flow ℝ α) (x : α) :
    stableSet φ.reverse x = unstableSet φ x := by
  ext y
  simp only [mem_stableSet, mem_unstableSet, _root_.Flow.reverse_apply]
  constructor
  · intro h
    simpa only [Function.comp_def, neg_neg] using h.comp tendsto_neg_atBot_atTop
  · intro h
    simpa only [Function.comp_def, neg_neg] using h.comp tendsto_neg_atTop_atBot

/-- Time reversal exchanges unstable and stable sets. -/
@[simp]
theorem unstableSet_reverse (φ : _root_.Flow ℝ α) (x : α) :
    unstableSet φ.reverse x = stableSet φ x := by
  rw [← stableSet_reverse φ.reverse x, reverse_reverse]

/-- Under the identity flow, the stable set of `x` is the singleton `{x}`. -/
@[simp]
theorem stableSet_id [T1Space α] (x : α) :
    stableSet (_root_.Flow.id ℝ α) x = {x} := by
  ext y
  simp [stableSet]

/-- Under the identity flow, the unstable set of `x` is the singleton `{x}`. -/
@[simp]
theorem unstableSet_id [T1Space α] (x : α) :
    unstableSet (_root_.Flow.id ℝ α) x = {x} := by
  ext y
  simp [unstableSet]

end Flow
