/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Connected.LocallyConnected
import TauCeti.Topology.LocallyConnected

/-!
# Uniform local connectedness

A set `s` in a pseudometric space is **uniformly locally connected** when the connected sets
joining nearby points can be chosen small *at a rate independent of where they are*: for every
`ε > 0` there is a single `δ > 0` such that any two points of `s` at distance less than `δ` lie in
a connected subset of `s` of diameter at most `ε`.

This is the metric strengthening of local connectedness, and the two notions are *equivalent on a
compact set*. That equivalence is what this file proves:
`TauCeti.IsCompact.isUniformlyLocallyConnected` derives the uniform statement from the local one by
a Lebesgue-number argument, and `TauCeti.IsUniformlyLocallyConnected.locallyConnectedSpace` returns
from the uniform statement to the local one with no compactness at all.

Compactness is genuinely needed for the first direction. The graph of `x ↦ sin (1 / x)` over
`(0, 1]` is homeomorphic to an interval, hence locally connected, but not uniformly so: the
oscillations crowd together as `x → 0`, so two points of equal ordinate on distinct oscillations
come arbitrarily close to one another, while every connected subset of the graph joining them
sweeps out a whole oscillation and so meets ordinates near both `1` and `-1`. Such a set has
diameter at least `2`, so no `δ` works for `ε = 1`. It fails no hypothesis but compactness.

## Why this notion

Local connectedness is a statement about one point at a time, and an argument that must produce a
small connected set near *every* point of a set at once cannot use it directly. The uniform form is
what such arguments actually consume, and on a compact set it costs nothing extra.

The intended consumer is layer **L5** of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`), Carathéodory's boundary correspondence. The
sufficiency half of Carathéodory's continuity theorem — a conformal map of the disc onto a bounded
domain with locally connected boundary extends continuously to the closed disc — controls the image
of a crosscut, and what it asks of the boundary is exactly a uniform `ε`–`δ` supply of small
connected sets joining nearby boundary points. The boundary of a bounded domain is compact, so the
equivalence proved here converts the roadmap's hypothesis into that form once and for all; the
conformal consequences are in `TauCeti/Analysis/Complex/Conformal/Jordan/Domain.lean` and
`TauCeti/Analysis/Complex/Conformal/LocallyConnectedBoundary.lean`.

Nothing here is specific to that application: the definition and both implications are stated for
an arbitrary pseudometric space. Mathlib has `LocallyConnectedSpace` but no metric refinement of
it, and no Lebesgue-number consequence of this shape.

## Main definitions

* `TauCeti.IsUniformlyLocallyConnected` — the uniform `ε`–`δ` form of local connectedness for a
  set in a pseudometric space.

## Main results

* `TauCeti.IsCompact.isUniformlyLocallyConnected` — a compact locally connected set is uniformly
  locally connected.
* `TauCeti.IsUniformlyLocallyConnected.locallyConnectedSpace` — a uniformly locally connected set
  is locally connected; no compactness is used.
* `TauCeti.IsUniformlyLocallyConnected.exists_isConnected_superset` — a small enough subset is
  enclosed in a small connected subset, at a rate independent of the subset.
* `TauCeti.IsCompact.isUniformlyLocallyConnected_iff` — on a compact set the two notions agree.
* `TauCeti.Convex.isUniformlyLocallyConnected` — a convex set in a real normed space is uniformly
  locally connected, with the joining segment as the connected set.
* `TauCeti.isUniformlyLocallyConnected_image_of_isCompact` — a continuous image of a compact,
  locally connected set is uniformly locally connected.

## References

* R. L. Moore, *Foundations of Point Set Theory*, Ch. IV (uniform local connectedness, "property
  S").
* J. G. Hocking and G. S. Young, *Topology*, Ch. 3.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2 (the use in Carathéodory's
  continuity theorem).
-/

public section

namespace TauCeti

open Metric Set Topology

variable {X : Type*} [PseudoMetricSpace X] {s : Set X}

/-- A set `s` is **uniformly locally connected** if for every `ε > 0` there is a `δ > 0` such that
any two points of `s` at distance less than `δ` are joined by a connected subset of `s` of diameter
at most `ε`.

The smallness of the joining set is spelled out as a pairwise distance bound rather than as
`Metric.diam C ≤ ε`, because `Metric.diam` is `0` on an unbounded set, which would let an unbounded
`C` satisfy the condition vacuously. The lemma
`TauCeti.IsUniformlyLocallyConnected.exists_isConnected_diam_le` recovers the diameter phrasing,
boundedness of the joining set being one of its consequences. -/
def IsUniformlyLocallyConnected (s : Set X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ a ∈ s, ∀ b ∈ s, dist a b < δ →
    ∃ C ⊆ s, IsConnected C ∧ a ∈ C ∧ b ∈ C ∧ ∀ x ∈ C, ∀ y ∈ C, dist x y ≤ ε

/-- `TauCeti.IsUniformlyLocallyConnected` restated as an `Iff`, so that it can be established and
consumed in its native pairwise-distance form without unfolding the definition — which downstream
modules cannot do, the definition being public but not exposed. -/
theorem isUniformlyLocallyConnected_def :
    IsUniformlyLocallyConnected s ↔ ∀ ε > 0, ∃ δ > 0, ∀ a ∈ s, ∀ b ∈ s, dist a b < δ →
      ∃ C ⊆ s, IsConnected C ∧ a ∈ C ∧ b ∈ C ∧ ∀ x ∈ C, ∀ y ∈ C, dist x y ≤ ε := Iff.rfl

/-- The elimination form of `TauCeti.IsUniformlyLocallyConnected`: each `ε > 0` comes with a `δ > 0`
serving every pair of points of `s` at distance less than `δ` at once. -/
theorem IsUniformlyLocallyConnected.exists_isConnected (h : IsUniformlyLocallyConnected s) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ s, ∀ b ∈ s, dist a b < δ →
      ∃ C ⊆ s, IsConnected C ∧ a ∈ C ∧ b ∈ C ∧ ∀ x ∈ C, ∀ y ∈ C, dist x y ≤ ε :=
  isUniformlyLocallyConnected_def.mp h ε hε

/-- The diameter phrasing of `TauCeti.IsUniformlyLocallyConnected`: the joining set is bounded and
has diameter at most `ε`. -/
theorem IsUniformlyLocallyConnected.exists_isConnected_diam_le (h : IsUniformlyLocallyConnected s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ s, ∀ b ∈ s, dist a b < δ →
      ∃ C ⊆ s, IsConnected C ∧ a ∈ C ∧ b ∈ C ∧ Bornology.IsBounded C ∧ diam C ≤ ε := by
  obtain ⟨δ, hδ, hjoin⟩ := h.exists_isConnected hε
  refine ⟨δ, hδ, fun a ha b hb hab => ?_⟩
  obtain ⟨C, hCs, hCconn, hCa, hCb, hCsmall⟩ := hjoin a ha b hb hab
  exact ⟨C, hCs, hCconn, hCa, hCb, isBounded_iff.mpr ⟨ε, hCsmall⟩,
    diam_le_of_forall_dist_le hε.le hCsmall⟩

/-- `TauCeti.IsUniformlyLocallyConnected` is equivalent to its diameter phrasing: it may be
established, and not just used, from joining sets that are bounded and of diameter at most `ε`. -/
theorem isUniformlyLocallyConnected_iff_exists_isConnected_diam_le :
    IsUniformlyLocallyConnected s ↔ ∀ ε > 0, ∃ δ > 0, ∀ a ∈ s, ∀ b ∈ s, dist a b < δ →
      ∃ C ⊆ s, IsConnected C ∧ a ∈ C ∧ b ∈ C ∧ Bornology.IsBounded C ∧ diam C ≤ ε := by
  refine ⟨fun h ε hε => h.exists_isConnected_diam_le hε,
    fun h => isUniformlyLocallyConnected_def.mpr fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hjoin⟩ := h ε hε
  refine ⟨δ, hδ, fun a ha b hb hab => ?_⟩
  obtain ⟨C, hCs, hCconn, hCa, hCb, hCbdd, hCdiam⟩ := hjoin a ha b hb hab
  exact ⟨C, hCs, hCconn, hCa, hCb,
    fun x hx y hy => (dist_le_diam_of_mem hCbdd hx hy).trans hCdiam⟩

/-- **A uniformly locally connected set encloses each of its small subsets in a small connected
set.** For every `ε > 0` there is a single `δ > 0` — depending on `s` and `ε` alone — such that
every nonempty bounded subset of `s` of diameter less than `δ` is contained in a connected subset
of `s` of diameter at most `ε`.

This upgrades the two-point statement `TauCeti.IsUniformlyLocallyConnected.exists_isConnected` from
a pair of points to a whole small set, one connected set swallowing the subset entirely. The `δ`
produced is the two-point modulus of `ε / 2`, not of `ε`: the enclosing set is reached from the
fixed point `a` below, so each of its points is allowed only half of the budget.

The enclosing set is built by taking every candidate at once, as in
`TauCeti.IsUniformlyLocallyConnected.locallyConnectedSpace`: fix a point `a` of the subset and
unite every preconnected subset of `s` that contains `a` and stays within `ε / 2` of it. -/
theorem IsUniformlyLocallyConnected.exists_isConnected_superset
    (h : IsUniformlyLocallyConnected s) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ⊆ s, Bornology.IsBounded t → t.Nonempty → diam t < δ →
      ∃ S ⊆ s, IsConnected S ∧ t ⊆ S ∧ diam S ≤ ε := by
  obtain ⟨δ, hδ, hjoin⟩ := h.exists_isConnected (by linarith : (0 : ℝ) < ε / 2)
  refine ⟨δ, hδ, fun t hts htb htne hdiam => ?_⟩
  obtain ⟨a, ha⟩ := htne
  -- every preconnected subset of `s` through `a` that stays within `ε / 2` of it
  set 𝒞 : Set (Set X) := {T : Set X | T ⊆ s ∧ IsPreconnected T ∧ a ∈ T ∧
    ∀ x ∈ T, dist x a ≤ ε / 2}
  have haS : a ∈ ⋃₀ 𝒞 :=
    ⟨{a}, ⟨singleton_subset_iff.mpr (hts ha), isPreconnected_singleton, rfl,
      fun x hx => by rw [mem_singleton_iff.mp hx, dist_self]; linarith⟩, rfl⟩
  refine ⟨⋃₀ 𝒞, ?_, ⟨⟨a, haS⟩, isPreconnected_sUnion a 𝒞 (fun T hT => hT.2.2.1)
    fun T hT => hT.2.1⟩, ?_, ?_⟩
  · rintro x ⟨T, hT, hxT⟩
    exact hT.1 hxT
  · -- uniform local connectedness joins each point of `t` to `a` by a set being united
    intro b hbt
    obtain ⟨C, hCs, hCconn, hCa, hCb, hCsmall⟩ := hjoin a (hts ha) b (hts hbt)
      (lt_of_le_of_lt (dist_le_diam_of_mem htb ha hbt) hdiam)
    exact ⟨C, ⟨hCs, hCconn.isPreconnected, hCa, fun x hx => hCsmall x hx a hCa⟩, hCb⟩
  · refine diam_le_of_forall_dist_le hε.le ?_
    rintro x ⟨T, hT, hxT⟩ y ⟨T', hT', hyT'⟩
    have hx : dist x a ≤ ε / 2 := hT.2.2.2 x hxT
    have hy : dist y a ≤ ε / 2 := hT'.2.2.2 y hyT'
    calc dist x y ≤ dist x a + dist a y := dist_triangle x a y
      _ ≤ ε / 2 + ε / 2 := by rw [dist_comm a y]; linarith
      _ = ε := by ring

/-- The empty set is uniformly locally connected, vacuously. -/
@[simp]
theorem isUniformlyLocallyConnected_empty : IsUniformlyLocallyConnected (∅ : Set X) :=
  isUniformlyLocallyConnected_def.mpr fun ε hε => ⟨ε, hε, by simp⟩

/-- **A convex set is uniformly locally connected**: two points at distance less than `ε / 2` are
joined by the segment between them, which stays in the set by convexity and, by
`segment_subset_closedBall_left`, inside the closed ball of radius `dist a b < ε / 2` about the
first endpoint, so its points are pairwise within `ε`.

This is the basic example, and the one the closed disc supplies in the conformal application. -/
protected theorem Convex.isUniformlyLocallyConnected {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {t : Set E} (ht : Convex ℝ t) : IsUniformlyLocallyConnected t := by
  refine isUniformlyLocallyConnected_def.mpr fun ε hε => ⟨ε / 2, by linarith,
    fun a ha b hb hab => ⟨segment ℝ a b,
    ht.segment_subset ha hb, (convex_segment a b).isConnected ⟨a, left_mem_segment ℝ a b⟩,
    left_mem_segment ℝ a b, right_mem_segment ℝ a b, fun x hx y hy => ?_⟩⟩
  have hx' := mem_closedBall.mp (segment_subset_closedBall_left a b hx)
  have hy' := mem_closedBall.mp (segment_subset_closedBall_left a b hy)
  linarith [dist_triangle_right x y a]

/-! ## The compact case: local connectedness suffices -/

/-- **A compact locally connected set is uniformly locally connected.**

Given `ε > 0`, local connectedness supplies for each point a connected open neighbourhood inside
the ball of radius `ε / 2` about it — the connected component of that ball, open precisely because
the subspace is locally connected. These cover the compact set, and a Lebesgue number `δ` for the
cover does the rest: two points at distance less than `δ` lie in a common ball of radius `δ`, hence
in a common member of the cover, whose points are pairwise within `ε` of one another. -/
protected theorem IsCompact.isUniformlyLocallyConnected [LocallyConnectedSpace s]
    (hs : IsCompact s) : IsUniformlyLocallyConnected s := by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  rw [isUniformlyLocallyConnected_def]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  -- The cover of the subspace by the connected components of the small balls.
  have hcopen : ∀ x : s, IsOpen (connectedComponentIn (ball x (ε / 2)) x) := fun _ =>
    isOpen_ball.connectedComponentIn
  have hcmem : ∀ x : s, x ∈ connectedComponentIn (ball x (ε / 2)) x := fun _ =>
    mem_connectedComponentIn (mem_ball_self hε2)
  obtain ⟨δ, hδ, hlb⟩ :=
    lebesgue_number_lemma_of_metric (c := fun x : s => connectedComponentIn (ball x (ε / 2)) x)
      isCompact_univ hcopen fun x _ => mem_iUnion.mpr ⟨x, hcmem x⟩
  refine ⟨δ, hδ, fun a ha b hb hab => ?_⟩
  -- The Lebesgue number applied at `a`: a single member of the cover contains both `a` and `b`.
  obtain ⟨x, hx⟩ := hlb ⟨a, ha⟩ (mem_univ _)
  have hamem : (⟨a, ha⟩ : s) ∈ connectedComponentIn (ball x (ε / 2)) x := hx (mem_ball_self hδ)
  have hbmem : (⟨b, hb⟩ : s) ∈ connectedComponentIn (ball x (ε / 2)) x :=
    hx (mem_ball.mpr (by rw [Subtype.dist_eq, dist_comm]; exact hab))
  -- Its points lie within `ε / 2` of `x`, hence within `ε` of one another.
  have hball : ∀ w ∈ (connectedComponentIn (ball x (ε / 2)) x : Set s), dist w x < ε / 2 :=
    fun w hw => mem_ball.mp (connectedComponentIn_subset _ _ hw)
  -- Transport the component down to `X` along the inclusion, an inducing map.
  refine ⟨Subtype.val '' connectedComponentIn (ball x (ε / 2)) x, Subtype.coe_image_subset _ _,
    ⟨⟨_, mem_image_of_mem _ hamem⟩, IsInducing.subtypeVal.isPreconnected_image.mpr
      isPreconnected_connectedComponentIn⟩, mem_image_of_mem _ hamem,
    mem_image_of_mem _ hbmem, ?_⟩
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  have hu' : dist (u : X) (x : X) < ε / 2 := hball u hu
  have hv' : dist (v : X) (x : X) < ε / 2 := hball v hv
  linarith [dist_triangle_right (u : X) (v : X) (x : X)]

/-! ## The converse: uniform local connectedness implies local connectedness -/

/-- **A uniformly locally connected set is locally connected.** No compactness is needed.

The connected neighbourhood of a point `x` of `s` inside a prescribed ball is built by *taking all
candidates at once*: the union of every connected subset of `s` that contains `x` and stays within
`ε / 2` of it. The union is connected because all its members contain `x`, it stays inside the ball
of radius `ε` about `x`, and it is a neighbourhood of `x` in `s` because the uniform hypothesis
puts every point within `δ` of `x` into one of the sets being united. -/
theorem IsUniformlyLocallyConnected.locallyConnectedSpace (h : IsUniformlyLocallyConnected s) :
    LocallyConnectedSpace s := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨δ, hδ, hjoin⟩ := h.exists_isConnected hε2
  refine ⟨⋃₀ {C : Set s | IsPreconnected C ∧ x ∈ C ∧ C ⊆ closedBall x (ε / 2)}, ?_,
    isPreconnected_sUnion x _ (fun C hC => hC.2.1) fun C hC => hC.1, ?_⟩
  · -- The union contains the ball of radius `δ` about `x`, hence is a neighbourhood of `x`.
    refine Filter.mem_of_superset (ball_mem_nhds x hδ) fun y hy => ?_
    obtain ⟨C, hCs, hCconn, hCx, hCy, hCsmall⟩ :=
      hjoin x x.2 y y.2 (by rw [dist_comm, ← Subtype.dist_eq]; exact mem_ball.mp hy)
    -- Pull the joining set back to the subspace; it stays preconnected because it already lies
    -- in `s` and the inclusion is inducing.
    refine ⟨(Subtype.val ⁻¹' C : Set s),
      ⟨?_, hCx, fun z hz => mem_closedBall.mpr (hCsmall _ hz _ hCx)⟩, hCy⟩
    refine IsInducing.subtypeVal.isPreconnected_image.mp ?_
    rw [Subtype.image_preimage_coe, inter_eq_self_of_subset_right hCs]
    exact hCconn.isPreconnected
  · -- The union lies in the ball of radius `ε`, hence in `U`.
    rintro y ⟨C, hC, hyC⟩
    exact hball (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp (hC.2.2 hyC)) (by linarith)))

/-- **On a compact set, uniform local connectedness and local connectedness agree.** The forward
implication is `TauCeti.IsUniformlyLocallyConnected.locallyConnectedSpace`, which needs no
compactness; the backward one is `TauCeti.IsCompact.isUniformlyLocallyConnected`, which does. -/
protected theorem IsCompact.isUniformlyLocallyConnected_iff (hs : IsCompact s) :
    IsUniformlyLocallyConnected s ↔ LocallyConnectedSpace s :=
  ⟨fun h => h.locallyConnectedSpace, fun h => haveI := h; IsCompact.isUniformlyLocallyConnected hs⟩

/-! ## Continuous images -/

/-- **A continuous image of a compact, locally connected set is uniformly locally connected.** The
uniform companion of `TauCeti.locallyConnectedSpace_image_of_isCompact`: that lemma makes the image
locally connected, the image is compact, and on a compact set the two notions agree. -/
theorem isUniformlyLocallyConnected_image_of_isCompact {Z : Type*} [TopologicalSpace Z] [T2Space X]
    {t : Set Z} {g : Z → X} [LocallyConnectedSpace t] (ht : IsCompact t) (hg : ContinuousOn g t) :
    IsUniformlyLocallyConnected (g '' t) :=
  haveI := locallyConnectedSpace_image_of_isCompact ht hg
  IsCompact.isUniformlyLocallyConnected (ht.image_of_continuousOn hg)

end TauCeti
