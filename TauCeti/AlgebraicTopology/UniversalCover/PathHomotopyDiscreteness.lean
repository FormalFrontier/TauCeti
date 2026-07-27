/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.On
import Mathlib.Topology.Order

/-!
# Discreteness of path-homotopy fibres

This file contains the tube construction proving that fixed-endpoint path-homotopy quotients are
discrete in semilocally simply connected, locally path-connected spaces. It is adapted from Kim
Morrison's Mathlib universal-cover drafts, especially
[#31576](https://github.com/leanprover-community/mathlib4/pull/31576) and
[#38292](https://github.com/leanprover-community/mathlib4/pull/38292), for Stage 0.1 of the
`TauCetiRoadmap/UniversalCovers` roadmap, following the earlier Tau Ceti work in
[#42](https://github.com/TauCetiProject/TauCeti/pull/42).
-/

noncomputable section

open CategoryTheory Filter FundamentalGroupoid Set Topology TauCeti

variable {X : Type*} [TopologicalSpace X]

/-! ### Tube data structures -/

/-- A partition of the unit interval `[0, 1]` into `n` segments, used as scaffolding for the
tube construction below. (It is `public` only so that the `structureInType` environment linter
can resolve its projections across the module boundary; it is not intended as reusable API.) -/
public structure IntervalPartition (n : ℕ) : Type where
  /-- The partition points. -/
  t : Fin (n + 1) → unitInterval
  /-- The partition points are monotone. -/
  mono : Monotone t
  /-- The first partition point is `0`. -/
  t_zero : t 0 = 0
  /-- The last partition point is `1`. -/
  t_last : t (Fin.last n) = 1

namespace IntervalPartition

attribute [simp, grind =] t_zero t_last

/-- `IntervalPartition 0` is empty: a single partition point cannot be simultaneously
`0` and `1`.

`public` because the based-path openness argument in
`TauCeti.AlgebraicTopology.UniversalCover.BasedPath` rules out the `n = 0` tube by
`isEmptyElim` on the partition. -/
public instance : IsEmpty (IntervalPartition 0) where
  false part := by
    have h0 : part.t 0 = 0 := part.t_zero
    have h1 : part.t 0 = 1 := part.t_last
    exact zero_ne_one (h0.symm.trans h1)

end IntervalPartition

/-- Data for a tubular neighborhood in an SLSC space: segment neighborhoods, point
neighborhoods at all partition points, and the openness/path-connectedness/SLSC subset data.
Like `IntervalPartition`, this is tube scaffolding marked `public` only so the `structureInType`
environment linter can resolve its projections; it is not intended as reusable API. -/
public structure TubeData (X : Type*) [TopologicalSpace X] (n : ℕ) : Type _ where
  /-- Segment neighborhoods -/
  U : Fin n → Set X
  /-- Point neighborhoods at ALL partition points (including endpoints) -/
  V : Fin (n + 1) → Set X
  /-- Each U[i] is open -/
  U_open : ∀ i, IsOpen (U i)
  /-- SLSC property: paths in U[i] with same endpoints are homotopic -/
  U_slsc : ∀ i, IsPathHomotopyTrivial (U i)
  /-- Each V[j] is open -/
  V_open : ∀ j, IsOpen (V j)
  /-- Each V[j] is path-connected -/
  V_pathConn : ∀ j, IsPathConnected (V j)
  /-- For each segment i, the left endpoint neighborhood V[i.castSucc] is in U[i] -/
  V_left_subset : ∀ i : Fin n, V i.castSucc ⊆ U i
  /-- For each segment i, the right endpoint neighborhood V[i.succ] is in U[i] -/
  V_right_subset : ∀ i : Fin n, V i.succ ⊆ U i

/-- A path γ is in the tube defined by partition `part` and tube data T.
This means:
1. γ stays in the segment neighborhoods U[i] on each interval [t[i], t[i+1]]
2. γ passes through the point neighborhoods V[j] at ALL partition points

`public` because the variable-endpoint based-path openness argument in
`TauCeti.AlgebraicTopology.UniversalCover.BasedPath` builds and destructures tube membership
directly (it refines the terminal vertex neighborhood before appealing to
`Path.tube_subset_homotopy_class_source`); it is not otherwise part of the reusable API. -/
public structure PathInTube {X : Type*} [TopologicalSpace X] {x y : X} {n : ℕ}
    (γ : Path x y) (part : IntervalPartition n) (T : TubeData X n) : Prop where
  /-- γ stays in the segment neighborhoods U[i] on each interval [t[i], t[i+1]] -/
  stays_in_U : ∀ i (s : unitInterval),
    (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → γ s ∈ T.U i
  /-- γ passes through the point neighborhoods V[j] at ALL partition points -/
  passes_through_V : ∀ j, γ (part.t j) ∈ T.V j

/-- If γ is in a tube, then its subpath on segment i has range in U[i]. -/
lemma PathInTube.subpath_range_subset {X : Type*} [TopologicalSpace X] {x y : X} {n : ℕ}
    {γ : Path x y} {part : IntervalPartition n} {T : TubeData X n}
    (hγ : PathInTube γ part T) (i : Fin n) :
    Set.range (γ.subpath (part.t i.castSucc) (part.t i.succ)) ⊆ T.U i := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  have h_mono : (part.t i.castSucc : ℝ) ≤ part.t i.succ :=
    part.mono i.castSucc_lt_succ.le
  simpa [Path.subpath] using
    hγ.stays_in_U i (Set.Icc.convexComb (part.t i.castSucc) (part.t i.succ) t)
      ⟨Set.Icc.le_convexComb h_mono t, Set.Icc.convexComb_le h_mono t⟩

/-- Convert TubeData with partition to the set of paths in the tube -/
def TubeData.toSet {X : Type*} [TopologicalSpace X] {x y : X} {n : ℕ}
    (part : IntervalPartition n) (T : TubeData X n) : Set (Path x y) :=
  {γ | PathInTube γ part T}

@[simp] theorem TubeData.mem_toSet_iff {X : Type*} [TopologicalSpace X] {x y : X} {n : ℕ}
    (part : IntervalPartition n) (T : TubeData X n) (γ : Path x y) :
    γ ∈ T.toSet part ↔ PathInTube γ part T :=
  Iff.rfl

/-- File-local adapter from Mathlib's unit-interval open-cover partition lemma to the segment
data needed by the tube construction. -/
private theorem Path.exists_partition_with_property {x y : X} (γ : Path x y)
    (P : Set X → Prop)
    (h : ∀ z ∈ Set.range γ, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ P U) :
    ∃ (n : ℕ) (part : IntervalPartition n),
      ∀ i : Fin n, ∃ U : Set X, IsOpen U ∧ P U ∧
        ∀ s : unitInterval, (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) →
          γ s ∈ U := by
  choose U hU_open hU_mem hU_P using h
  obtain ⟨t, ht0, ht_mono, ⟨N, hN⟩, ht_cover⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun z : Set.range γ ↦ (hU_open z.val z.property).preimage γ.continuous)
      (fun s _ ↦
        Set.mem_iUnion.2
          ⟨⟨γ s, ⟨s, rfl⟩⟩, hU_mem (γ s) ⟨s, rfl⟩⟩)
  let part : IntervalPartition N := {
    t := fun k ↦ t (k : ℕ)
    mono := fun _ _ hij ↦ ht_mono hij
    t_zero := by simpa using ht0
    t_last := by simpa using hN N le_rfl
  }
  refine ⟨N, part, fun i ↦ ?_⟩
  obtain ⟨⟨z, hz⟩, h_seg⟩ := ht_cover i
  exact ⟨U z hz, hU_open z hz, hU_P z hz, fun s hs ↦ h_seg ⟨hs.1, hs.2⟩⟩

/-- Given segment neighborhoods covering each subpath of `γ`, construct the vertex neighborhoods
as path components of the finite intersections of adjacent segment neighborhoods. -/
private theorem Path.exists_vertexNeighborhood_family [LocallyPathConnectedSpace X]
    {x y : X} {γ : Path x y} {n : ℕ}
    {t : Fin (n + 1) → unitInterval} {U : Fin n → Set X}
    (h_mono : Monotone t) (hU_open : ∀ i, IsOpen (U i))
    (hU_contains : ∀ i : Fin n, ∀ s : unitInterval,
      (t i.castSucc : ℝ) ≤ s ∧ s ≤ (t i.succ : ℝ) → γ s ∈ U i) :
    ∃ V : Fin (n + 1) → Set X,
      (∀ j, IsOpen (V j)) ∧
      (∀ j, IsPathConnected (V j)) ∧
      (∀ j, γ (t j) ∈ V j) ∧
      (∀ i : Fin n, V i.castSucc ⊆ U i) ∧
      (∀ i : Fin n, V i.succ ⊆ U i) := by
  have V_data : ∀ j : Fin (n + 1),
      ∃ V : Set X, IsOpen V ∧ IsPathConnected V ∧ γ (t j) ∈ V ∧
        (∀ i : Fin n, j = i.castSucc → V ⊆ U i) ∧
        (∀ i : Fin n, j = i.succ → V ⊆ U i) := by
    intro j
    let U_inter := ⋂ i : Fin n, ⋂ (_ : j = i.castSucc ∨ j = i.succ), U i
    have hγ_in_inter : γ (t j) ∈ U_inter := by
      simp only [U_inter, Set.mem_iInter]
      intro i hi
      exact hU_contains i (t j) <| by
        cases hi with
        | inl h =>
            constructor <;> apply h_mono <;> simp [h, Fin.le_def]
        | inr h =>
            constructor <;> apply h_mono <;> simp [h, Fin.le_def, Fin.succ]
    refine ⟨pathComponentIn U_inter (γ (t j)), ?_, isPathConnected_pathComponentIn hγ_in_inter,
      mem_pathComponentIn_self hγ_in_inter, ?_, ?_⟩
    · apply IsOpen.pathComponentIn
      apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro _
      exact hU_open i
    · intro i hi
      trans U_inter
      · exact pathComponentIn_subset
      · exact Set.iInter_subset_of_subset i <| Set.iInter_subset_of_subset (Or.inl hi) <| subset_rfl
    · intro i hi
      trans U_inter
      · exact pathComponentIn_subset
      · exact Set.iInter_subset_of_subset i <| Set.iInter_subset_of_subset (Or.inr hi) <| subset_rfl
  choose V hV_open hV_pathConn hγ_in_V hV_left hV_right using V_data
  refine ⟨V, hV_open, hV_pathConn, hγ_in_V, ?_, ?_⟩
  · intro i
    exact hV_left i.castSucc i rfl
  · intro i
    exact hV_right i.succ i rfl

/-- If `X` is locally path-connected and SLSC along the range of `γ`, then `γ` lies in a
path-homotopy-trivial tube.

`public` because `TauCeti.AlgebraicTopology.UniversalCover.BasedPath` consumes the tube (partition
and tube data) around a based path to build an open endpoint-preimage neighborhood. -/
public theorem Path.exists_pathHomotopyTrivial_tube
    [LocallyPathConnectedSpace X] {x y : X}
    (γ : Path x y) (hslsc : SemilocallySimplyConnectedOn (Set.range γ)) :
    ∃ (n : ℕ) (part : IntervalPartition n) (T : TubeData X n), PathInTube γ part T := by
  obtain ⟨n, part, h_partition⟩ := γ.exists_partition_with_property
    (fun U ↦ IsPathConnected U ∧ IsPathHomotopyTrivial U)
    (fun z hz ↦
      (hslsc.at hz).exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial)
  choose U hU_open hU_prop hU_contains using h_partition
  obtain ⟨V, hV_open, hV_pathConn, hγ_in_V, hV_left, hV_right⟩ :=
    Path.exists_vertexNeighborhood_family part.mono hU_open hU_contains
  let T : TubeData X n := {
    U := U
    V := V
    U_open := hU_open
    U_slsc := fun i ↦ (hU_prop i).2
    V_open := hV_open
    V_pathConn := hV_pathConn
    V_left_subset := hV_left
    V_right_subset := hV_right
  }
  refine ⟨n, part, T, ?_⟩
  exact { stays_in_U := hU_contains, passes_through_V := hγ_in_V }

/-- The set of paths sending each partition segment `[part.t i.castSucc, part.t i.succ]` into the
corresponding set `U i` is open, provided every `U i` is open. Only openness of the `U i` is used,
via the compact-open topology on `C(unitInterval, X)` restricted to each compact segment. -/
private theorem isOpen_setOf_forall_segment_mapsTo {x y : X} {n : ℕ}
    (part : IntervalPartition n) (U : Fin n → Set X) (hU_open : ∀ i, IsOpen (U i)) :
    IsOpen {γ' : Path x y | ∀ i (s : unitInterval),
      (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → γ' s ∈ U i} := by
  have hrw : {γ' : Path x y | ∀ i (s : unitInterval),
        (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → γ' s ∈ U i} =
      ⋂ i : Fin n, {γ' : Path x y | ∀ s : unitInterval,
        (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → γ' s ∈ U i} := by
    ext γ'
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [hrw]
  apply isOpen_iInter_of_finite
  intro i
  let K_i : Set unitInterval := Set.Icc (part.t i.castSucc) (part.t i.succ)
  have h_compact_K : IsCompact K_i := isCompact_Icc
  have h_eq : {γ' : Path x y | ∀ s : unitInterval,
      (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → γ' s ∈ U i} =
    {γ' : Path x y | Set.MapsTo γ' K_i (U i)} := by
    ext γ'
    simp only [Set.mem_setOf_eq, Set.MapsTo, K_i, Set.mem_Icc]
    refine forall_congr' fun s ↦ ?_
    constructor
    · intro h hs; exact h hs
    · intro h hs; exact h hs
  rw [h_eq]
  -- BRITTLE (intentional): `Set.MapsTo γ' K_i (U i)` for a `Path` unfolds its application through
  -- the `Path → C(I, X)` coercion, so the path-set is *definitionally* the coercion-preimage of the
  -- continuous-map-set. If `Path`'s coercion is ever restated, replace this `rfl`.
  have hpre : {γ' : Path x y | Set.MapsTo γ' K_i (U i)} =
      (↑) ⁻¹' {f : C(unitInterval, X) | Set.MapsTo f K_i (U i)} := rfl
  rw [hpre]
  exact (ContinuousMap.isOpen_setOf_mapsTo h_compact_K (hU_open i)).preimage
    continuous_induced_dom

/-- The set of paths sending each partition vertex `part.t j` into the corresponding set `V j` is
open, provided every `V j` is open: it is a finite intersection of preimages of the `V j` under the
(continuous) evaluation maps. -/
private theorem isOpen_setOf_forall_vertex_mem {x y : X} {n : ℕ}
    (part : IntervalPartition n) (V : Fin (n + 1) → Set X) (hV_open : ∀ j, IsOpen (V j)) :
    IsOpen {γ' : Path x y | ∀ j, γ' (part.t j) ∈ V j} := by
  have hrw : {γ' : Path x y | ∀ j, γ' (part.t j) ∈ V j} =
      ⋂ j : Fin (n + 1), {γ' : Path x y | γ' (part.t j) ∈ V j} := by
    ext γ'
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [hrw]
  apply isOpen_iInter_of_finite
  intro j
  exact (hV_open j).preimage <|
    (continuous_eval_const (part.t j)).comp continuous_induced_dom

/-- Given open segment and vertex families, the corresponding raw tube set is open in the path
space. This compact-open statement only uses openness of the two families, not the full SLSC tube
data carried by `TubeData`. -/
theorem isOpen_pathTube {x y : X} {n : ℕ}
    (part : IntervalPartition n) (U : Fin n → Set X) (V : Fin (n + 1) → Set X)
    (hU_open : ∀ i, IsOpen (U i)) (hV_open : ∀ j, IsOpen (V j)) :
    IsOpen {γ' : Path x y |
      (∀ i (s : unitInterval),
        (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → γ' s ∈ U i) ∧
      ∀ j, γ' (part.t j) ∈ V j} := by
  rw [Set.setOf_and]
  exact (isOpen_setOf_forall_segment_mapsTo part U hU_open).inter
    (isOpen_setOf_forall_vertex_mem part V hV_open)

/-- Given a partition and tube data, the set of paths in the tube is open in the path space. -/
theorem TubeData.isOpen {x y : X} {n : ℕ}
    (part : IntervalPartition n) (T : TubeData X n) :
    IsOpen (T.toSet (x := x) (y := y) part) := by
  have : T.toSet (x := x) (y := y) part =
      {γ' : Path x y |
        (∀ i (s : unitInterval),
          (part.t i.castSucc : ℝ) ≤ s ∧ s ≤ (part.t i.succ : ℝ) → γ' s ∈ T.U i) ∧
        ∀ j, γ' (part.t j) ∈ T.V j} := by
    ext γ'
    simp only [TubeData.mem_toSet_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      exact ⟨h.stays_in_U, h.passes_through_V⟩
    · intro ⟨h1, h2⟩
      exact ⟨h1, h2⟩
  rw [this]
  exact isOpen_pathTube part T.U T.V T.U_open T.V_open

/-! ### Construction of "rung" paths for the ladder homotopy -/

/-- Given two paths `γ` and `γ'` in a tube, construct connecting rung paths at every partition
point. Each rung lies in its vertex neighborhood `V j`; for every segment `i`, the left and
right boundary rungs lie in the segment neighborhood `U i`, so only interior rungs are required
to lie in both adjacent segment neighborhoods. -/
theorem Path.exists_rung_paths {x y y' : X} {n : ℕ} (γ : Path x y) (γ' : Path x y')
    (part : IntervalPartition n) (T : TubeData X n)
    (hγ : PathInTube γ part T) (hγ' : PathInTube γ' part T) :
    ∃ α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i)),
      (∀ j, Set.range (α j) ⊆ T.V j) ∧
      (∀ (i : Fin n), Set.range (α i.castSucc) ⊆ T.U i ∧ Set.range (α i.succ) ⊆ T.U i) := by
  -- For each point j, construct a rung path α_j from γ(t_j) to γ'(t_j)
  -- using the path-connected neighborhood V[j]
  have rung_exists : ∀ j, ∃ α_j : Path (γ (part.t j)) (γ' (part.t j)),
      Set.range α_j ⊆ T.V j := fun j ↦
    let h := (T.V_pathConn j).joinedIn _ (hγ.passes_through_V j) _
      (hγ'.passes_through_V j)
    ⟨h.somePath, Set.range_subset_iff.mpr h.somePath_mem⟩
  choose α hα_range using rung_exists
  -- Prove the range conditions using the subset properties
  refine ⟨α, hα_range, fun i ↦ ?_⟩
  constructor
  · calc Set.range (α i.castSucc) ⊆ T.V i.castSucc := hα_range i.castSucc
      _ ⊆ T.U i := T.V_left_subset i
  · calc Set.range (α i.succ) ⊆ T.V i.succ := hα_range i.succ
      _ ⊆ T.U i := T.V_right_subset i

/-! ### Single segment homotopy: the key step in the ladder construction -/

/-- For a single segment in a path-homotopy-trivial set `U`, the path `γ.trans α_end` is
homotopic to `α_start.trans γ'` when all four paths have range in `U`. -/
theorem Path.segment_rung_homotopy {a b c d : X} (U : Set X)
    (hU : IsPathHomotopyTrivial U)
    (γ : Path a b) (γ' : Path c d) (α_start : Path a c) (α_end : Path b d)
    (hγ : Set.range γ ⊆ U) (hγ' : Set.range γ' ⊆ U)
    (hα_start : Set.range α_start ⊆ U) (hα_end : Set.range α_end ⊆ U) :
    Path.Homotopic (γ.trans α_end) (α_start.trans γ') := by
  apply hU.apply
  · rw [Path.trans_range]; exact Set.union_subset hγ hα_end
  · rw [Path.trans_range]; exact Set.union_subset hα_start hγ'

/-! ### Pasting lemma: telescoping cancellation of rungs -/

/-- The cast'd quotient class of `p.subpath` over the endpoints of an `IntervalPartition`
equals the class of `p` itself. This packages `Path.Homotopic.Quotient.subpath_zero_one`
together with `part.t_zero` / `part.t_last`, sidestepping the dependent-type "motive"
obstruction one hits when rewriting `part.t 0 = 0` / `part.t (Fin.last n) = 1` directly
through `subpath`. -/
theorem Path.Homotopic.Quotient.cast_mk_subpath_part_endpoints
    {x y : X} (p : Path x y) {n : ℕ} (part : IntervalPartition n)
    (h₁ : x = p (part.t 0)) (h₂ : y = p (part.t (Fin.last n))) :
    (Path.Homotopic.Quotient.mk (p.subpath (part.t 0) (part.t (Fin.last n)))).cast h₁ h₂ =
      Path.Homotopic.Quotient.mk p := by
  convert congrArg (fun q ↦ q.cast p.source.symm p.target.symm)
    (Path.Homotopic.Quotient.subpath_zero_one p)
  · simp [part.t_zero]
  · simp [part.t_last]
  · simp

/-- The first partition point is the source of a path. This names the endpoint cast used when
turning the first rung into an honest loop at the source. -/
theorem Path.source_eq_eval_partition_zero {x y : X} (p : Path x y)
    {n : ℕ} (part : IntervalPartition n) : x = p (part.t 0) := by
  rw [part.t_zero, p.source]

/-- The last partition point is the target of a path. This names the endpoint cast used when
turning the final rung into an honest path between the targets. -/
theorem Path.target_eq_eval_partition_last {x y : X} (p : Path x y)
    {n : ℕ} (part : IntervalPartition n) : y = p (part.t (Fin.last n)) := by
  rw [part.t_last, p.target]

/-- The `i`-th intermediate path of the telescoping ladder from `γ.trans αₙ` to `α₀.trans γ'`:
follow `γ` up to the partition point `t i`, cross to `γ'` along the rung `α i`, then follow `γ'`
to the end. The endpoints are cast back to `x` and `y'` using `t 0 = 0` and `t (last n) = 1`. -/
private def Path.pasteSegmentAuxPath {x y y' : X} {n : ℕ}
    (γ : Path x y) (γ' : Path x y') (part : IntervalPartition n)
    (α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i))) (i : Fin (n + 1)) :
    Path x y' :=
  (((γ.subpath (part.t 0) (part.t i)).trans (α i)).trans
    (γ'.subpath (part.t i) (part.t (Fin.last n)))).cast
    (by rw [part.t_zero, γ.source])
    (by rw [part.t_last, γ'.target])

/-- At the first partition point the `γ`-prefix is constant and the `γ'`-suffix is all of `γ'`, so
the intermediate path reduces to the first rung `α 0` followed by `γ'`. -/
private lemma Path.pasteSegmentAuxPath_zero_homotopic {x y y' : X} {n : ℕ}
    (γ : Path x y) (γ' : Path x y') (part : IntervalPartition n)
    (α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i))) :
    Path.Homotopic (Path.pasteSegmentAuxPath γ γ' part α 0)
      (((α 0).cast (Path.source_eq_eval_partition_zero γ part)
                   (Path.source_eq_eval_partition_zero γ' part)).trans γ') := by
  apply Path.Homotopic.Quotient.exact
  dsimp [Path.pasteSegmentAuxPath]
  rw [Path.Homotopic.Quotient.subpath_self,
      Path.Homotopic.Quotient.cast_mk_subpath_part_endpoints γ' part]
  simp

/-- At the last partition point the `γ`-prefix is all of `γ` and the `γ'`-suffix is constant, so
the intermediate path reduces to `γ` followed by the final rung `α (last n)`. -/
private lemma Path.pasteSegmentAuxPath_last_homotopic {x y y' : X} {n : ℕ}
    (γ : Path x y) (γ' : Path x y') (part : IntervalPartition n)
    (α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i))) :
    Path.Homotopic (Path.pasteSegmentAuxPath γ γ' part α (Fin.last n))
      (γ.trans ((α (Fin.last n)).cast
        (Path.target_eq_eval_partition_last γ part)
        (Path.target_eq_eval_partition_last γ' part))) := by
  apply Path.Homotopic.Quotient.exact
  dsimp [Path.pasteSegmentAuxPath]
  rw [Path.Homotopic.Quotient.subpath_self,
      Path.Homotopic.Quotient.cast_mk_subpath_part_endpoints γ part]
  simp

open Path.Homotopic.Quotient in
/-- Consecutive intermediate paths are homotopic: passing from segment `i` to segment `i+1` swaps
a single rung across one rectangle, and the rectangle homotopy `h_rectangles i` cancels it. -/
private lemma Path.pasteSegmentAuxPath_succ_homotopic {x y y' : X} {n : ℕ}
    (γ : Path x y) (γ' : Path x y') (part : IntervalPartition n)
    (α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i)))
    (i : Fin n)
    (h_rectangle : Path.Homotopic
        ((γ.subpath (part.t i.castSucc) (part.t i.succ)).trans (α i.succ))
        ((α i.castSucc).trans (γ'.subpath (part.t i.castSucc) (part.t i.succ)))) :
    Path.Homotopic (Path.pasteSegmentAuxPath γ γ' part α i.succ)
      (Path.pasteSegmentAuxPath γ γ' part α i.castSucc) := by
  apply exact
  simp only [Path.pasteSegmentAuxPath, mk_trans, mk_cast]
  -- Decompose γ|[0, i+1] = γ|[0, i] · γ|[i, i+1] and γ'|[i, last] = γ'|[i, i+1] · γ'|[i+1, last].
  rw [← Path.Homotopic.Quotient.subpath_trans γ
    (part.t 0) (part.t i.castSucc) (part.t i.succ)]
  rw [← Path.Homotopic.Quotient.subpath_trans γ'
    (part.t i.castSucc) (part.t i.succ) (part.t (Fin.last n))]
  -- Right-associate everything so the rectangle rewrite fires on the shared suffix.
  simp only [trans_assoc]
  -- Turn the rectangle homotopy into an equality of quotient composites, then cancel the suffix.
  have h_eq :
      (Path.Homotopic.Quotient.mk (γ.subpath (part.t i.castSucc) (part.t i.succ))).trans
          (Path.Homotopic.Quotient.mk (α i.succ)) =
        (Path.Homotopic.Quotient.mk (α i.castSucc)).trans
          (Path.Homotopic.Quotient.mk (γ'.subpath (part.t i.castSucc) (part.t i.succ))) := by
    rw [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_trans]
    exact Path.Homotopic.Quotient.eq.mpr h_rectangle
  -- Reassociate the inner rung pair so `γ|[i, i+1] · α_{i+1}` surfaces as a subterm, rewrite it to
  -- `α_i · γ'|[i, i+1]` via `h_eq`, then restore right-association. The shared prefix `γ|[0, i]`
  -- and the outer endpoint `cast` are carried along untouched.
  rw [← Path.Homotopic.Quotient.trans_assoc
        (Path.Homotopic.Quotient.mk (γ.subpath (part.t i.castSucc) (part.t i.succ))),
      h_eq,
      Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk (α i.castSucc))]

/-- The pasting lemma for segment homotopies. Works directly with path restrictions.

Given:
- γ is a path from x to y and γ' is a path from x to y' with a partition
- α : (i : Fin (n+1)) → Path (γ (t i)) (γ' (t i)) are rung paths connecting partition points
- For each segment i, the rectangle homotopy: γ|[t_i,t_{i+1}] · α_{i+1} ≃ α_i · γ'|[t_i,t_{i+1}]

Then by telescoping, we get: γ · αₙ ≃ α₀ · γ'

Since part.t 0 = 0 and part.t (Fin.last n) = 1:
- α₀ : Path (γ 0) (γ' 0) = Path x x (loop at x)
- αₙ : Path (γ 1) (γ' 1) = Path y y'

When the initial loop is null-homotopic, this identifies `γ'` with `γ` followed by the final
rung. If the final rung is also null-homotopic, we recover γ ≃ γ'. -/
theorem Path.paste_segment_homotopies {x y y' : X} {n : ℕ}
    (γ : Path x y) (γ' : Path x y') (part : IntervalPartition n)
    (α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i)))
    (h_rectangles : ∀ (i : Fin n),
        Path.Homotopic
          ((γ.subpath (part.t i.castSucc) (part.t i.succ)).trans (α i.succ))
          ((α i.castSucc).trans (γ'.subpath (part.t i.castSucc) (part.t i.succ)))) :
    Path.Homotopic
      (γ.trans ((α (Fin.last n)).cast
        (Path.target_eq_eval_partition_last γ part)
        (Path.target_eq_eval_partition_last γ' part)))
      (((α 0).cast (Path.source_eq_eval_partition_zero γ part)
                   (Path.source_eq_eval_partition_zero γ' part)).trans γ') := by
  -- Telescope the intermediate paths `pasteSegmentAuxPath … i` from `i = last n` down to `i = 0`.
  have h_chain : ∀ i : Fin (n + 1),
      Path.Homotopic (Path.pasteSegmentAuxPath γ γ' part α i)
        (Path.pasteSegmentAuxPath γ γ' part α 0) := by
    intro i
    induction i using Fin.induction with
    | zero => exact Path.Homotopic.refl _
    | succ i ih =>
      exact (Path.pasteSegmentAuxPath_succ_homotopic γ γ' part α i (h_rectangles i)).trans ih
  -- γ · αₙ ≃ aux (last n) ≃ aux 0 ≃ α₀ · γ'.
  exact (Path.pasteSegmentAuxPath_last_homotopic γ γ' part α).symm.trans
    ((h_chain (Fin.last n)).trans (Path.pasteSegmentAuxPath_zero_homotopic γ γ' part α))

/-- A loop whose range lies in a path-homotopy-trivial set is null-homotopic. -/
theorem Path.nullhomotopic_of_range_subset_pathHomotopyTrivial {x : X} (γ : Path x x)
    (U : Set X) (hU : IsPathHomotopyTrivial U)
    (hγU : Set.range γ ⊆ U) :
    Path.Homotopic γ (Path.refl x) :=
  hU.apply γ (Path.refl x) hγU <| by
    rintro _ ⟨_, rfl⟩
    simpa [γ.source] using hγU ⟨0, rfl⟩

private theorem Path.first_rung_nullhomotopic_of_range_subset_pathHomotopyTrivial
    {x y y' : X} {n : ℕ}
    (γ : Path x y) (γ' : Path x y')
    (part : IntervalPartition n)
    (α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i)))
    (U₀ : Set X) (hU₀ : IsPathHomotopyTrivial U₀)
    (h_α₀_in_U₀ : Set.range (α 0) ⊆ U₀) :
    let α₀ := (α 0).cast (Path.source_eq_eval_partition_zero γ part)
      (Path.source_eq_eval_partition_zero γ' part)
    Path.Homotopic α₀ (Path.refl x) := by
  intro α₀
  apply Path.nullhomotopic_of_range_subset_pathHomotopyTrivial α₀ U₀ hU₀
  simpa only [α₀, Path.cast_coe] using h_α₀_in_U₀

private theorem Path.last_rung_nullhomotopic_of_range_subset_pathHomotopyTrivial
    {x y : X} {n : ℕ}
    (γ γ' : Path x y) (part : IntervalPartition n)
    (α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i)))
    (Uₙ : Set X) (hUₙ : IsPathHomotopyTrivial Uₙ)
    (h_αₙ_in_Uₙ : Set.range (α (Fin.last n)) ⊆ Uₙ) :
    let αₙ := (α (Fin.last n)).cast
      (Path.target_eq_eval_partition_last γ part)
      (Path.target_eq_eval_partition_last γ' part)
    Path.Homotopic αₙ (Path.refl y) := by
  intro αₙ
  apply Path.nullhomotopic_of_range_subset_pathHomotopyTrivial αₙ Uₙ hUₙ
  simpa only [αₙ, Path.cast_coe] using h_αₙ_in_Uₙ

/-- One-sided specialization of `paste_segment_homotopies` that kills the source loop when the
first rung has range in a path-homotopy-trivial set. Then `γ'` is homotopic to `γ` followed by
the final rung. -/
theorem Path.paste_segment_homotopies_pathHomotopyTrivial_source {x y y' : X} {n : ℕ}
    (γ : Path x y) (γ' : Path x y')
    (part : IntervalPartition n)
    (α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i)))
    (h_rectangles : ∀ (i : Fin n),
        Path.Homotopic
          ((γ.subpath (part.t i.castSucc) (part.t i.succ)).trans (α i.succ))
          ((α i.castSucc).trans (γ'.subpath (part.t i.castSucc) (part.t i.succ))))
    (U₀ : Set X) (hU₀ : IsPathHomotopyTrivial U₀)
    (h_α₀_in_U₀ : Set.range (α 0) ⊆ U₀) :
    Path.Homotopic
      (γ.trans ((α (Fin.last n)).cast
        (Path.target_eq_eval_partition_last γ part)
        (Path.target_eq_eval_partition_last γ' part)))
      γ' := by
  have h_paste := paste_segment_homotopies γ γ' part α h_rectangles
  let α₀ := (α 0).cast (Path.source_eq_eval_partition_zero γ part)
                       (Path.source_eq_eval_partition_zero γ' part)
  have h_α₀_null : Path.Homotopic α₀ (Path.refl x) := by
    simpa [α₀] using
      Path.first_rung_nullhomotopic_of_range_subset_pathHomotopyTrivial γ γ' part α
        U₀ hU₀ h_α₀_in_U₀
  exact h_paste.trans <| Path.Homotopic.trans_left_of_nullhomotopic h_α₀_null

/-- Variable-endpoint tube theorem: paths in the same tube as `γ` are homotopic to `γ`
followed by the final endpoint rung.

`public` because `TauCeti.AlgebraicTopology.UniversalCover.BasedPath` uses exactly this
variable-endpoint statement to move between based paths with distinct endpoints inside a common
path component of `endpoint ⁻¹' U`; the fixed-endpoint public API does not suffice there. -/
public theorem Path.tube_subset_homotopy_class_source {x y y' : X} {n : ℕ}
    (γ : Path x y) (part : IntervalPartition n) (T : TubeData X n)
    (hγ : PathInTube γ part T)
    (γ' : Path x y') (hγ' : PathInTube γ' part T) :
    ∃ ρ : Path y y', Set.range ρ ⊆ T.V (Fin.last n) ∧ Path.Homotopic (γ.trans ρ) γ' := by
  cases n with
  | zero => exact isEmptyElim part
  | succ n' =>
    obtain ⟨α, hα_V_ranges, hα_ranges⟩ := Path.exists_rung_paths γ γ' part T hγ hγ'
    have h_rectangles : ∀ (i : Fin (n' + 1)),
        Path.Homotopic
          ((γ.subpath (part.t i.castSucc) (part.t i.succ)).trans (α i.succ))
          ((α i.castSucc).trans (γ'.subpath (part.t i.castSucc) (part.t i.succ))) := by
      intro i
      apply segment_rung_homotopy (T.U i) (T.U_slsc i)
      · exact hγ.subpath_range_subset i
      · exact hγ'.subpath_range_subset i
      · exact (hα_ranges i).1
      · exact (hα_ranges i).2
    let ρ : Path y y' := (α (Fin.last (n' + 1))).cast
      (Path.target_eq_eval_partition_last γ part)
      (Path.target_eq_eval_partition_last γ' part)
    refine ⟨ρ, ?_, ?_⟩
    · simpa only [ρ, Path.cast_coe] using hα_V_ranges (Fin.last (n' + 1))
    · simpa only [ρ] using
        paste_segment_homotopies_pathHomotopyTrivial_source γ γ' part α h_rectangles
          (T.U ⟨0, Nat.succ_pos n'⟩) (T.U_slsc ⟨0, Nat.succ_pos n'⟩)
          (hα_ranges ⟨0, Nat.succ_pos n'⟩).1

/-- Two-sided specialization of `paste_segment_homotopies` killing both endpoint loops. -/
theorem Path.paste_segment_homotopies_pathHomotopyTrivial {x y : X} {n : ℕ} (γ γ' : Path x y)
    (part : IntervalPartition n)
    (α : (i : Fin (n + 1)) → Path (γ (part.t i)) (γ' (part.t i)))
    (h_rectangles : ∀ (i : Fin n),
        Path.Homotopic
          ((γ.subpath (part.t i.castSucc) (part.t i.succ)).trans (α i.succ))
          ((α i.castSucc).trans (γ'.subpath (part.t i.castSucc) (part.t i.succ))))
    (U₀ : Set X) (hU₀ : IsPathHomotopyTrivial U₀)
    (h_α₀_in_U₀ : Set.range (α 0) ⊆ U₀)
    (Uₙ : Set X) (hUₙ : IsPathHomotopyTrivial Uₙ)
    (h_αₙ_in_Uₙ : Set.range (α (Fin.last n)) ⊆ Uₙ) :
    Path.Homotopic γ γ' := by
  let αₙ := (α (Fin.last n)).cast
              (Path.target_eq_eval_partition_last γ part)
              (Path.target_eq_eval_partition_last γ' part)
  have h_source : Path.Homotopic (γ.trans αₙ) γ' := by
    simpa only [αₙ] using
      paste_segment_homotopies_pathHomotopyTrivial_source γ γ' part α h_rectangles U₀ hU₀ h_α₀_in_U₀
  have h_αₙ_null : Path.Homotopic αₙ (Path.refl y) := by
    simpa [αₙ] using
      Path.last_rung_nullhomotopic_of_range_subset_pathHomotopyTrivial γ γ' part α Uₙ hUₙ h_αₙ_in_Uₙ
  exact (Path.Homotopic.trans_right_of_nullhomotopic h_αₙ_null).symm.trans h_source

/-- Any fixed-endpoint path in the same tube as `γ` is homotopic to `γ`. -/
theorem Path.tube_subset_homotopy_class {x y : X} {n : ℕ}
    (γ : Path x y) (part : IntervalPartition n) (T : TubeData X n)
    (hγ : PathInTube γ part T)
    (γ' : Path x y) (hγ' : PathInTube γ' part T) :
    Path.Homotopic γ' γ := by
  cases n with
  | zero => exact isEmptyElim part
  | succ n' =>
    let i_last : Fin (n' + 1) := ⟨n', Nat.lt_succ_self n'⟩
    obtain ⟨ρ, hρ_V, hρ⟩ := Path.tube_subset_homotopy_class_source γ part T hγ γ' hγ'
    have hρ_null : Path.Homotopic ρ (Path.refl y) := by
      apply Path.nullhomotopic_of_range_subset_pathHomotopyTrivial ρ (T.U i_last) (T.U_slsc i_last)
      exact hρ_V.trans (T.V_right_subset i_last)
    have hdrop : Path.Homotopic (γ.trans ρ) γ :=
      Path.Homotopic.trans_right_of_nullhomotopic (γ₀ := γ) hρ_null
    exact hρ.symm.trans hdrop

/-- If semilocal simple connectivity holds along `p` in a locally path-connected space, then
`p` has an open neighborhood in the path space contained in its homotopy class. -/
public theorem Path.exists_isOpen_mem_subset_setOf_homotopic
    [LocallyPathConnectedSpace X] {x y : X} (p : Path x y)
    (hslsc : SemilocallySimplyConnectedOn (Set.range p)) :
    ∃ (T : Set (Path x y)), IsOpen T ∧ p ∈ T ∧ T ⊆ {p' | Path.Homotopic p' p} := by
  -- Step 1: Get partition and SLSC neighborhoods
  obtain ⟨n, part, T_data, hp_in_tube⟩ :=
    p.exists_pathHomotopyTrivial_tube hslsc
  refine ⟨T_data.toSet part, ?_, ?_, ?_⟩
  · -- Show `T` is open.
    exact T_data.isOpen part
  · -- Show p ∈ T
    exact hp_in_tube
  · -- Show T ⊆ {p' | Homotopic p' p} using tube_subset_homotopy_class
    intro p' hp'
    apply Path.tube_subset_homotopy_class p part T_data
    · exact hp_in_tube
    · exact hp'

/-- If semilocal simple connectivity holds along every representative of the homotopy class of
`p`, then that homotopy class is open in the path space. -/
public theorem Path.isOpen_setOf_homotopic_of_semilocallySimplyConnectedOn
    [LocallyPathConnectedSpace X] {x y : X} (p : Path x y)
    (hslsc : ∀ q : Path x y, Path.Homotopic q p →
      SemilocallySimplyConnectedOn (Set.range q)) :
    IsOpen {p' : Path x y | Path.Homotopic p' p} := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  obtain ⟨T, hT_open, hqT, hT_subset⟩ :=
    exists_isOpen_mem_subset_setOf_homotopic q (hslsc q hq)
  rw [mem_nhds_iff]
  refine ⟨T, fun p' hp' ↦ (hT_subset hp').trans hq, hT_open, hqT⟩

/-- In an SLSC locally path-connected space, for any path `p`, the set of paths homotopic to `p`
is open. -/
public theorem Path.isOpen_setOf_homotopic [SemilocallySimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] {x y : X} (p : Path x y) :
    IsOpen {p' : Path x y | Path.Homotopic p' p} :=
  p.isOpen_setOf_homotopic_of_semilocallySimplyConnectedOn
    fun q _ ↦ SemilocallySimplyConnectedOn.of_semilocallySimplyConnectedSpace (Set.range q)

/-- If semilocal simple connectivity holds along every fixed-endpoint path, the
fixed-endpoint path-homotopy quotient is discrete. -/
public theorem Path.Homotopic.Quotient.discreteTopology_of_semilocallySimplyConnectedOn
    [LocallyPathConnectedSpace X] {x y : X}
    (hslsc : ∀ p : Path x y, SemilocallySimplyConnectedOn (Set.range p)) :
    DiscreteTopology (Path.Homotopic.Quotient x y) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro a
  induction a using Quotient.inductionOn with
  | h p =>
    rw [Path.Homotopic.Quotient.isOpen_iff_preimage_mk]
    convert p.isOpen_setOf_homotopic_of_semilocallySimplyConnectedOn
      (fun q _ ↦ hslsc q) using 1
    ext p'
    exact Path.Homotopic.Quotient.eq

/--
In a semilocally simply connected, locally path-connected space, the quotient of paths by
homotopy has discrete topology.
-/
public instance Path.Homotopic.Quotient.instDiscreteTopology
    [SemilocallySimplyConnectedSpace X] [LocallyPathConnectedSpace X] {x y : X} :
    DiscreteTopology (Path.Homotopic.Quotient x y) :=
  Path.Homotopic.Quotient.discreteTopology_of_semilocallySimplyConnectedOn
    fun p ↦ SemilocallySimplyConnectedOn.of_semilocallySimplyConnectedSpace (Set.range p)

end
