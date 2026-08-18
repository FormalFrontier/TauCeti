/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Length spaces and geodesic spaces

A metric space is a *length space* when the distance between two points is the infimum of the
lengths of the continuous curves joining them, and a *geodesic space* when that infimum is
realised by a curve on `[0, 1]` whose distance function is the affine one, `dist (γ s) (γ t) =
|s - t| * dist x y`. This file sets up both notions, together with the length of a curve that
they are phrased in terms of, and proves that a geodesic space is a length space.

## The length of a curve

The length of a curve `γ : ℝ → X` over a parameter interval `[a, b]` is the supremum of the sums
`∑ i, edist (γ (u (i + 1))) (γ (u i))` over finite increasing families `u` in `[a, b]`, which is
exactly Mathlib's total variation `eVariationOn γ (Set.Icc a b)`. `TauCeti.curveELength` names
that specialisation. Two conventions are inherited deliberately:

* curves are functions on all of `ℝ`, read on a parameter interval, rather than functions on a
  subtype. This is the convention of `Manifold.pathELength I γ a b`, the Riemannian length that
  `curveELength` is to be compared against, and it avoids subtype juggling in the API;
* the value is an extended nonnegative real, since a continuous curve can have infinite length.

Mathlib's bundled `Path x y` is bridged to this convention in both directions, by
`TauCeti.IsCurveJoining.joined` and `TauCeti.isCurveJoining_extend`.

## Continuity is load-bearing

The infimum defining a length space must range over *continuous* curves. Dropping continuity makes
every metric space a length space: the two-valued curve which is `x` on `[0, 1)` and `y` at `1`
already has length `edist x y`, by `TauCeti.edist_le_curveELength`.

## Main definitions

* `TauCeti.curveELength γ a b` — the length of the curve `γ` on the parameter interval `[a, b]`.
* `TauCeti.IsCurveJoining γ x y` — `γ` is continuous on `[0, 1]` and runs from `x` to `y` there.
* `TauCeti.IsGeodesicSegment γ x y` — `γ` parametrises a shortest curve from `x` to `y`
  proportionally to arclength on `[0, 1]`.
* `TauCeti.IsLengthSpace X` — the distance is the infimum of the lengths of the joining curves.
* `TauCeti.IsGeodesicSpace X` — any two points are joined by a geodesic segment.

## Main results

* `TauCeti.curveELength_comp_affine` and `TauCeti.exists_isCurveJoining_of_continuousOn` — the
  parameter interval `[0, 1]` is no loss of generality.
* `TauCeti.IsGeodesicSegment.curveELength_eq_edist` — a geodesic segment realises the distance
  between any two of its points, and in particular between its endpoints.
* `TauCeti.IsGeodesicSpace.toIsLengthSpace` — a geodesic space is a length space; there the
  infimum is attained, by `TauCeti.IsGeodesicSpace.exists_curveELength_eq`.
* `TauCeti.IsLengthSpace.pathConnectedSpace` — a nonempty length space with finite distances is
  path connected.
* `TauCeti.instIsGeodesicSpace` — a real seminormed space is a geodesic space, its geodesic
  segments being the affine ones (`TauCeti.isGeodesicSegment_lineMap`).

This is the metric half of the length-space and geodesic-space layer of
`TauCetiRoadmap/HopfRinow/README.md`; the Riemannian half, that a complete connected Riemannian
manifold is a geodesic space, needs the minimising geodesics of that roadmap's Layer 3.
-/

public section

namespace TauCeti

open Set

open scoped ENNReal

/-! ### The length of a curve -/

section CurveELength

variable {X : Type*} [PseudoEMetricSpace X]

/-- The length of the curve `γ : ℝ → X` on the parameter interval `[a, b]`: the supremum of the
sums `∑ i, edist (γ (u (i + 1))) (γ (u i))` over finite increasing families `u` in `[a, b]`.

This is the total variation `eVariationOn γ (Set.Icc a b)`, packaged with the argument shape of
`Manifold.pathELength I γ a b` so that the two lengths can be compared. It vanishes when
`b ≤ a`. -/
noncomputable def curveELength (γ : ℝ → X) (a b : ℝ) : ℝ≥0∞ :=
  eVariationOn γ (Icc a b)

theorem curveELength_eq_eVariationOn (γ : ℝ → X) (a b : ℝ) :
    curveELength γ a b = eVariationOn γ (Icc a b) :=
  (rfl)

-- The equation above is the elimination API of `curveELength`: the body is not `@[expose]`d, so
-- no other module unfolds it. The parentheses in `(rfl)` are the module system's -- a bare `rfl`,
-- whose proof term is exported, fails with "not a definitional equality", while the parenthesised
-- form elaborates inside this module, where the body is visible.

theorem curveELength_eq_zero_of_le (γ : ℝ → X) {a b : ℝ} (hba : b ≤ a) :
    curveELength γ a b = 0 :=
  eVariationOn.subsingleton γ (subsingleton_Icc_of_ge hba)

@[simp]
theorem curveELength_self (γ : ℝ → X) (a : ℝ) : curveELength γ a a = 0 :=
  curveELength_eq_zero_of_le γ le_rfl

theorem curveELength_congr {γ γ' : ℝ → X} {a b : ℝ} (h : EqOn γ γ' (Icc a b)) :
    curveELength γ a b = curveELength γ' a b :=
  eVariationOn.congr h

@[simp]
theorem curveELength_const (x : X) (a b : ℝ) : curveELength (fun _ : ℝ => x) a b = 0 := by
  refine eVariationOn.constant_on ?_
  rintro _ ⟨s, -, rfl⟩ _ ⟨t, -, rfl⟩
  rfl

/-- Any two points of a curve are at most its length apart. -/
theorem edist_le_curveELength (γ : ℝ → X) {a b s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    edist (γ s) (γ t) ≤ curveELength γ a b :=
  eVariationOn.edist_le γ hs ht

theorem curveELength_mono (γ : ℝ → X) {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    curveELength γ a b ≤ curveELength γ c d :=
  eVariationOn.mono γ (Icc_subset_Icc hca hbd)

/-- Length is additive along a subdivision of the parameter interval. -/
theorem curveELength_add (γ : ℝ → X) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    curveELength γ a b + curveELength γ b c = curveELength γ a c := by
  simpa only [curveELength_eq_eVariationOn, univ_inter] using
    eVariationOn.Icc_add_Icc γ (s := univ) hab hbc (mem_univ b)

/-- Length is invariant under a monotone reparametrisation of the parameter interval. -/
theorem curveELength_comp_of_monotoneOn (γ : ℝ → X) {φ : ℝ → ℝ} {a b c d : ℝ}
    (hφ : MonotoneOn φ (Icc a b)) (himg : φ '' Icc a b = Icc c d) :
    curveELength (γ ∘ φ) a b = curveELength γ c d := by
  rw [curveELength_eq_eVariationOn, curveELength_eq_eVariationOn,
    eVariationOn.comp_eq_of_monotoneOn γ φ hφ, himg]

/-- Every parameter interval can be rescaled affinely to `[0, 1]` without changing the length of
the curve read on it. This is what makes the choice of `[0, 1]` in `TauCeti.IsCurveJoining` and
`TauCeti.IsGeodesicSegment` no loss of generality. -/
theorem curveELength_comp_affine (γ : ℝ → X) {a b : ℝ} (hab : a ≤ b) :
    curveELength (fun t => γ ((b - a) * t + a)) 0 1 = curveELength γ a b := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  · have hpos : (0 : ℝ) < b - a := sub_pos.2 hlt
    have hmono : MonotoneOn (fun t : ℝ => (b - a) * t + a) (Icc 0 1) :=
      fun _ _ _ _ hst => by nlinarith
    refine curveELength_comp_of_monotoneOn γ hmono ?_
    simpa using Set.image_affine_Icc' hpos a 0 1

end CurveELength

/-! ### Curves joining two points -/

section IsCurveJoining

variable {X : Type*} [PseudoEMetricSpace X] {γ : ℝ → X} {x y : X}

/-- `IsCurveJoining γ x y` says that the curve `γ`, read on the parameter interval `[0, 1]`, is
continuous and runs from `x` to `y`. -/
structure IsCurveJoining (γ : ℝ → X) (x y : X) : Prop where
  /-- A joining curve is continuous on its parameter interval. -/
  continuousOn : ContinuousOn γ (Icc 0 1)
  /-- A joining curve starts at `x`. -/
  source : γ 0 = x
  /-- A joining curve ends at `y`. -/
  target : γ 1 = y

/-- A joining curve is at least as long as the distance between the points it joins. -/
theorem IsCurveJoining.edist_le (h : IsCurveJoining γ x y) :
    edist x y ≤ curveELength γ 0 1 := by
  simpa only [h.source, h.target] using
    edist_le_curveELength γ (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)

/-- The extension to `ℝ` of a bundled path is a joining curve. -/
theorem isCurveJoining_extend (γ : Path x y) : IsCurveJoining γ.extend x y where
  continuousOn := γ.continuous_extend.continuousOn
  source := γ.extend_zero
  target := γ.extend_one

/-- A continuous curve joining `x` to `y` on an arbitrary parameter interval can be renormalised
to `[0, 1]` without changing its length. This is how curves produced on other parameter intervals
enter the length-space condition below. -/
theorem exists_isCurveJoining_of_continuousOn {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (ha : γ a = x) (hb : γ b = y) :
    ∃ γ' : ℝ → X, IsCurveJoining γ' x y ∧ curveELength γ' 0 1 = curveELength γ a b := by
  have hmaps : MapsTo (fun t : ℝ => (b - a) * t + a) (Icc 0 1) (Icc a b) := by
    rintro t ⟨ht0, ht1⟩
    constructor <;> nlinarith
  refine ⟨fun t => γ ((b - a) * t + a), ⟨?_, ?_, ?_⟩, curveELength_comp_affine γ hab⟩
  · exact hγ.comp (by fun_prop) hmaps
  · simpa using ha
  · simpa using hb

/-- A joining curve restricts to a bundled path, so it witnesses `Joined`. -/
theorem IsCurveJoining.joined (h : IsCurveJoining γ x y) : Joined x y :=
  ⟨{ toFun := (Icc (0 : ℝ) 1).domRestrict γ
     continuous_toFun := h.continuousOn.domRestrict
     source' := h.source
     target' := h.target }⟩

end IsCurveJoining

/-! ### Length spaces -/

section IsLengthSpace

variable {X : Type*} [PseudoEMetricSpace X] {γ : ℝ → X} {x y : X}

/-- A *length space* is a space in which the distance between two points is the infimum of the
lengths of the continuous curves joining them. -/
class IsLengthSpace (X : Type*) [PseudoEMetricSpace X] : Prop where
  /-- The distance between two points is the infimum of the lengths of the curves joining them. -/
  edist_eq_iInf (x y : X) :
    edist x y = ⨅ (γ : ℝ → X) (_ : IsCurveJoining γ x y), curveELength γ 0 1

/-- One half of the length-space condition holds in any space: no curve joining `x` to `y` is
shorter than `edist x y`. -/
theorem edist_le_iInf_curveELength (x y : X) :
    edist x y ≤ ⨅ (γ : ℝ → X) (_ : IsCurveJoining γ x y), curveELength γ 0 1 :=
  le_iInf₂ fun _ h => h.edist_le

/-- To check that a space is a length space it suffices to produce, for every pair of points and
every bound strictly above their distance, a joining curve shorter than that bound. -/
theorem IsLengthSpace.of_exists_curveELength_lt
    (h : ∀ (x y : X) (c : ℝ≥0∞), edist x y < c →
      ∃ γ : ℝ → X, IsCurveJoining γ x y ∧ curveELength γ 0 1 < c) :
    IsLengthSpace X where
  edist_eq_iInf x y := by
    refine le_antisymm (edist_le_iInf_curveELength x y) ?_
    by_contra hcon
    obtain ⟨γ, hγ, hlt⟩ := h x y _ (not_le.1 hcon)
    exact absurd (iInf₂_le γ hγ) (not_le.2 hlt)

/-- In a length space, joining curves of length arbitrarily close to the distance exist. -/
theorem IsLengthSpace.exists_curveELength_lt [IsLengthSpace X] {c : ℝ≥0∞} (hc : edist x y < c) :
    ∃ γ : ℝ → X, IsCurveJoining γ x y ∧ curveELength γ 0 1 < c := by
  simp only [IsLengthSpace.edist_eq_iInf x y, iInf_lt_iff, exists_prop] at hc
  exact hc

/-- Any two points of a length space with finite distances are joined by a continuous curve. -/
theorem IsLengthSpace.joined {X : Type*} [PseudoMetricSpace X] [IsLengthSpace X] (x y : X) :
    Joined x y := by
  obtain ⟨γ, hγ, -⟩ := IsLengthSpace.exists_curveELength_lt (x := x) (y := y) (c := ⊤)
    (edist_lt_top x y)
  exact hγ.joined

/-- A nonempty length space with finite distances is path connected. This is not an instance:
`PathConnectedSpace` is a goal about a bare topological space, and searching a metric structure
and a length-space structure on every such goal is not worth it. -/
theorem IsLengthSpace.pathConnectedSpace {X : Type*} [PseudoMetricSpace X] [IsLengthSpace X]
    [Nonempty X] : PathConnectedSpace X :=
  ⟨‹Nonempty X›, IsLengthSpace.joined⟩

/-- The metric form of `TauCeti.IsLengthSpace.exists_curveELength_lt`. -/
theorem IsLengthSpace.exists_curveELength_lt_ofReal {X : Type*} [PseudoMetricSpace X]
    [IsLengthSpace X] {x y : X} {r : ℝ} (hr : dist x y < r) :
    ∃ γ : ℝ → X, IsCurveJoining γ x y ∧ curveELength γ 0 1 < ENNReal.ofReal r := by
  refine IsLengthSpace.exists_curveELength_lt ?_
  rw [edist_dist]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.2 hr

end IsLengthSpace

/-! ### Geodesic segments and geodesic spaces -/

section Geodesic

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {x y : X}

/-- `IsGeodesicSegment γ x y` says that the curve `γ`, read on the parameter interval `[0, 1]`,
runs from `x` to `y` with `dist (γ s) (γ t) = |s - t| * dist x y`: it is a shortest curve from `x`
to `y`, parametrised proportionally to arclength. -/
structure IsGeodesicSegment (γ : ℝ → X) (x y : X) : Prop where
  /-- A geodesic segment starts at `x`. -/
  source : γ 0 = x
  /-- A geodesic segment ends at `y`. -/
  target : γ 1 = y
  /-- A geodesic segment is affinely parametrised by arclength. -/
  dist_eq : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (γ s) (γ t) = |s - t| * dist x y

/-- A geodesic segment is Lipschitz on its parameter interval, with constant `dist x y`. -/
theorem IsGeodesicSegment.lipschitzOnWith (h : IsGeodesicSegment γ x y) :
    LipschitzOnWith (dist x y).toNNReal γ (Icc 0 1) :=
  LipschitzOnWith.of_dist_le_mul fun s hs t ht => by
    rw [h.dist_eq s hs t ht, Real.coe_toNNReal _ dist_nonneg, Real.dist_eq, mul_comm]

theorem IsGeodesicSegment.continuousOn (h : IsGeodesicSegment γ x y) :
    ContinuousOn γ (Icc 0 1) :=
  h.lipschitzOnWith.continuousOn

theorem IsGeodesicSegment.isCurveJoining (h : IsGeodesicSegment γ x y) : IsCurveJoining γ x y where
  continuousOn := h.continuousOn
  source := h.source
  target := h.target

/-- The constant curve is a geodesic segment from a point to itself. -/
theorem isGeodesicSegment_const (x : X) : IsGeodesicSegment (fun _ : ℝ => x) x x where
  source := rfl
  target := rfl
  dist_eq _ _ _ _ := by simp

/-- Running a geodesic segment backwards gives a geodesic segment between the same points. -/
theorem IsGeodesicSegment.reverse (h : IsGeodesicSegment γ x y) :
    IsGeodesicSegment (fun t => γ (1 - t)) y x where
  source := by simpa using h.target
  target := by simpa using h.source
  dist_eq s hs t ht := by
    have hs' : 1 - s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [h.dist_eq _ hs' _ ht', dist_comm y x, sub_sub_sub_cancel_left, abs_sub_comm]

/-- No piece of a geodesic segment is longer than the affine bound its parametrisation predicts.
The reverse inequality is `TauCeti.edist_le_curveELength`, so the two together identify the
length of every piece. -/
theorem IsGeodesicSegment.curveELength_le (h : IsGeodesicSegment γ x y) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    curveELength γ a b ≤ ENNReal.ofReal ((b - a) * dist x y) := by
  rw [curveELength_eq_eVariationOn, eVariationOn]
  refine iSup_le ?_
  rintro ⟨n, u, hu, hus⟩
  have key : ∀ i : ℕ, edist (γ (u (i + 1))) (γ (u i))
      = ENNReal.ofReal ((u (i + 1) - u i) * dist x y) := by
    intro i
    have hi : u i ∈ Icc (0 : ℝ) 1 := Icc_subset_Icc ha.1 hb.2 (hus i)
    have hi' : u (i + 1) ∈ Icc (0 : ℝ) 1 := Icc_subset_Icc ha.1 hb.2 (hus (i + 1))
    rw [edist_dist, h.dist_eq _ hi' _ hi,
      abs_of_nonneg (sub_nonneg.2 (hu (Nat.le_succ i)))]
  simp only [key]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ =>
    mul_nonneg (sub_nonneg.2 (hu (Nat.le_succ i))) dist_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.sum_mul, Finset.sum_range_sub fun i => u i]
  refine mul_le_mul_of_nonneg_right ?_ dist_nonneg
  have h0 : a ≤ u 0 := (hus 0).1
  have hn : u n ≤ b := (hus n).2
  linarith

/-- A geodesic segment realises the distance between any two of its points. -/
theorem IsGeodesicSegment.curveELength_eq_edist (h : IsGeodesicSegment γ x y) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≤ b) :
    curveELength γ a b = edist (γ a) (γ b) := by
  refine le_antisymm ?_
    (edist_le_curveELength γ (left_mem_Icc.2 hab) (right_mem_Icc.2 hab))
  rw [edist_dist, h.dist_eq a ha b hb, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hab)]
  exact h.curveELength_le ha hb

/-- A geodesic segment from `x` to `y` has length `edist x y`. -/
theorem IsGeodesicSegment.curveELength_eq (h : IsGeodesicSegment γ x y) :
    curveELength γ 0 1 = edist x y := by
  rw [h.curveELength_eq_edist (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    zero_le_one, h.source, h.target]

/-- A *geodesic space* is a space in which any two points are joined by a geodesic segment. -/
class IsGeodesicSpace (X : Type*) [PseudoMetricSpace X] : Prop where
  /-- Any two points are joined by a geodesic segment. -/
  exists_isGeodesicSegment (x y : X) : ∃ γ : ℝ → X, IsGeodesicSegment γ x y

/-- In a geodesic space the infimum defining the length-space condition is attained. -/
theorem IsGeodesicSpace.exists_curveELength_eq [IsGeodesicSpace X] (x y : X) :
    ∃ γ : ℝ → X, IsCurveJoining γ x y ∧ curveELength γ 0 1 = edist x y := by
  obtain ⟨γ, hγ⟩ := IsGeodesicSpace.exists_isGeodesicSegment x y
  exact ⟨γ, hγ.isCurveJoining, hγ.curveELength_eq⟩

/-- **A geodesic space is a length space.** -/
instance IsGeodesicSpace.toIsLengthSpace [IsGeodesicSpace X] : IsLengthSpace X where
  edist_eq_iInf x y := by
    obtain ⟨γ, hγ, hlen⟩ := IsGeodesicSpace.exists_curveELength_eq x y
    exact le_antisymm (edist_le_iInf_curveELength x y) (hlen ▸ iInf₂_le γ hγ)

end Geodesic

/-! ### Seminormed spaces -/

section Normed

/-- In a real normed torsor the affine segment from `x` to `y` is a geodesic segment. -/
theorem isGeodesicSegment_lineMap {V P : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [PseudoMetricSpace P] [NormedAddTorsor V P] (x y : P) :
    IsGeodesicSegment (AffineMap.lineMap x y) x y where
  source := AffineMap.lineMap_apply_zero x y
  target := AffineMap.lineMap_apply_one x y
  dist_eq s _ t _ := by
    rw [dist_lineMap_lineMap, Real.dist_eq]

/-- A real normed torsor is a geodesic space. This is stated as a theorem rather than an instance
because the acting space `V` would have to be guessed before the torsor structure is found; the
instance below covers the case of a seminormed space acting on itself. -/
theorem IsGeodesicSpace.of_normedAddTorsor {V P : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] [PseudoMetricSpace P] [NormedAddTorsor V P] : IsGeodesicSpace P :=
  ⟨fun x y => ⟨AffineMap.lineMap x y, isGeodesicSegment_lineMap x y⟩⟩

instance instIsGeodesicSpace {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] :
    IsGeodesicSpace E :=
  IsGeodesicSpace.of_normedAddTorsor (V := E)

/-- The instance chain reaches the length-space condition: `ℝ` is a length space because it is a
geodesic space. -/
example : IsLengthSpace ℝ := inferInstance

end Normed

end TauCeti
