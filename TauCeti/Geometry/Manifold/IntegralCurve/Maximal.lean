/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.Extension

/-!
# The maximal integral curve of a vector field

Mathlib's integral-curve API produces a local integral curve through a point and shows that two
integral curves on a common open interval agree, and
`TauCeti/Geometry/Manifold/IntegralCurve/Extension.lean` extends an integral curve past a finite
endpoint at which it accumulates. What is still missing is the object those results describe: the
*maximal* integral curve of a `C^1` vector field `v` through a point `x`, defined on the largest
open interval around `0` on which any integral curve through `x` exists.

This file builds it. `maximalIntegralCurveInterval v x` is the union of the open intervals around
`0` carrying an integral curve of `v` taking the value `x` at time `0`, and
`maximalIntegralCurve v x` is the curve obtained by reading off, at each time of that set, the
value of one such witness, chosen arbitrarily. That choice becomes immaterial once `M` is a
separated boundaryless `C^1` manifold and `v` is a `C^1` field: uniqueness of integral curves on a
common interval then makes the reading unambiguous, so the maximal curve restricts to every
witness, is itself an integral curve on the whole interval, and is the largest one: every integral
curve through `x` on an open interval around `0` is one of its restrictions.

The interval is open and `Set.OrdConnected`, hence an interval in the order sense, and it contains
`0` as soon as `v` is `C^1` at `x` on a boundaryless manifold. At a finite endpoint the extension
criterion of `Extension.lean` applies with its maximality hypothesis discharged: the maximal curve
has no cluster point in `M` as the endpoint is approached, so in particular it leaves every compact
set there. Consequently a maximal curve confined to a compact set is defined for all time, and
every `C^1` vector field on a compact manifold is complete.

Only the initial time `0` is used, matching the intended geodesic application: for the geodesic
spray on the tangent bundle, `maximalIntegralCurveInterval` is the maximal interval `J(p, v)` of
the geodesic with initial data `(p, v)`. Since the fields considered here are autonomous, an
arbitrary initial time is recovered by translating the parameter with
`IsMIntegralCurveOn.comp_add`.

## Main definitions

* `maximalIntegralCurveInterval v x`: the maximal interval of existence of an integral curve of
  `v` through `x` at time `0`.
* `maximalIntegralCurve v x`: the maximal integral curve of `v` through `x`, junk-valued outside
  `maximalIntegralCurveInterval v x`.

## Main results

* `isOpen_maximalIntegralCurveInterval`, `ordConnected_maximalIntegralCurveInterval` and
  `isPreconnected_maximalIntegralCurveInterval`: the maximal interval of existence is an open
  interval, and `zero_mem_maximalIntegralCurveInterval` puts `0` in it.
* `isMIntegralCurveOn_maximalIntegralCurve`: the maximal curve is an integral curve of `v` on the
  maximal interval, with `maximalIntegralCurve_zero` giving its value at `0`.
* `IsMIntegralCurveOn.eqOn_maximalIntegralCurve` and
  `IsMIntegralCurveOn.subset_maximalIntegralCurveInterval`: every integral curve through `x` on an
  open interval around `0` is a restriction of the maximal one.
* `exists_Ioo_subset_maximalIntegralCurveInterval_of_isLUB` and its `IsGLB` counterpart: a finite
  endpoint of the maximal interval is reached by an open subinterval straddling `0`.
* `not_mapClusterPt_nhdsLT_maximalIntegralCurve` and
  `not_mapClusterPt_nhdsGT_maximalIntegralCurve`: at a finite endpoint of the maximal interval the
  maximal curve has no cluster point in the manifold, with
  `eventually_notMem_nhdsLT_maximalIntegralCurve` and
  `eventually_notMem_nhdsGT_maximalIntegralCurve` the compact-set forms.
* `maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo`: a maximal curve confined to a
  compact set is defined for all time, and `isMIntegralCurve_maximalIntegralCurve` specializes this
  to a compact manifold: **a `C^1` vector field on a compact manifold is complete**.
* `maximalIntegralCurveInterval_eq_univ_iff`: the maximal interval is all of `ℝ` exactly when some
  global integral curve passes through `x` at time `0`.

## References

* [Geodesics, the exponential map, and the Hopf–Rinow theorem roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "Maximal interval and homogeneity".
* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012],
  Chapter 9, Theorems 9.12 and 9.16.
* [michaellee94, mathlib4#26413: _Existence of maximal solutions for ODEs meeting
  Picard--Lindelöf conditions_](https://github.com/leanprover-community/mathlib4/pull/26413),
  for the maximal-solution and maximal-domain API direction.
* [Winston Yin, mathlib4#26394: _Existence of local flows on
  manifolds_](https://github.com/leanprover-community/mathlib4/pull/26394), for the manifold
  local-flow formulation and uniform local existence near an initial point.
-/

public section

open Filter Function Manifold Set
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x} {γ : ℝ → M} {a b t : ℝ} {x : M}

/-- **The maximal interval of existence** of an integral curve of `v` through `x`: the set of times
lying in some open interval around `0` on which an integral curve of `v` taking the value `x` at
time `0` is defined.

It is open and order-connected (`isOpen_maximalIntegralCurveInterval`,
`ordConnected_maximalIntegralCurveInterval`). Under the local-existence hypotheses of
`zero_mem_maximalIntegralCurveInterval`, it contains `0`, and `maximalIntegralCurve v x` is an
integral curve of `v` on it. -/
def maximalIntegralCurveInterval (v : (x : M) → TangentSpace I x) (x : M) : Set ℝ :=
  {t | ∃ γ : ℝ → M, ∃ a b : ℝ,
    IsMIntegralCurveOn γ v (Ioo a b) ∧ γ 0 = x ∧ 0 ∈ Ioo a b ∧ t ∈ Ioo a b}

/-- An integral curve of `v` through `x` on an open interval around `0` is defined on a subset of
the maximal interval of existence. -/
theorem IsMIntegralCurveOn.subset_maximalIntegralCurveInterval
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (h0 : (0 : ℝ) ∈ Ioo a b) (hx : γ 0 = x) :
    Ioo a b ⊆ maximalIntegralCurveInterval v x :=
  fun _ ht ↦ ⟨γ, a, b, hγ, hx, h0, ht⟩

/-- The maximal interval of existence is open. -/
theorem isOpen_maximalIntegralCurveInterval : IsOpen (maximalIntegralCurveInterval v x) := by
  rw [isOpen_iff_forall_mem_open]
  rintro t ⟨γ, a, b, hγ, hx, h0, ht⟩
  exact ⟨Ioo a b, hγ.subset_maximalIntegralCurveInterval h0 hx, isOpen_Ioo, ht⟩

/-- The maximal interval of existence is order-connected: it is an interval. Every witness interval
straddles `0`, so a time between two of its elements lies in the witness interval of whichever of
them is on the same side of `0`. -/
theorem ordConnected_maximalIntegralCurveInterval :
    (maximalIntegralCurveInterval v x).OrdConnected := by
  refine ⟨fun p hp q hq u hu ↦ ?_⟩
  rcases le_or_gt 0 u with h | h
  · obtain ⟨γ, a, b, hγ, hx, h0, hq'⟩ := hq
    exact hγ.subset_maximalIntegralCurveInterval h0 hx
      ⟨h0.1.trans_le h, hu.2.trans_lt hq'.2⟩
  · obtain ⟨γ, a, b, hγ, hx, h0, hp'⟩ := hp
    exact hγ.subset_maximalIntegralCurveInterval h0 hx
      ⟨hp'.1.trans_le hu.1, h.trans h0.2⟩

/-- The maximal interval of existence is preconnected. This is the hypothesis under which a
constant-speed statement for the curves defined on it can be read. -/
theorem isPreconnected_maximalIntegralCurveInterval :
    IsPreconnected (maximalIntegralCurveInterval v x) :=
  ordConnected_maximalIntegralCurveInterval.isPreconnected

/-- The maximal interval of existence contains an open interval with the same right endpoint and a
negative left endpoint. In particular a finite least upper bound of the interval is positive. -/
theorem exists_Ioo_subset_maximalIntegralCurveInterval_of_isLUB
    (h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval v x)
    (hb : IsLUB (maximalIntegralCurveInterval v x) b) :
    ∃ a < (0 : ℝ), 0 < b ∧ Ioo a b ⊆ maximalIntegralCurveInterval v x := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_maximalIntegralCurveInterval (v := v) (x := x)) 0 h0
  rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hball
  have hhalf : ε / 2 ∈ maximalIntegralCurveInterval v x := hball ⟨by linarith, by linarith⟩
  refine ⟨-(ε / 2), by linarith, lt_of_lt_of_le (by linarith) (hb.1 hhalf), fun t ht ↦ ?_⟩
  rcases le_or_gt 0 t with h | h
  · obtain ⟨s, hs, hts, -⟩ := hb.exists_between ht.2
    exact ordConnected_maximalIntegralCurveInterval.out h0 hs ⟨h, hts.le⟩
  · exact hball ⟨by linarith [ht.1], by linarith⟩

/-- The maximal interval of existence contains an open interval with the same left endpoint and a
positive right endpoint. In particular a finite greatest lower bound of the interval is
negative. -/
theorem exists_Ioo_subset_maximalIntegralCurveInterval_of_isGLB
    (h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval v x)
    (ha : IsGLB (maximalIntegralCurveInterval v x) a) :
    ∃ b > (0 : ℝ), a < 0 ∧ Ioo a b ⊆ maximalIntegralCurveInterval v x := by
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_maximalIntegralCurveInterval (v := v) (x := x)) 0 h0
  rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hball
  have hhalf : -(ε / 2) ∈ maximalIntegralCurveInterval v x := hball ⟨by linarith, by linarith⟩
  refine ⟨ε / 2, by linarith, lt_of_le_of_lt (ha.1 hhalf) (by linarith), fun t ht ↦ ?_⟩
  rcases le_or_gt t 0 with h | h
  · obtain ⟨s, hs, -, hst⟩ := ha.exists_between ht.1
    exact ordConnected_maximalIntegralCurveInterval.out hs h0 ⟨hst.le, h⟩
  · exact hball ⟨by linarith, by linarith [ht.2]⟩

/-- Local existence puts the initial time in the maximal interval of existence. -/
theorem zero_mem_maximalIntegralCurveInterval [CompleteSpace E] [IsManifold I 1 M]
    [BoundarylessManifold I M]
    (hv : CMDiffAt 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) x) :
    (0 : ℝ) ∈ maximalIntegralCurveInterval v x := by
  obtain ⟨γ, hγ0, hγ⟩ := exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (0 : ℝ) hv
  obtain ⟨ε, hε, hγε⟩ := isMIntegralCurveAt_iff'.mp hγ
  rw [Real.ball_eq_Ioo, zero_sub, zero_add] at hγε
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, by linarith⟩
  exact hγε.subset_maximalIntegralCurveInterval h0 hγ0 h0

/-- **The maximal integral curve** of `v` through `x`: at a time of `maximalIntegralCurveInterval
v x` it is the value there of one integral curve of `v` through `x` defined at that time, chosen
arbitrarily, and outside that set it is junk-valued at `x`.

No hypothesis on `M` or `v` is imposed here, so at this generality the definition only selects the
value of some witness. Under the hypotheses of `IsMIntegralCurveOn.eqOn_maximalIntegralCurve` — `M`
separated, boundaryless and `C^1`, and `v` a `C^1` field — uniqueness of integral curves makes the
value independent of the witness, and that theorem, rather than this definition, is what all the
results below use. -/
noncomputable def maximalIntegralCurve (v : (x : M) → TangentSpace I x) (x : M) (t : ℝ) : M :=
  letI := Classical.dec (t ∈ maximalIntegralCurveInterval v x)
  if h : t ∈ maximalIntegralCurveInterval v x then
    h.choose t
  else x

/-- Outside the maximal interval of existence, the junk value of the maximal integral curve is its
initial point. -/
@[simp]
theorem maximalIntegralCurve_eq_of_not_mem (h : t ∉ maximalIntegralCurveInterval v x) :
    maximalIntegralCurve v x t = x := by
  simp [maximalIntegralCurve, h]

/-- At a time of the maximal interval of existence, the maximal integral curve takes the value of
some integral curve of `v` through `x`. -/
theorem exists_isMIntegralCurveOn_maximalIntegralCurve_eq
    (h : t ∈ maximalIntegralCurveInterval v x) :
    ∃ γ : ℝ → M, ∃ a b : ℝ, IsMIntegralCurveOn γ v (Ioo a b) ∧ γ 0 = x ∧ (0 : ℝ) ∈ Ioo a b ∧
      t ∈ Ioo a b ∧ maximalIntegralCurve v x t = γ t := by
  obtain ⟨a, b, hγ⟩ := h.choose_spec
  exact ⟨_, a, b, hγ.1, hγ.2.1, hγ.2.2.1, hγ.2.2.2, dite_eq_left h⟩

/-- At the initial time, the maximal integral curve takes its prescribed initial value. -/
@[simp]
theorem maximalIntegralCurve_zero (h : (0 : ℝ) ∈ maximalIntegralCurveInterval v x) :
    maximalIntegralCurve v x 0 = x := by
  obtain ⟨γ, _, _, _, hx, _, _, heq⟩ := exists_isMIntegralCurveOn_maximalIntegralCurve_eq h
  rw [heq, hx]

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]

/-- **The maximal integral curve extends every integral curve through `x`.** An integral curve of
`v` on an open interval around `0` taking the value `x` at time `0` is the restriction of
`maximalIntegralCurve v x` to that interval. -/
theorem IsMIntegralCurveOn.eqOn_maximalIntegralCurve
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (hγ : IsMIntegralCurveOn γ v (Ioo a b)) (h0 : (0 : ℝ) ∈ Ioo a b) (hx : γ 0 = x) :
    EqOn (maximalIntegralCurve v x) γ (Ioo a b) := by
  intro t ht
  obtain ⟨δ, c, d, hδ, hδx, hc0, htcd, heq⟩ :=
    exists_isMIntegralCurveOn_maximalIntegralCurve_eq
      (hγ.subset_maximalIntegralCurveInterval h0 hx ht)
  have hsubδ : Ioo (max a c) (min b d) ⊆ Ioo c d :=
    Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  have hsubγ : Ioo (max a c) (min b d) ⊆ Ioo a b :=
    Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have h0' : (0 : ℝ) ∈ Ioo (max a c) (min b d) := ⟨max_lt h0.1 hc0.1, lt_min h0.2 hc0.2⟩
  have ht' : t ∈ Ioo (max a c) (min b d) := ⟨max_lt ht.1 htcd.1, lt_min ht.2 htcd.2⟩
  rw [heq]
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless h0' hv (hδ.mono hsubδ)
    (hγ.mono hsubγ) (hδx.trans hx.symm) ht'

/-- **The maximal integral curve is an integral curve** of `v` on the maximal interval of
existence. -/
theorem isMIntegralCurveOn_maximalIntegralCurve
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    IsMIntegralCurveOn (maximalIntegralCurve v x) v (maximalIntegralCurveInterval v x) := by
  apply IsMIntegralCurveAt.isMIntegralCurveOn
  rintro t ⟨γ, a, b, hγ, hx, h0, ht⟩
  exact (hγ.congr (hγ.eqOn_maximalIntegralCurve hv h0 hx)).isMIntegralCurveAt
    (Ioo_mem_nhds ht.1 ht.2)

/-- **A maximal integral curve has no cluster point at a finite right endpoint.** If the maximal
interval of existence is bounded above, with least upper bound `b`, then `maximalIntegralCurve v x`
does not accumulate at any point of `M` as `t → b⁻`.

The finite-endpoint extension criterion would otherwise extend the curve past `b`, and the extension
would put times beyond `b` in the maximal interval. This is the form in which metric completeness
is turned into completeness of the field: a limit of the curve at a finite endpoint is exactly what
the criterion forbids. -/
theorem not_mapClusterPt_nhdsLT_maximalIntegralCurve [CompleteSpace E]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval v x)
    (hb : IsLUB (maximalIntegralCurveInterval v x) b) (y : M) :
    ¬ MapClusterPt y (𝓝[<] b) (maximalIntegralCurve v x) := by
  obtain ⟨a, ha, hb0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isLUB h0 hb
  intro hy
  obtain ⟨c, hc, δ, hδ, hδeq⟩ :=
    ((isMIntegralCurveOn_maximalIntegralCurve hv).mono hsub).exists_gt_isMIntegralCurveOn_Ioo
      (ha.trans hb0) hv hy
  have hδ0 : δ 0 = x := by rw [hδeq ⟨ha, hb0⟩, maximalIntegralCurve_zero h0]
  obtain ⟨s, hs⟩ := exists_between hc
  exact absurd (hb.1 (hδ.subset_maximalIntegralCurveInterval ⟨ha, hb0.trans hc⟩ hδ0
    ⟨ha.trans (hb0.trans hs.1), hs.2⟩)) (not_le.mpr hs.1)

/-- **The escape lemma for the maximal integral curve at a finite right endpoint.** If the maximal
interval of existence is bounded above, with least upper bound `b`, the maximal integral curve
leaves every compact set as `t → b⁻`. -/
theorem eventually_notMem_nhdsLT_maximalIntegralCurve [CompleteSpace E]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval v x)
    (hb : IsLUB (maximalIntegralCurveInterval v x) b) {K : Set M} (hK : IsCompact K) :
    ∀ᶠ t in 𝓝[<] b, maximalIntegralCurve v x t ∉ K := by
  by_contra h
  rw [not_eventually] at h
  simp only [not_not] at h
  obtain ⟨z, -, hz⟩ := hK.exists_mapClusterPt_of_frequently h
  exact not_mapClusterPt_nhdsLT_maximalIntegralCurve hv h0 hb z hz

/-- **A maximal integral curve has no cluster point at a finite left endpoint.** If the maximal
interval of existence is bounded below, with greatest lower bound `a`, then
`maximalIntegralCurve v x` does not accumulate at any point of `M` as `t → a⁺`. -/
theorem not_mapClusterPt_nhdsGT_maximalIntegralCurve [CompleteSpace E]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval v x)
    (ha : IsGLB (maximalIntegralCurveInterval v x) a) (y : M) :
    ¬ MapClusterPt y (𝓝[>] a) (maximalIntegralCurve v x) := by
  obtain ⟨b, hb, ha0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isGLB h0 ha
  intro hy
  obtain ⟨c, hc, δ, hδ, hδeq⟩ :=
    ((isMIntegralCurveOn_maximalIntegralCurve hv).mono hsub).exists_lt_isMIntegralCurveOn_Ioo
      (ha0.trans hb) hv hy
  have hδ0 : δ 0 = x := by rw [hδeq ⟨ha0, hb⟩, maximalIntegralCurve_zero h0]
  obtain ⟨s, hs⟩ := exists_between hc
  exact absurd (ha.1 (hδ.subset_maximalIntegralCurveInterval ⟨hc.trans ha0, hb⟩ hδ0
    ⟨hs.1, hs.2.trans (ha0.trans hb)⟩)) (not_le.mpr hs.2)

/-- **The escape lemma for the maximal integral curve at a finite left endpoint.** If the maximal
interval of existence is bounded below, with greatest lower bound `a`, the maximal integral curve
leaves every compact set as `t → a⁺`. -/
theorem eventually_notMem_nhdsGT_maximalIntegralCurve [CompleteSpace E]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval v x)
    (ha : IsGLB (maximalIntegralCurveInterval v x) a) {K : Set M} (hK : IsCompact K) :
    ∀ᶠ t in 𝓝[>] a, maximalIntegralCurve v x t ∉ K := by
  by_contra h
  rw [not_eventually] at h
  simp only [not_not] at h
  obtain ⟨z, -, hz⟩ := hK.exists_mapClusterPt_of_frequently h
  exact not_mapClusterPt_nhdsGT_maximalIntegralCurve hv h0 ha z hz

/-- **A maximal integral curve confined to a compact set is defined for all time.** Neither
endpoint of the maximal interval can be finite, since the escape lemma would force the curve out of
the compact set there. -/
theorem maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo [CompleteSpace E]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)))
    (h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval v x) {K : Set M} (hK : IsCompact K)
    (hmem : MapsTo (maximalIntegralCurve v x) (maximalIntegralCurveInterval v x) K) :
    maximalIntegralCurveInterval v x = univ := by
  have hcontra : ∀ {l : Filter ℝ}, l.NeBot →
      (∀ᶠ t in l, t ∈ maximalIntegralCurveInterval v x) →
      (∀ᶠ t in l, maximalIntegralCurve v x t ∉ K) → False := by
    intro l hl h1 h2
    obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
    exact ht2 (hmem ht1)
  have hup : ¬ BddAbove (maximalIntegralCurveInterval v x) := fun hbdd ↦ by
    have hlub := isLUB_csSup ⟨0, h0⟩ hbdd
    obtain ⟨a, ha, hb0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isLUB h0 hlub
    exact hcontra inferInstance
      (mem_of_superset (Ioo_mem_nhdsLT (ha.trans hb0)) hsub)
      (eventually_notMem_nhdsLT_maximalIntegralCurve hv h0 hlub hK)
  have hlow : ¬ BddBelow (maximalIntegralCurveInterval v x) := fun hbdd ↦ by
    have hglb := isGLB_csInf ⟨0, h0⟩ hbdd
    obtain ⟨b, hb, ha0, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isGLB h0 hglb
    exact hcontra inferInstance
      (mem_of_superset (Ioo_mem_nhdsGT (ha0.trans hb)) hsub)
      (eventually_notMem_nhdsGT_maximalIntegralCurve hv h0 hglb hK)
  refine eq_univ_of_forall fun t ↦ ?_
  rcases le_or_gt 0 t with h | h
  · obtain ⟨s, hs, hts⟩ := not_bddAbove_iff.mp hup t
    exact ordConnected_maximalIntegralCurveInterval.out h0 hs ⟨h, hts.le⟩
  · obtain ⟨s, hs, hst⟩ := not_bddBelow_iff.mp hlow t
    exact ordConnected_maximalIntegralCurveInterval.out hs h0 ⟨hst.le, h.le⟩

/-- **A `C^1` vector field on a compact boundaryless manifold is complete**: its maximal integral
curve through any point is defined for all time. -/
theorem isMIntegralCurve_maximalIntegralCurve [CompleteSpace E] [CompactSpace M]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    IsMIntegralCurve (maximalIntegralCurve v x) v := by
  have h0 := zero_mem_maximalIntegralCurveInterval (v := v) (x := x) hv.contMDiffAt
  rw [isMIntegralCurve_iff_isMIntegralCurveOn,
    ← maximalIntegralCurveInterval_eq_univ_of_isCompact_of_mapsTo hv h0 isCompact_univ
      (fun _ _ ↦ mem_univ _)]
  exact isMIntegralCurveOn_maximalIntegralCurve hv

/-- The maximal interval of existence is all of `ℝ` exactly when a global integral curve of `v`
passes through `x` at time `0`. This is the form in which completeness of the field at a point is
stated. -/
theorem maximalIntegralCurveInterval_eq_univ_iff
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) :
    maximalIntegralCurveInterval v x = univ ↔ ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  refine ⟨fun h ↦ ⟨maximalIntegralCurve v x, maximalIntegralCurve_zero (h ▸ mem_univ 0), ?_⟩,
    fun ⟨γ, hx, hγ⟩ ↦ eq_univ_of_forall fun t ↦ ?_⟩
  · rw [isMIntegralCurve_iff_isMIntegralCurveOn, ← h]
    exact isMIntegralCurveOn_maximalIntegralCurve hv
  · have habs := abs_nonneg t
    refine (hγ.isMIntegralCurveOn (Ioo (-(|t| + 1)) (|t| + 1))).subset_maximalIntegralCurveInterval
      ⟨by linarith, by linarith⟩ hx ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
