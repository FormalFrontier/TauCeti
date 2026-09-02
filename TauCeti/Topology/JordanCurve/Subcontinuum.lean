/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Circle.Arc
public import TauCeti.Topology.JordanCurve.Basic

/-!
# A proper subcontinuum of a Jordan curve is an arc

`TauCeti/Topology/JordanCurve/Separation.lean` cuts a Jordan curve at one or two *given* points.
This file describes the pieces from the other side: it classifies the compact connected subsets of
a Jordan curve. Every one of them other than the curve itself is a point or an **arc** — the range
of an injective path — and its complement in the curve is again path connected. In particular a
compact connected subset that is *nowhere dense in the curve* is a subsingleton, hence a single
point as soon as it is nonempty, which is the form in which the classification is spent.

## The argument

Everything is transported from the model curve `Circle`, so the work is on the circle, and the
transport is the parametrization `TauCeti.jordanParam` of `TauCeti/Topology/JordanCurve/Basic.lean`.

The circle half is `TauCeti/Topology/Circle/Arc.lean`: a nonempty closed preconnected proper subset
of the circle is a closed arc `Circle.exp '' Icc a b` with `b - a < 2 * π`
(`TauCeti.exists_eq_circleExp_image_Icc`), the two degenerate cases `a = b` and the empty set being
the point and the empty set, and its complement is the open arc `Circle.exp '' Ioo b (a + 2 * π)`
(`TauCeti.compl_circleExp_image_Icc`), path connected as the continuous image of an interval. So a
proper subcontinuum `S` of the curve is the image of such a closed arc of angles under the
parametrization, and `C \ S` the image of the complementary open arc.

Nowhere density is the same computation once more. If `a < b` then the midpoint `(a + b) / 2` names
a point of `S` whose angle lies outside `Icc b (a + 2 * π)`, so it lies outside the image of that
compact interval of angles, which is closed and contains the whole of `C \ S`; hence that point of
`S` is not adherent to `C \ S`, and `S` is not nowhere dense. Contrapositively, a nowhere dense
compact connected subset is a subsingleton: it is empty, or it has `a = b` and is a point.

## Why this is a layer-L5 prerequisite

The target is layer **L5** of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`), Carathéodory's boundary correspondence for a Jordan
domain. `ConformalMapping/STATUS.md` counts the Jordan-curve side of that layer as its
infrastructure, listing Jordan curves with "the arc theory the boundary work needs: two points cut
it into two arcs, and two nearby points cut off a small one", and, of the topological facts about
Jordan curves that the forward direction classically leans on, asks under **Plane separation for
Jordan curves** that how much of them it needs "should be settled first". The classification of the
compact connected subsets of a curve is one such fact, established here with no conformal input, as
`TauCeti/Topology/JordanCurve/Separation.lean` settles the cutting of a curve at given points and
`TauCeti/Topology/JordanCurve/SmallArc.lean` the size of the pieces that cutting leaves. Of the
statements below, `TauCeti.IsJordanCurve.isPathConnected_sdiff` is a strict generalisation of the
`Separation.lean` statement for a removed point.

The path from here to that target is one step, and it is a reduction. A boundary cluster set of a
conformal map is already known in this repository to be a *continuum contained in the image
boundary* (`TauCeti.isConnected_clusterSetOn_of_convex_of_isBounded` together with
`TauCeti.clusterSetOn_subset_frontier_image`), so for a Jordan domain it is a compact connected
subset of a Jordan curve — and until this file nothing said what such a set can be. The results
here say it: a point, an arc, or the whole curve —
`TauCeti.subsingleton_or_exists_injective_path_clusterSetOn`, in
`TauCeti/Analysis/Complex/Conformal/ClusterSet.lean`. L5's forward direction is the assertion that
for a Riemann map the first case always holds, so what this file leaves of it on the Jordan-curve
side is exactly the exclusion of the other two.

`TauCeti.IsJordanCurve.subsingleton_of_subset_closure_sdiff` excludes both at once from a single
condition on the subcontinuum — that it be nowhere dense in the curve — and that is the step of the
L5 argument this file exists for: fed to
`TauCeti.exists_continuousOn_closure_eqOn_of_isBounded` — the criterion that turns singleton
boundary cluster sets into a continuous extension on the closure of the domain, and the companion of
the diameter form `TauCeti.exists_continuousOn_closure_eqOn_of_forall_exists_diam_union_le` that
`ConformalMapping/STATUS.md` names as proved — it gives
`TauCeti.exists_continuousOn_closure_eqOn_of_forall_subset_closure_sdiff`, a conformal map of
a convex domain onto a bounded Jordan-bounded region none of whose boundary cluster sets has
interior in the boundary curve extends continuously to `closure U`. That conclusion is the L5
milestone's conclusion; the hypothesis separating them is relative nowhere density of each boundary
cluster set in the curve. That is a condition on the cluster sets, which depend on the map, its
domain and the boundary point, and not one on the curve by itself: what it drops is the analytic
content of the milestone, not the map.

Verifying that hypothesis for a Riemann map is not attempted here, and nothing here shortens or
replaces the route `ConformalMapping/STATUS.md` sequences next for it: showing that the boundary
piece a small crosscut cuts off is itself small, which the length–area estimate and the crosscut
files are aimed at, proves singletonness directly.

## Generality

The statements are for a subset of an arbitrary topological space, as in
`TauCeti/Topology/JordanCurve/Separation.lean`; the subcontinuum is asked to be *compact* rather
than closed, which is what transports along the parametrization without a separation axiom. Only the
two nowhere-density statements `TauCeti.IsJordanCurve.exists_notMem_closure_sdiff` and
`TauCeti.IsJordanCurve.subsingleton_of_subset_closure_sdiff` need the ambient space to be Hausdorff,
because they speak of a closure taken in that space.

## Main results

* `TauCeti.IsJordanCurve.subsingleton_or_exists_injective_path` — **a proper subcontinuum of a
  Jordan curve is a point or an arc**: it is either a subsingleton or the range of an injective
  path.
* `TauCeti.IsJordanCurve.isPathConnected_sdiff` — the complement of a proper subcontinuum in the
  curve is path connected; for a singleton this is
  `TauCeti.IsJordanCurve.isPathConnected_sdiff_singleton`.
* `TauCeti.IsJordanCurve.exists_notMem_closure_sdiff` — a subcontinuum with more than one point is
  not nowhere dense: one of its points is not adherent to the rest of the curve.
* `TauCeti.IsJordanCurve.subsingleton_of_subset_closure_sdiff` — the contrapositive, and the form
  the boundary correspondence consumes: a compact connected subset of a Jordan curve every point of
  which is adherent to the complement is a subsingleton, so a single point once it is nonempty.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
-/

public section

namespace TauCeti

open Real Set Topology

variable {X : Type*} [TopologicalSpace X] {C S : Set X}

/-! ## Subcontinua of a Jordan curve

Each statement below transports its circle counterpart along the parametrization
`TauCeti.jordanParam e`, which is a continuous injection with range the curve. The two private
lemmas carry the closed arc and its complement across it once and for all; the theorems then read
off the consequences. -/

/-- The transport of `TauCeti.exists_eq_circleExp_image_Icc` to a Jordan curve: a nonempty compact
preconnected proper subset of the curve is the image of a closed arc of angles under the
parametrization. -/
private lemma exists_eq_jordanParam_image (e : C ≃ₜ Circle) (hSC : S ⊆ C) (hS : IsCompact S)
    (hpre : IsPreconnected S) (hne : S.Nonempty) (hSne : S ≠ C) :
    ∃ a b : ℝ, a ≤ b ∧ b - a < 2 * π ∧ S = jordanParam e '' (Circle.exp '' Icc a b) := by
  set g : Circle → X := jordanParam e
  have hginj : Function.Injective g := jordanParam_injective e
  have hgrange : range g = C := range_jordanParam e
  set T : Set Circle := g ⁻¹' S
  have himg : g '' T = S := image_preimage_eq_of_subset (hgrange ▸ hSC)
  have hTcompact : IsCompact T := (isInducing_jordanParam e).isCompact_iff.mpr (himg ▸ hS)
  have hTpre : IsPreconnected T :=
    ((isInducing_jordanParam e).isPreconnected_image).mp (himg ▸ hpre)
  have hTne : T.Nonempty := by
    rw [← image_nonempty (f := g), himg]
    exact hne
  have hTuniv : T ≠ univ := fun hcon => hSne (by rw [← himg, hcon, image_univ, hgrange])
  obtain ⟨a, b, hab, hlt, hTeq⟩ :=
    exists_eq_circleExp_image_Icc hTcompact.isClosed hTpre hTne hTuniv
  exact ⟨a, b, hab, hlt, by rw [← himg, hTeq]⟩

/-- **A proper subcontinuum of a Jordan curve is a point or an arc.** A compact preconnected subset
of a Jordan curve other than the curve itself is either a subsingleton — the empty set or a single
point — or the range of an injective path, which is what it means for it to be an arc.

The path is the closed arc of angles produced by `TauCeti.exists_eq_circleExp_image_Icc`, carried to
the curve; it is injective because `Circle.exp` is injective on an interval shorter than a full turn
and the parametrization of the curve is injective outright. Its endpoints, `γ 0` and `γ 1`, are the
two endpoints of the arc. -/
theorem IsJordanCurve.subsingleton_or_exists_injective_path (h : IsJordanCurve C) (hSC : S ⊆ C)
    (hS : IsCompact S) (hpre : IsPreconnected S) (hSne : S ≠ C) :
    S.Subsingleton ∨ ∃ (p q : X) (γ : Path p q), Function.Injective γ ∧ range γ = S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact Or.inl subsingleton_empty
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  obtain ⟨a, b, hab, hlt, hSeq⟩ := exists_eq_jordanParam_image e hSC hS hpre hne hSne
  rcases eq_or_lt_of_le hab with rfl | hab'
  · refine Or.inl ?_
    rw [hSeq, Icc_self, image_singleton, image_singleton]
    exact subsingleton_singleton
  refine Or.inr ⟨_, _,
    ((Path.segment a b).map Circle.exp.continuous).map (continuous_jordanParam e), ?_, ?_⟩
  · have hseg : range (Path.segment a b) = Icc a b := by
      rw [Path.range_segment, segment_eq_Icc hab]
    intro x y hxy
    rw [Path.map_coe, Path.map_coe] at hxy
    have h₁ : Circle.exp (Path.segment a b x) = Circle.exp (Path.segment a b y) :=
      jordanParam_injective e hxy
    have h₂ : (Path.segment a b) x = (Path.segment a b) y :=
      Circle.exp_injOn_Icc hlt (hseg ▸ mem_range_self x) (hseg ▸ mem_range_self y) h₁
    exact Path.segment_injective_of_ne hab'.ne h₂
  · rw [Path.map_coe, Path.map_coe, range_comp, range_comp, Path.range_segment,
      segment_eq_Icc hab, hSeq]

/-- The complement in the curve of the image of a closed arc of angles is the image of the
complementary open arc, by `TauCeti.compl_circleExp_image_Icc` and injectivity of the
parametrization. -/
private lemma sdiff_eq_jordanParam_image (e : C ≃ₜ Circle) {a b : ℝ} (hab : a ≤ b)
    (hlt : b - a < 2 * π) (hSeq : S = jordanParam e '' (Circle.exp '' Icc a b)) :
    C \ S = jordanParam e '' (Circle.exp '' Ioo b (a + 2 * π)) := by
  rw [← compl_circleExp_image_Icc hab hlt, compl_eq_univ_sdiff, hSeq,
    (jordanParam_injective e).injOn.image_sdiff_subset (subset_univ _), image_univ,
    range_jordanParam]

/-- **The complement of a proper subcontinuum in a Jordan curve is path connected.** Removing a
compact connected piece other than the whole curve leaves an open arc, in particular a nonempty path
connected set. The case of a single point is
`TauCeti.IsJordanCurve.isPathConnected_sdiff_singleton`. -/
theorem IsJordanCurve.isPathConnected_sdiff (h : IsJordanCurve C) (hSC : S ⊆ C) (hS : IsCompact S)
    (hpre : IsPreconnected S) (hSne : S ≠ C) : IsPathConnected (C \ S) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · rw [sdiff_empty]
    exact h.isPathConnected
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  obtain ⟨a, b, hab, hlt, hSeq⟩ := exists_eq_jordanParam_image e hSC hS hpre hne hSne
  rw [sdiff_eq_jordanParam_image e hab hlt hSeq]
  refine IsPathConnected.image' ?_ (continuous_jordanParam e).continuousOn
  exact ((convex_Ioo b (a + 2 * π)).isPathConnected
    (nonempty_Ioo.mpr (by linarith))).image' Circle.exp.continuous.continuousOn

/-! ## Nowhere density

A subcontinuum with more than one point occupies a relatively open piece of the curve, so it is not
nowhere dense there. Stated in the contrapositive this is what identifies a nowhere dense
subcontinuum as a subsingleton — a single point once it is nonempty, which is how the classification
is used — and it is the form the Carathéodory boundary correspondence spends:
a boundary cluster set of a conformal map is a continuum on the image boundary, and this is what
degenerates it. Both statements are about a closure taken in the ambient space, so that space is
asked to be Hausdorff here. -/

/-- **A subcontinuum of a Jordan curve with more than one point is not nowhere dense in it**: one of
its points is not adherent to the rest of the curve.

The witness is the midpoint of the arc of angles carrying the subcontinuum. The complement of the
subcontinuum in the curve is the open arc of `TauCeti.compl_circleExp_image_Icc`, whose closure is
contained in the compact — hence closed — image of the corresponding closed arc, and the midpoint
misses that image because `Circle.exp` is injective on a period. The subcontinuum is not asked to be
proper: for the whole curve the complement is empty and any of its points will do. -/
theorem IsJordanCurve.exists_notMem_closure_sdiff [T2Space X] (h : IsJordanCurve C) (hSC : S ⊆ C)
    (hS : IsCompact S) (hpre : IsPreconnected S) (hnsub : ¬ S.Subsingleton) :
    ∃ p ∈ S, p ∉ closure (C \ S) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := not_subsingleton_iff.mp hnsub
  rcases eq_or_ne S C with rfl | hSne
  · exact ⟨x, hx, by simp⟩
  obtain ⟨e⟩ := isJordanCurve_iff.mp h
  obtain ⟨a, b, hab, hlt, hSeq⟩ := exists_eq_jordanParam_image e hSC hS hpre ⟨x, hx⟩ hSne
  have hab' : a < b := by
    rcases eq_or_lt_of_le hab with rfl | hab'
    · rw [hSeq, Icc_self, image_singleton, image_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hxy
    · exact hab'
  have hLclosed : IsClosed (jordanParam e '' (Circle.exp '' Icc b (a + 2 * π))) :=
    ((isCompact_Icc.image Circle.exp.continuous).image (continuous_jordanParam e)).isClosed
  have hsub : C \ S ⊆ jordanParam e '' (Circle.exp '' Icc b (a + 2 * π)) := by
    rw [sdiff_eq_jordanParam_image e hab hlt hSeq]
    exact image_mono (image_mono Ioo_subset_Icc_self)
  have hmmem : (a + b) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hpS : jordanParam e (Circle.exp ((a + b) / 2)) ∈ S := by
    rw [hSeq]
    exact mem_image_of_mem _ (mem_image_of_mem _ hmmem)
  refine ⟨_, hpS, fun hcon => ?_⟩
  obtain ⟨u, ⟨s, hs, hsu⟩, hu⟩ := closure_minimal hsub hLclosed hcon
  have hsm : s = (a + b) / 2 := by
    refine Circle.exp_injOn_Ioc (a := a) (b := a + 2 * π) (by linarith)
      ⟨by linarith [hs.1], hs.2⟩ ⟨by linarith, by linarith⟩ ?_
    rw [hsu]
    exact jordanParam_injective e hu
  linarith [hs.1, hsm ▸ hs.1]

/-- **A nowhere dense subcontinuum of a Jordan curve is a subsingleton**, so a single point when it
is nonempty. If every point of a compact preconnected subset of a Jordan curve is adherent to the
complement of that subset in the curve, then the subset has at most one point.

This is the contrapositive of `TauCeti.IsJordanCurve.exists_notMem_closure_sdiff`. -/
theorem IsJordanCurve.subsingleton_of_subset_closure_sdiff [T2Space X] (h : IsJordanCurve C)
    (hSC : S ⊆ C) (hS : IsCompact S) (hpre : IsPreconnected S) (hdense : S ⊆ closure (C \ S)) :
    S.Subsingleton := by
  by_contra hnsub
  obtain ⟨p, hp, hpn⟩ := h.exists_notMem_closure_sdiff hSC hS hpre hnsub
  exact hpn (hdense hp)

/-! ### Jordan curves in ℂ -/

open Metric Function

/-- **A Jordan curve has, near any of its points, a closed preconnected arc
missing that point whose complement lies in a given ball around it.**  The
closed arc `S` is the image of a closed circle arc under the Jordan
parametrization, chosen small enough that its complement `J \ S` — the open
window through `a` — stays inside `ball a r`.

`S` is built directly: parametrize `J` by `jordanParam e`, pick an angle
`θ₀` over `a`, and let `S` be the image of the closed arc of angles
`Icc (θ₀ + η) (θ₀ - η + 2π)`, compact and preconnected as a continuous image
of an interval; continuity at `θ₀` keeps its complement inside `ball a r`. -/
theorem IsJordanCurve.exists_isClosed_isPreconnected_notMem_sdiff_subset_ball
    {J : Set ℂ} (hJ : IsJordanCurve J) {a : ℂ} (ha : a ∈ J) {r : ℝ} (hr : 0 < r) :
    ∃ S ⊆ J, IsClosed S ∧ IsPreconnected S ∧ a ∉ S ∧ J \ S ⊆ ball a r := by
  obtain ⟨e⟩ := isJordanCurve_iff.mp hJ
  set g : Circle → ℂ := jordanParam e with hg
  have hginj : Injective g := jordanParam_injective e
  have hgrange : range g = J := range_jordanParam e
  have hgc : Continuous g := continuous_jordanParam e
  obtain ⟨u₀, hu₀⟩ : a ∈ range g := by rw [hgrange]; exact ha
  obtain ⟨θ₀, hθ₀⟩ := Circle.exp_surjective u₀
  have hga : g (Circle.exp θ₀) = a := by rw [hθ₀, hu₀]
  -- continuity of `g ∘ Circle.exp` at `θ₀`
  have hcont : ContinuousAt (fun θ : ℝ => g (Circle.exp θ)) θ₀ :=
    (hgc.comp Circle.exp.continuous).continuousAt
  obtain ⟨η₀, hη₀, hη⟩ := Metric.continuousAt_iff.mp hcont r hr
  set η : ℝ := min η₀ (π / 2) with hηdef
  have hηpos : 0 < η := lt_min hη₀ (by positivity)
  have hηle : η ≤ π / 2 := min_le_right _ _
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  set K : Set Circle := Circle.exp '' Icc (θ₀ + η) (θ₀ - η + 2 * π) with hK
  set S : Set ℂ := g '' K with hS
  have hSJ : S ⊆ J := by rw [← hgrange]; exact image_subset_range _ _
  have hScompact : IsCompact S :=
    (isCompact_Icc.image Circle.exp.continuous).image hgc
  have hSpre : IsPreconnected S :=
    (isPreconnected_Icc.image _ Circle.exp.continuous.continuousOn).image _ hgc.continuousOn
  have hab : θ₀ + η ≤ θ₀ - η + 2 * π := by linarith [pi_pos]
  have hlt : (θ₀ - η + 2 * π) - (θ₀ + η) < 2 * π := by linarith
  refine ⟨S, hSJ, hScompact.isClosed, hSpre, ?_, ?_⟩
  · -- `a ∉ S`
    rintro ⟨u, huK, hu⟩
    have : u = Circle.exp θ₀ := hginj (hu.trans hga.symm)
    subst this
    obtain ⟨θ, hθ, hθeq⟩ := huK
    have hnot : Circle.exp θ₀ ∈ (Circle.exp '' Icc (θ₀ + η) (θ₀ - η + 2 * π))ᶜ := by
      rw [compl_circleExp_image_Icc hab hlt]
      refine ⟨θ₀ + 2 * π, ⟨by linarith, by linarith⟩, ?_⟩
      rw [Circle.exp_add, Circle.exp_two_pi, mul_one]
    exact hnot ⟨θ, hθ, hθeq⟩
  · -- `J \ S ⊆ ball a r`
    rintro z ⟨hzJ, hzS⟩
    rw [← hgrange] at hzJ
    obtain ⟨u, rfl⟩ := hzJ
    have huK : u ∉ K := fun h => hzS ⟨u, h, rfl⟩
    have hu : u ∈ Circle.exp '' Ioo (θ₀ - η + 2 * π) (θ₀ + η + 2 * π) := by
      have := compl_circleExp_image_Icc hab hlt
      rw [← hK] at this
      have hu' : u ∈ Kᶜ := huK
      rw [this] at hu'
      convert hu' using 3
    obtain ⟨θ, hθ, rfl⟩ := hu
    have hshift : Circle.exp θ = Circle.exp (θ - 2 * π) := by
      have hθ2 : θ = (θ - 2 * π) + 2 * π := by ring
      conv_lhs => rw [hθ2]
      rw [Circle.exp_add, Circle.exp_two_pi, mul_one]
    rw [hshift, mem_ball, ← hga]
    apply hη
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hθ.1, hθ.2]

end TauCeti
