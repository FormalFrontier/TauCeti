/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Crosscut.SmallJordanCurve
public import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Analysis.Complex.Conformal.Crosscut.Image
import TauCeti.Topology.ClusterSet

/-!
# The piece a crosscut cuts off lies inside the Jordan curve that closes it

`Conformal/Crosscut/SmallJordanCurve.lean` closes a short image crosscut of a conformal map into an
arbitrarily small Jordan curve `J`. This file spends that: the image of the crosscut neighbourhood
is a connected set disjoint from `J`, so it lies in a single connected component of the complement
of `J`, and if that component is bounded — if the piece is *inside* `J` — then
`TauCeti.diam_le_diam_of_subset_filledHull` bounds the piece by `diam J`. Feeding this to the
oscillation criterion of `Topology/ClusterSet.lean` gives the continuous extension of the map to the
closed disc: **the Carathéodory continuity theorem for a Jordan domain**, layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md`.

## What is proved and what is assumed

Everything above is proved here except one step, which is stated as a hypothesis:

> `hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (filledHull J \ J)` —
> *every point of a Jordan curve is a limit of points inside it.*

It is a true statement — for a Jordan curve the complement has a bounded component, the inside,
whose frontier is the whole curve — so nothing below is vacuous; what is missing is a Lean proof.
It is a form of the Jordan curve theorem, which the pinned Mathlib does not have and which
`TauCeti/Topology/JordanCurve/` does not build: `STATUS.md` of the roadmap records plane separation
for Jordan curves as an open frontier item and asks how much of it the forward direction of the
continuity theorem needs. The answer this file gives is: *exactly that one statement*, and nothing
about the geometry of the particular curve, nor the count of complementary components, nor
Schoenflies. Once it is available, the final theorem below becomes the L5 milestone by discharging
a hypothesis, with no further mathematics.

## How the hypothesis is used

Write `Ω = f '' ball c r`, `σ = f '' (ball c r ∩ sphere ζ ρ)` for the image crosscut, and
`A = f '' (ball c r ∩ ball ζ ρ)`, `B = f '' (ball c r \ closedBall ζ ρ)` for the images of the two
sides, so that `Ω = A ∪ σ ∪ B` disjointly. The small Jordan curve satisfies
`closure σ ⊆ J ⊆ closure σ ∪ frontier Ω`, and:

* `A` and `B` are preconnected — the near side is convex, the far side is
  `TauCeti.isConnected_ball_diff_closedBall` — and each is disjoint from `J`, since it misses
  `frontier Ω` (being inside the open set `Ω`) and misses `closure σ`
  (`TauCeti.disjoint_image_closure_image_inter_sphere`: the closure of an image crosscut meets `Ω`
  only in the crosscut itself, the points it adds being cluster values on `frontier Ω`).
* A point `p` of `σ` lies on `J` and *inside* `Ω`, so a whole ball about it lies in `Ω`. The
  hypothesis puts a point `q` of `filledHull J \ J` in that ball, and `q ∈ Ω \ J ⊆ A ∪ B`.
* So one of `A`, `B` meets `filledHull J` while being preconnected and disjoint from `J`, hence is
  contained in it (`TauCeti.IsPreconnected.subset_filledHull`) and is no wider than `J`.

Which of the two it is, is then decided by size rather than by topology: `B` contains the images of
the centre `c` and of `c + r / 2`, two points at a fixed positive distance apart that no crosscut of
radius `ρ < r / 2` separates from each other, so `B` cannot have diameter below that fixed distance.
Choosing the Jordan curve smaller than it forces the *near* side to be the inside one, which is the
one whose smallness the boundary limit at `ζ` needs.

## Generality

The two lemmas about the closure of an image crosscut are stated for an arbitrary open domain `U`,
as in `Conformal/Crosscut/Image.lean`; from the dichotomy onwards the domain is a disc, which is
where the crosscut vocabulary (`dist ζ c = r`, `ρ < 2 * r`) and the small-Jordan-curve theorem live.
In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything is stated for maps of `ℂ`; the filled hull it runs
on is stated for an arbitrary real normed space in
`TauCeti/Analysis/Normed/Module/FilledHull.lean`.

## Main results

* `TauCeti.closure_image_inter_sphere_inter_image_subset` and
  `TauCeti.disjoint_image_closure_image_inter_sphere` — the closure of an image crosscut meets the
  image domain only in the image crosscut, so it is disjoint from the image of anything in the
  domain that avoids the cutting circle.
* `TauCeti.subset_filledHull_or_subset_filledHull` — one of the two sides of a crosscut has its
  image inside the Jordan curve that closes the image crosscut.
* `TauCeti.exists_diam_image_ball_inter_ball_le` — hence, at every boundary point of the disc, the
  image of the crosscut neighbourhood can be made arbitrarily small.
* `TauCeti.subsingleton_clusterSetOn_ball_of_forall_subset_closure_filledHull_sdiff` and
  `TauCeti.exists_continuousOn_closedBall_eqOn_of_forall_subset_closure_filledHull_sdiff` — the
  boundary limit and the continuous extension to the closed disc.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and the
pinned Mathlib has neither a boundary correspondence for conformal maps nor any Jordan-curve
vocabulary. So this file is new Lean formalization rather than a temporary shim. It consumes the
L0–L3 shim `TauCeti.isOpen_image_of_differentiableOn_of_injOn`, to be refactored onto Mathlib's
open mapping API once the upstream work lands.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2–2.3.
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open Bornology Complex Metric Set

variable {f : ℂ → ℂ} {U : Set ℂ} {c ζ : ℂ} {r ρ : ℝ}

/-! ## The closed image crosscut meets the image domain only in the crosscut -/

/-- **Closing up an image crosscut adds no interior point.** For `f` holomorphic and injective on an
open `U`, the closure of `f '' (U ∩ sphere ζ ρ)` meets `f '' U` only in `f '' (U ∩ sphere ζ ρ)`.

By `TauCeti.closure_image_inter_sphere_eq_union_biUnion_clusterSetOn` the points that closing adds
are cluster values of `f` at points of `frontier U` on the circle, and properness of a conformal map
(`TauCeti.clusterSetOn_inter_sphere_subset_frontier_inter_closure_image`) puts those on
`frontier (f '' U)`, which is disjoint from the open set `f '' U`. -/
theorem closure_image_inter_sphere_inter_image_subset (hUo : IsOpen U)
    (hfd : DifferentiableOn ℂ f U) (hinj : InjOn f U) :
    closure (f '' (U ∩ sphere ζ ρ)) ∩ f '' U ⊆ f '' (U ∩ sphere ζ ρ) := by
  rintro w ⟨hwcl, hwU⟩
  rw [closure_image_inter_sphere_eq_union_biUnion_clusterSetOn
    (hfd.continuousOn.mono inter_subset_left)] at hwcl
  rcases hwcl with hw | hw
  · exact hw
  · obtain ⟨e, he, hwe⟩ := mem_iUnion₂.mp hw
    have hfr := (clusterSetOn_inter_sphere_subset_frontier_inter_closure_image hUo hfd hinj he.1
      hwe).1
    rw [(isOpen_image_of_differentiableOn_of_injOn hUo hfd hinj).frontier_eq] at hfr
    exact absurd hwU hfr.2

/-- **A part of the domain avoiding the cutting circle has image disjoint from the closed image
crosscut.** This is `TauCeti.closure_image_inter_sphere_inter_image_subset` read through
injectivity: a common point would be the image both of a point of `V` and of a point of the circle,
hence of a single point lying on both. -/
theorem disjoint_image_closure_image_inter_sphere (hUo : IsOpen U) (hfd : DifferentiableOn ℂ f U)
    (hinj : InjOn f U) {V : Set ℂ} (hVU : V ⊆ U) (hV : Disjoint V (sphere ζ ρ)) :
    Disjoint (f '' V) (closure (f '' (U ∩ sphere ζ ρ))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨z, hzV, rfl⟩ hcl
  obtain ⟨w, hw, hfw⟩ := closure_image_inter_sphere_inter_image_subset hUo hfd hinj
    ⟨hcl, mem_image_of_mem f (hVU hzV)⟩
  have hzw : z = w := hinj (hVU hzV) hw.1 hfw.symm
  exact Set.disjoint_left.mp hV hzV (hzw ▸ hw.2)

/-! ## One of the two sides of a crosscut is inside -/

/-- The near side of a circular crosscut avoids the cutting circle. -/
private lemma disjoint_inter_ball_sphere : Disjoint (ball c r ∩ ball ζ ρ) (sphere ζ ρ) :=
  Set.disjoint_left.mpr fun _ ha hb => absurd (mem_sphere.mp hb) (ne_of_lt (mem_ball.mp ha.2))

/-- The far side of a circular crosscut avoids the cutting circle. -/
private lemma disjoint_sdiff_closedBall_sphere :
    Disjoint (ball c r \ closedBall ζ ρ) (sphere ζ ρ) :=
  Set.disjoint_left.mpr fun _ ha hb =>
    ha.2 (mem_closedBall.mpr (le_of_eq (mem_sphere.mp hb)))

/-- **One of the two sides of a crosscut has its image inside the Jordan curve closing the image
crosscut.** Let `f` be a conformal map of a disc, let `ρ` be a genuine crosscut radius at a boundary
point `ζ`, and let `J` be a Jordan curve containing the closed image crosscut and contained in it
together with the boundary of the image domain — the curve
`TauCeti.exists_isJordanCurve_superset_closure_image_ball_inter_sphere_diam_le_of_isBounded`
produces. If every point of `J` is a limit of points of `filledHull J \ J`, then the image of one of
the two sides of the crosscut lies in `filledHull J`.

The hypothesis `hJsep` is the plane-separation input discussed in the module docstring; it is used
only at a single point of the image crosscut, to place a point of `filledHull J \ J` inside the
image domain. That point lies on one of the two sides, and the side it lies on is preconnected and
disjoint from `J`, hence is swept into `filledHull J` by
`TauCeti.IsPreconnected.subset_filledHull`. -/
theorem subset_filledHull_or_subset_filledHull (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (hfd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) {J : Set ℂ}
    (hJcross : closure (f '' (ball c r ∩ sphere ζ ρ)) ⊆ J)
    (hJsub : J ⊆ closure (f '' (ball c r ∩ sphere ζ ρ)) ∪ frontier (f '' ball c r))
    (hJsep : J ⊆ closure (filledHull J \ J)) :
    f '' (ball c r ∩ ball ζ ρ) ⊆ filledHull J ∨
      f '' (ball c r \ closedBall ζ ρ) ⊆ filledHull J := by
  have hΩo : IsOpen (f '' ball c r) :=
    isOpen_image_of_differentiableOn_of_injOn isOpen_ball hfd hinj
  have hfrdisj : Disjoint (f '' ball c r) (frontier (f '' ball c r)) := by
    rw [Set.disjoint_right]
    intro a ha
    rw [hΩo.frontier_eq] at ha
    exact ha.2
  have hdisj : ∀ V : Set ℂ, V ⊆ ball c r → Disjoint V (sphere ζ ρ) → Disjoint (f '' V) J := by
    intro V hVU hV
    refine Disjoint.mono_right hJsub ?_
    rw [disjoint_union_right]
    exact ⟨disjoint_image_closure_image_inter_sphere isOpen_ball hfd hinj hVU hV,
      hfrdisj.mono_left (image_mono hVU)⟩
  -- A point of the image crosscut, and a point inside `J` in the image domain next to it.
  obtain ⟨z₀, hz₀⟩ : (ball c r ∩ sphere ζ ρ).Nonempty := by
    refine ⟨circleMap ζ ρ (c - ζ).arg, ?_, circleMap_mem_sphere ζ hρ.le _⟩
    rw [circleMap_mem_ball_iff hζ hρ]
    simpa using hρr
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hΩo (f z₀) (mem_image_of_mem f hz₀.1)
  obtain ⟨q, hqball, hqin⟩ := mem_closure_iff.mp
    (hJsep (hJcross (subset_closure (mem_image_of_mem f hz₀)))) (ball (f z₀) δ) isOpen_ball
    (mem_ball_self hδ)
  obtain ⟨z, hz, rfl⟩ := hball hqball
  have hzns : dist z ζ ≠ ρ := fun h =>
    hqin.2 (hJcross (subset_closure (mem_image_of_mem f ⟨hz, mem_sphere.mpr h⟩)))
  rcases lt_or_gt_of_ne hzns with hlt | hgt
  · exact Or.inl (IsPreconnected.subset_filledHull
      (((convex_ball c r).inter (convex_ball ζ ρ)).isPreconnected.image f
        (hfd.continuousOn.mono inter_subset_left))
      (hdisj _ inter_subset_left disjoint_inter_ball_sphere)
      ⟨f z, mem_image_of_mem f ⟨hz, mem_ball.mpr hlt⟩, hqin.1⟩)
  · exact Or.inr (IsPreconnected.subset_filledHull
      ((isConnected_ball_diff_closedBall hζ hρ hρr).isPreconnected.image f
        (hfd.continuousOn.mono sdiff_subset))
      (hdisj _ sdiff_subset disjoint_sdiff_closedBall_sphere)
      ⟨f z, mem_image_of_mem f ⟨hz, fun h => absurd (mem_closedBall.mp h) (not_le.mpr hgt)⟩,
        hqin.1⟩)

/-! ## The crosscut neighbourhood is small -/

/-- **A conformal map of a disc onto a Jordan domain oscillates arbitrarily little on small crosscut
neighbourhoods.** For every tolerance there is a crosscut radius at which the image of the crosscut
neighbourhood at a prescribed boundary point has diameter below it.

The Jordan curve `J` closing a short image crosscut is chosen smaller than the fixed distance
`dist (f c) (f (c + r / 2))`, which the far side realises for every crosscut radius below `r / 2`;
so of the two sides that `TauCeti.subset_filledHull_or_subset_filledHull` offers, only the near one
can lie inside `J`, and it is then no wider than `J` by
`TauCeti.diam_le_diam_of_subset_filledHull`. -/
theorem exists_diam_image_ball_inter_ball_le (hζ : dist ζ c = r) (hr : 0 < r)
    (hfd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) (hfr : IsJordanCurve (frontier (f '' ball c r)))
    (hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (filledHull J \ J)) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, diam (f '' (ball c r ∩ ball ζ ρ)) ≤ ε := by
  -- Two points of the disc that no crosscut of radius below `r / 2` separates from each other.
  set z₀ : ℂ := c + (r / 2 : ℝ) with hz₀def
  have hrle : (0 : ℝ) ≤ r := hr.le
  have hz₀c : dist z₀ c = r / 2 := by
    simp [hz₀def, dist_eq_norm, hrle]
  have hz₀ball : z₀ ∈ ball c r := by rw [mem_ball, hz₀c]; linarith
  have hcball : c ∈ ball c r := mem_ball_self hr
  have hne : f c ≠ f z₀ := fun h => by
    have : dist z₀ c = 0 := by rw [← hinj hcball hz₀ball h]; simp
    rw [hz₀c] at this
    linarith
  set d : ℝ := dist (f c) (f z₀) with hddef
  have hd0 : 0 < d := dist_pos.mpr hne
  obtain ⟨ρ, hρIoo, hρ2r, J, hJc, hJ1, hJ2, -, hJdiam⟩ :=
    exists_isJordanCurve_superset_closure_image_ball_inter_sphere_diam_le_of_isBounded hζ hr hfd
      hinj hb hfr (ε := min ε (d / 2)) (R := r / 2) (lt_min hε (by linarith)) (by linarith)
  have hJb : IsBounded J := hJc.isCompact.isBounded
  rcases subset_filledHull_or_subset_filledHull hζ hρIoo.1 hρ2r hfd hinj hJ1 hJ2 (hsep J hJc) with
    h | h
  · exact ⟨ρ, hρIoo.1, (diam_le_diam_of_subset_filledHull hJb hJc.nonempty h).trans
      (hJdiam.trans (min_le_left _ _))⟩
  · -- The far side is too wide to be the inside one.
    exfalso
    have hρr : ρ < r := lt_trans hρIoo.2 (by linarith)
    have hcnot : c ∉ closedBall ζ ρ := by
      simp only [mem_closedBall, dist_comm c ζ, hζ, not_le]
      exact hρr
    have hz₀not : z₀ ∉ closedBall ζ ρ := by
      have htri : dist ζ c ≤ dist ζ z₀ + dist z₀ c := dist_triangle ζ z₀ c
      rw [hζ, hz₀c] at htri
      simp only [mem_closedBall, dist_comm z₀ ζ, not_le]
      linarith [hρIoo.2]
    have h1 : d ≤ diam (f '' (ball c r \ closedBall ζ ρ)) :=
      dist_le_diam_of_mem (hb.subset (image_mono sdiff_subset))
        (mem_image_of_mem f ⟨hcball, hcnot⟩) (mem_image_of_mem f ⟨hz₀ball, hz₀not⟩)
    have h2 : diam (f '' (ball c r \ closedBall ζ ρ)) ≤ diam J :=
      diam_le_diam_of_subset_filledHull hJb hJc.nonempty h
    have h3 : diam J ≤ d / 2 := hJdiam.trans (min_le_right _ _)
    linarith

/-! ## The boundary limit and the continuous extension -/

/-- **A conformal map of a disc onto a Jordan domain has at most one boundary value at each point of
the circle.** The oscillation criterion `TauCeti.subsingleton_clusterSetOn_of_forall_exists` fed by
`TauCeti.exists_diam_image_ball_inter_ball_le`. -/
theorem subsingleton_clusterSetOn_ball_of_forall_subset_closure_filledHull_sdiff
    (hζ : dist ζ c = r) (hr : 0 < r) (hfd : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hb : IsBounded (f '' ball c r))
    (hfr : IsJordanCurve (frontier (f '' ball c r)))
    (hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (filledHull J \ J)) :
    (clusterSetOn f (ball c r) ζ).Subsingleton := by
  refine subsingleton_clusterSetOn_of_forall_exists fun ε hε => ?_
  obtain ⟨ρ, hρ, hdiam⟩ := exists_diam_image_ball_inter_ball_le hζ hr hfd hinj hb hfr hsep hε
  exact ⟨ρ, hρ, fun _ hx _ hy => (dist_le_diam_of_mem (hb.subset (image_mono inter_subset_left))
    (mem_image_of_mem f hx) (mem_image_of_mem f hy)).trans hdiam⟩

/-- **The Carathéodory continuity theorem for a Jordan domain, modulo plane separation.** A
conformal map of a disc whose image is bounded with Jordan-curve boundary extends continuously to
the closed disc, provided every Jordan curve of the plane is approached from inside — the
separation statement discussed in the module docstring, which is the one input the argument still
takes on trust.

Nothing is claimed here about injectivity of the extension, which is the independent second half of
the boundary correspondence; the converse direction, that an injective continuous extension makes
the domain a Jordan domain, is `TauCeti.isJordanDomain_of_isJordanCurve_frontier_image` of
`Conformal/JordanDomain.lean`. -/
theorem exists_continuousOn_closedBall_eqOn_of_forall_subset_closure_filledHull_sdiff (hr : 0 < r)
    (hfd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) (hfr : IsJordanCurve (frontier (f '' ball c r)))
    (hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (filledHull J \ J)) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closedBall c r) ∧ EqOn F f (ball c r) := by
  have h := exists_continuousOn_closure_eqOn_of_isBounded isOpen_ball hfd.continuousOn hb
    fun w hw => subsingleton_clusterSetOn_ball_of_forall_subset_closure_filledHull_sdiff
      (mem_sphere.mp (by rwa [frontier_ball c hr.ne'] at hw)) hr hfd hinj hb hfr hsep
  rwa [closure_ball c hr.ne'] at h

end TauCeti
