/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Crosscut.Inside
public import TauCeti.Analysis.Complex.Conformal.Crosscut.SmallJordanCurve
public import TauCeti.Analysis.Complex.Conformal.JordanDomain
public import TauCeti.Topology.ClusterSet
import TauCeti.Analysis.Complex.Conformal.Crosscut.Endpoints
import TauCeti.Analysis.Normed.Module.Ball.Cut

/-!
# A conditional near-side reduction for boundary continuity

Let `f` be a conformal map of a disc `ball c r` onto a bounded domain `Ω = f '' ball c r` whose
frontier is a Jordan curve, and cut the disc at a point `ζ` of its bounding circle by the circle
`sphere ζ ρ`. This file assembles the crosscut machinery of the surrounding directory into the
conditional reduction toward layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md` — the
Jordan-domain case of the Carathéodory boundary correspondence. Under the plane-separation input
spelled out below, at every point of the bounding circle the *near side*
`f '' (ball c r ∩ ball ζ ρ)` can be made arbitrarily narrow by taking `ρ` small, so `f` has a limit
at every boundary point and extends continuously to `closedBall c r`.

This file does not establish the unconditional L5 theorem. One input is not proved: that a Jordan
curve `J` is a limit of points of its inside,
`J ⊆ closure (filledHull J \ J)`. It is carried as an explicit hypothesis, asked only of the
Jordan curves that lie in `closure Ω`. Everything else the argument needs is discharged here.

## What was already available, and what is added

`Conformal/Crosscut/SmallJordanCurve.lean` produces, at every prescribed tolerance and radius
bound, a genuine crosscut whose closed image lies on a Jordan curve `J ⊆ closure Ω` of diameter at
most the tolerance, running from the image crosscut along `frontier Ω`.
`Conformal/Crosscut/Inside.lean` turns such a curve into a bound on the near side
(`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt`), but only against four further data,
which it lists and does not supply:

* both sides of the cut preconnected — the near side by convexity
  (`TauCeti.isConnected_ball_inter_ball`) and the far side by the Möbius reduction
  (`TauCeti.isConnected_ball_diff_closedBall`), both already available for a circular crosscut of a
  disc;
* a point of the image domain on the curve — the image of any point of the crosscut, which is
  nonempty because the crosscut reaches the bounding circle
  (`TauCeti.nonempty_frontier_ball_inter_closure_ball_inter_sphere`);
* the *far* side strictly wider than the curve, so that it is the near side and not the far one
  that the curve encloses. This is the quantitative input, and it is what
  `TauCeti.exists_pos_forall_le_diam_image_sdiff_closedBall` of
  `TauCeti/Topology/MetricSpace/Cut.lean` supplies: two points of the disc survive in the far side
  once `ρ` is small, so the far side keeps the fixed width `d > 0` between their images. Running
  the small-curve construction at tolerance `min ε (d / 2)` and radius bound the corresponding
  `ρ₀` makes the comparison automatic;
* the inside statement at that point, which is the hypothesis carried through.

With those in place the near side is enclosed by `J` and hence, by
`TauCeti.diam_le_diam_of_subset_filledHull`, no wider than it. That is
`TauCeti.exists_diam_image_ball_inter_ball_le`, and the rest of the file is its standard
consequences: the crosscut neighbourhoods form a neighbourhood basis of `ζ` in the disc, so a
width bound at every tolerance is a Cauchy criterion, and
`TauCeti.subsingleton_clusterSetOn_of_forall_exists` of `TauCeti/Topology/ClusterSet.lean` turns it
into a one-point cluster set, a boundary limit and — the hypothesis being uniform in `ζ` — a
continuous extension to the closed disc.

## What the remaining hypothesis is

The hypothesis is

> `∀ J, IsJordanCurve J → J ⊆ closure Ω → J ⊆ closure (filledHull J \ J)`,

the statement recorded as the open frontier item in the roadmap section of
`TauCeti/Topology/FilledHull.lean`: *every point of a Jordan curve is a limit of points inside it*,
the inside of `J` being `filledHull J \ J`. It is a theorem of plane topology — a consequence of
the Jordan curve theorem together with the accessibility of the boundary of a complementary
component — and it is the only part of plane separation the forward direction of the continuity
theorem turns out to consume, which is what `ConformalMapping/STATUS.md` asks to have settled
before separation is attacked. It is not an empty hypothesis: for the model Jordan curve, a
circle, it is `TauCeti.sphere_subset_closure_filledHull_sphere_sdiff` of
`TauCeti/Analysis/Normed/Module/FilledHull.lean`, where it needs no separation theory at all.
Nothing here weakens the conditional conclusion in exchange: the theorems below isolate the one
remaining plane-separation prerequisite for the continuity half of the L5 milestone. They do not
claim that milestone unconditionally; once the prerequisite is proved separately, their conclusion
has the form `Conformal/BoundaryCorrespondence.lean` packages into a boundary homeomorphism.

## Generality

The domain is a disc, not an arbitrary open set: the crosscut geometry — the two sides of a
circular cut being connected, the cut reaching the boundary — is a fact about a disc cut at a point
of its bounding circle, and the disc is the side a Riemann map is defined on. The image is asked
only to be bounded with Jordan-curve frontier, which is `TauCeti.IsJordanDomain` and is how the
final corollary states it. In accordance with the generality bar of `ConformalMapping/README.md`
every statement is for scalar `ℂ`.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and the
pinned Mathlib has neither a boundary correspondence for conformal maps nor any Jordan-curve
vocabulary. So this is new Lean formalization rather than a temporary shim.

## Main results

* `TauCeti.exists_diam_image_ball_inter_ball_le` — some crosscut neighbourhood of a boundary point
  has image of diameter at most any prescribed tolerance.
* `TauCeti.subsingleton_clusterSetOn_ball_of_isJordanCurve_frontier` — the cluster set of the map
  at a boundary point of the disc has at most one element.
* `TauCeti.exists_tendsto_nhdsWithin_ball_of_isJordanCurve_frontier` — the map has a limit at every
  point of the bounding circle.
* `TauCeti.exists_continuousOn_closedBall_eqOn_of_isJordanCurve_frontier` and
  `TauCeti.IsJordanDomain.exists_continuousOn_closedBall_eqOn_image` — the map extends continuously
  to the closed disc.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2–2.3.
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open Bornology Complex Filter Metric Set Topology

variable {f : ℂ → ℂ} {c ζ : ℂ} {r : ℝ}

/-! ## The near side of a small crosscut is narrow -/

/-- **A crosscut neighbourhood with narrow image.** Let `f` be holomorphic and injective on
`ball c r`, with bounded image whose frontier is a Jordan curve, and let `ζ` lie on the bounding
circle. If every Jordan curve inside `closure (f '' ball c r)` is a limit of points of its inside,
then for every `ε > 0` some crosscut radius `ρ > 0` has

> `diam (f '' (ball c r ∩ ball ζ ρ)) ≤ ε`.

The tolerance handed to the small-Jordan-curve theorem
`TauCeti.exists_isJordanCurve_superset_closure_image_ball_inter_sphere_diam_le_of_isBounded` is
`min ε (d / 2)`, where `d` is the width the far side keeps at every radius below `ρ₀`, and the
radius bound handed to it is `ρ₀`. Both roles of the tolerance are then discharged at once: the
resulting Jordan curve `J` is narrower than `ε`, and strictly narrower than the far side, so by
`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt` it encloses the near side rather than the
far one. -/
theorem exists_diam_image_ball_inter_ball_le (hζ : dist ζ c = r) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r))
    (hfrontier : IsJordanCurve (frontier (f '' ball c r)))
    (hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (f '' ball c r) →
      J ⊆ closure (filledHull J \ J))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, diam (f '' (ball c r ∩ ball ζ ρ)) ≤ ε := by
  have hζball : ζ ∉ ball c r := by simp [mem_ball, hζ]
  have hns : ¬ (ball c r).Subsingleton := by
    rw [not_subsingleton_iff]
    refine ⟨c, mem_ball_self hr, c + ((r / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < r / 2)]
      linarith
    · simpa using (by positivity : (r / 2 : ℝ) ≠ 0)
  obtain ⟨d, hd, ρ₀, hρ₀, hfar⟩ :=
    exists_pos_forall_le_diam_image_sdiff_closedBall hns hζball hinj hb
  obtain ⟨ρ, hρ, hρr, J, hJ, hJcross, hJup, hJcl, hJdiam⟩ :=
    exists_isJordanCurve_superset_closure_image_ball_inter_sphere_diam_le_of_isBounded hζ hr hf
      hinj hb hfrontier (lt_min hε (by linarith : (0 : ℝ) < d / 2)) hρ₀
  have hγ : f '' (ball c r ∩ sphere ζ ρ) ⊆ J := subset_closure.trans hJcross
  have hJb : IsBounded J := hJ.isCompact.isBounded
  have hlt : diam J < diam (f '' (ball c r \ closedBall ζ ρ)) := by
    have h₁ := hfar ρ hρ.2.le
    have h₂ : min ε (d / 2) ≤ d / 2 := min_le_right _ _
    linarith
  obtain ⟨z, hz⟩ : (ball c r ∩ sphere ζ ρ).Nonempty :=
    Set.Nonempty.of_closure
      (Set.Nonempty.mono inter_subset_right
        (nonempty_frontier_ball_inter_closure_ball_inter_sphere hζ hρ.1 hρr))
  refine ⟨ρ, hρ.1, ?_⟩
  calc
    diam (f '' (ball c r ∩ ball ζ ρ)) ≤ diam J :=
      diam_le_diam_of_subset_filledHull hJb
        (image_inter_ball_subset_filledHull_of_diam_lt isOpen_ball hf hinj
          (isConnected_ball_inter_ball hr hρ.1 (by rw [dist_comm, hζ]; linarith [hρ.1])
            |>.isPreconnected)
          (isConnected_ball_diff_closedBall hζ hρ.1 hρr).isPreconnected hJb hγ hJup hlt
          (mem_image_of_mem f hz.1) (hsep J hJ hJcl (hγ (mem_image_of_mem f hz))))
    _ ≤ min ε (d / 2) := hJdiam
    _ ≤ ε := min_le_left _ _

/-! ## The boundary limit and the continuous extension -/

/-- **The cluster set at a boundary point of the disc is a subsingleton.** The crosscut
neighbourhoods `ball c r ∩ ball ζ ρ` are the approach regions the Cauchy criterion
`TauCeti.subsingleton_clusterSetOn_of_forall_exists` runs on, and
`TauCeti.exists_diam_image_ball_inter_ball_le` makes their images narrow at every tolerance;
`Metric.dist_le_diam_of_mem` reads a width bound as a bound on the distance between two values. -/
theorem subsingleton_clusterSetOn_ball_of_isJordanCurve_frontier (hζ : dist ζ c = r) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r))
    (hfrontier : IsJordanCurve (frontier (f '' ball c r)))
    (hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (f '' ball c r) →
      J ⊆ closure (filledHull J \ J)) :
    (clusterSetOn f (ball c r) ζ).Subsingleton := by
  refine subsingleton_clusterSetOn_of_forall_exists fun ε hε => ?_
  obtain ⟨ρ, hρ, hdiam⟩ :=
    exists_diam_image_ball_inter_ball_le hζ hr hf hinj hb hfrontier hsep hε
  exact ⟨ρ, hρ, fun x hx y hy =>
    (dist_le_diam_of_mem (hb.subset (image_mono inter_subset_left))
      (mem_image_of_mem f hx) (mem_image_of_mem f hy)).trans hdiam⟩

/-- **A conformal map of a disc onto a bounded Jordan-curve-bounded domain has a limit at every
point of the bounding circle.** The cluster set at `ζ` is a subsingleton by
`TauCeti.subsingleton_clusterSetOn_ball_of_isJordanCurve_frontier`, and it is nonempty because the
map takes the disc into the compact closure of its bounded image, which is what
`TauCeti.exists_tendsto_of_clusterSetOn_subsingleton` needs. -/
theorem exists_tendsto_nhdsWithin_ball_of_isJordanCurve_frontier (hζ : dist ζ c = r) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r))
    (hfrontier : IsJordanCurve (frontier (f '' ball c r)))
    (hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (f '' ball c r) →
      J ⊆ closure (filledHull J \ J)) :
    ∃ v, Tendsto f (𝓝[ball c r] ζ) (𝓝 v) :=
  exists_tendsto_of_clusterSetOn_subsingleton hb.isCompact_closure
    (fun w hw => subset_closure ⟨w, hw, rfl⟩)
    (by rw [closure_ball c hr.ne']; exact mem_closedBall.mpr hζ.le)
    (subsingleton_clusterSetOn_ball_of_isJordanCurve_frontier hζ hr hf hinj hb hfrontier hsep)

/-- **The continuity theorem for a conformal map of a disc, modulo the inside statement.** A
holomorphic injection of `ball c r` with bounded image whose frontier is a Jordan curve extends
continuously to `closedBall c r`, provided every Jordan curve inside the closure of the image is a
limit of points of its inside.

The hypothesis of `TauCeti.exists_continuousOn_closure_eqOn_of_isBounded` — a subsingleton cluster
set at every point of `frontier (ball c r) = sphere c r` — is
`TauCeti.subsingleton_clusterSetOn_ball_of_isJordanCurve_frontier` read at each such point, the
inside hypothesis being uniform in the point. Nothing is claimed about injectivity of the
extension, which is the independent second half of the boundary correspondence. -/
theorem exists_continuousOn_closedBall_eqOn_of_isJordanCurve_frontier (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r))
    (hfrontier : IsJordanCurve (frontier (f '' ball c r)))
    (hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (f '' ball c r) →
      J ⊆ closure (filledHull J \ J)) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closedBall c r) ∧ EqOn F f (ball c r) := by
  have h := exists_continuousOn_closure_eqOn_of_isBounded isOpen_ball hf.continuousOn hb
    fun w hw => subsingleton_clusterSetOn_ball_of_isJordanCurve_frontier
      (by rw [frontier_ball c hr.ne'] at hw; exact mem_sphere.mp hw) hr hf hinj hb hfrontier hsep
  rwa [closure_ball c hr.ne'] at h

/-- **The continuity theorem, stated for a Jordan domain, modulo the inside statement.** A
conformal map of a disc onto a Jordan domain extends continuously to the closed disc. This is
`TauCeti.exists_continuousOn_closedBall_eqOn_of_isJordanCurve_frontier` with the two hypotheses on
the image — boundedness and a Jordan-curve frontier — read off `TauCeti.IsJordanDomain`.

Composed with `TauCeti.bijOn_closure_closure_image` of `Conformal/BoundaryCorrespondence.lean`,
which upgrades a continuous extension that is injective on the closure to a homeomorphism of the
closures, this is the shape the L5 milestone of `TauCetiRoadmap/ConformalMapping/README.md` asks
for. -/
theorem IsJordanDomain.exists_continuousOn_closedBall_eqOn_image (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hΩ : IsJordanDomain (f '' ball c r))
    (hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (f '' ball c r) →
      J ⊆ closure (filledHull J \ J)) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closedBall c r) ∧ EqOn F f (ball c r) :=
  exists_continuousOn_closedBall_eqOn_of_isJordanCurve_frontier hr hf hinj hΩ.isBounded
    hΩ.isJordanCurve_frontier hsep

end TauCeti
