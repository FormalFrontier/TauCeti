/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Crosscut.Inside
public import TauCeti.Analysis.Complex.Conformal.Crosscut.SmallJordanCurve
public import TauCeti.Analysis.Complex.Conformal.RiemannMapping.Existence
public import TauCeti.Topology.ClusterSet
import TauCeti.Analysis.Complex.Conformal.Crosscut.Basic
import TauCeti.Analysis.Normed.Module.Ball.Cut
import TauCeti.Topology.MetricSpace.Cut

/-!
# Carathéodory's continuity theorem, on plane separation

A conformal map of a disc onto a bounded region whose boundary is a Jordan curve extends
continuously to the closed disc. This file proves that statement from one unproved input, the
**plane separation** statement of the roadmap section of `TauCeti/Topology/FilledHull.lean`,

> every point of a Jordan curve is a limit of points inside it, `J ⊆ closure (filledHull J \ J)`,

carried through every theorem below as the explicit hypothesis

> `hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (filledHull J \ J)`.

Nothing else is assumed: `hsep` is the *only* hypothesis here that the repository does not
discharge, and no theorem below is stated in a shape that presumes anything further. What the file
therefore establishes is that plane separation is the last gate on the continuity half of layer
**L5**, and that the gate is a statement about Jordan curves alone — no longer one about conformal
maps, crosscuts or boundary behaviour.

## The argument

Fix a point `ζ` of the bounding circle and a tolerance `ε`. The **crosscut neighbourhoods**
`ball c r ∩ ball ζ ρ` shrink to `ζ`, so by the Cauchy criterion
`TauCeti.subsingleton_clusterSetOn_of_forall_exists` it is enough to make the image of one of them
have diameter at most `ε`. Four inputs combine to do that, at a radius `ρ` chosen by the
length–area method:

* **a small curve along the crosscut.**
  `TauCeti.exists_isJordanCurve_superset_closure_image_ball_inter_sphere_diam_le_of_isBounded`
  produces, at some radius `ρ` below any prescribed bound, a Jordan curve `J` of diameter at most
  `ε` containing the closed image crosscut and running back along the image boundary;
* **the far side stays wide.** `TauCeti.exists_pos_forall_le_diam_image_sdiff_closedBall`, applied
  at the point `ζ` off the disc, gives a `d > 0` below which the image of the far side
  `ball c r \ closedBall ζ ρ` never shrinks, for every small `ρ`; taking `J` narrower than `d` makes
  it narrower than the far side;
* **both sides of the cut are connected.** The near side `ball c r ∩ ball ζ ρ` is an intersection of
  two discs, hence convex (`TauCeti.isConnected_ball_inter_ball`); the far side
  `ball c r \ closedBall ζ ρ` is connected by the Möbius reduction
  `TauCeti.isConnected_ball_diff_closedBall`;
* **the curve has a point of its inside on the image crosscut.** The circular crosscut
  `ball c r ∩ sphere ζ ρ` is nonempty (`TauCeti.nonempty_ball_inter_sphere`), its image lies on `J`,
  and it lies in the image of the disc; `hsep` is read at that one point, and only there.

`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt` then puts the *near* side inside
`filledHull J` — the far side cannot be the enclosed one, being wider than `J` — and
`TauCeti.diam_le_diam_of_subset_filledHull` reads that enclosure as the width bound
`diam (f '' (ball c r ∩ ball ζ ρ)) ≤ diam J ≤ ε`. Since this holds at every boundary point, the
extension theorem `TauCeti.exists_continuousOn_closure_eqOn_of_isBounded` assembles the continuous
extension on `closedBall c r`.

## What is not claimed

**Injectivity of the extension is not established**, and no statement below asserts it: the L5
milestone asks for a homeomorphism of the closures, and this file supplies only the continuous
extension. Given injectivity on the bounding circle, `TauCeti.closureHomeomorph` of
`Conformal/BoundaryCorrespondence.lean` upgrades the extension to that homeomorphism, and
`TauCeti.injOn_closure_of_injOn_frontier` of `Conformal/ClusterSet.lean` reduces injectivity on the
closed disc to injectivity on the circle; producing the latter is a separate Jordan-curve argument
whose analytic half is `TauCeti.not_eqOn_const_inter_sphere_of_injOn` of
`Conformal/ArcConstancy.lean`.

Nor is the *converse* route through `Conformal/Crosscut/BoundarySplit.lean` taken: the enclosure
route used here asks only that the near side fall inside a small curve, whereas that route asks
which arc of the image boundary the near side clings to.

## Roadmap role

This is layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, the Jordan-domain case of the
Carathéodory boundary correspondence, reduced to its one open frontier item. `ConformalMapping`'s
status record names plane separation for Jordan curves as that item and asks that *how much of it
the boundary work needs* be settled first; the answer this file gives is `hsep`, at a single point
of a single curve at each radius.

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, and Mathlib has no boundary correspondence for
conformal maps and no Jordan curve theorem, so this is new Lean formalization rather than a
temporary shim.

## Main results

* `TauCeti.exists_diam_image_ball_inter_ball_le_of_isJordanCurve_frontier` — the crosscut
  neighbourhoods at a boundary point have images of arbitrarily small diameter.
* `TauCeti.subsingleton_clusterSetOn_of_isJordanCurve_frontier` and
  `TauCeti.exists_tendsto_nhdsWithin_of_isJordanCurve_frontier` — such a map has at most one
  boundary cluster value at each point of the bounding circle, hence a boundary limit there.
* `TauCeti.exists_continuousOn_closedBall_eqOn_of_isJordanCurve_frontier` — **Carathéodory's
  continuity theorem**: it extends continuously to the closed disc.
* `TauCeti.exists_continuousOn_closedBall_bijOn_ball_of_isJordanCurve_frontier` — the form the
  milestone is stated in: a bounded simply connected domain with Jordan-curve boundary is the
  image of the disc under a holomorphic bijection continuous up to the closed disc.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913), 305–320.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Theorem 2.1 and §2.2–2.3.
* P. L. Duren, *Univalent Functions*, Theorem 3.1.
-/

public section

namespace TauCeti

open Bornology Complex Filter Metric Set Topology

variable {f : ℂ → ℂ} {c ζ : ℂ} {r : ℝ}

/-! ## The crosscut neighbourhoods have small images -/

/-- **The image of a crosscut neighbourhood can be made arbitrarily small.** Let `f` be holomorphic
and injective on `ball c r`, with bounded image whose boundary is a Jordan curve, and let `ζ` lie on
the bounding circle. Assuming the plane-separation statement `hsep`, for every `ε > 0` there is a
crosscut radius `ρ > 0` with

> `Metric.diam (f '' (ball c r ∩ ball ζ ρ)) ≤ ε`.

This is the quantitative heart of the file, and the only place `hsep` is used: it is read once, at
the image of a point of the circular crosscut `ball c r ∩ sphere ζ ρ`, which lies both on the small
curve `J` and in the image of the disc. The inputs the enclosure theorem
`TauCeti.image_inter_ball_subset_filledHull_of_diam_lt` isolates — connectedness of each of the two
sides of the cut, nonemptiness of the crosscut, and a far side wider than `J` — are all discharged
here. -/
theorem exists_diam_image_ball_inter_ball_le_of_isJordanCurve_frontier
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) (hJf : IsJordanCurve (frontier (f '' ball c r)))
    (hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (filledHull J \ J))
    (hζ : dist ζ c = r) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, diam (f '' (ball c r ∩ ball ζ ρ)) ≤ ε := by
  -- the image of the disc has two distinct points, so the far side does not degenerate
  have hhalf : (0 : ℝ) < r / 2 := by linarith
  have hc : c ∈ ball c r := mem_ball_self hr
  have hc' : c + ((r / 2 : ℝ) : ℂ) ∈ ball c r := by
    simp only [mem_ball, dist_self_add_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hhalf]
    linarith
  have hne : c ≠ c + ((r / 2 : ℝ) : ℂ) := by simp [hr.ne']
  have hnotsub : ¬ (f '' ball c r).Subsingleton := fun h =>
    hne (hinj hc hc' (h (mem_image_of_mem f hc) (mem_image_of_mem f hc')))
  have hζball : ζ ∉ ball c r := by simp [mem_ball, hζ]
  obtain ⟨d, hd, ρ₀, hρ₀, hfar⟩ :=
    exists_pos_forall_le_diam_image_sdiff_closedBall hnotsub hζball hb
  -- a small Jordan curve along the image crosscut, narrower than half the far-side width
  obtain ⟨ρ, hρmem, hρr, J, hJ, hcl, hJsub, -, hdiamJ⟩ :=
    exists_isJordanCurve_superset_closure_image_ball_inter_sphere_diam_le_of_isBounded
      hζ hr hf hinj hb hJf (lt_min hε (half_pos hd)) hρ₀
  refine ⟨ρ, hρmem.1, ?_⟩
  have hJb : IsBounded J := hJ.isCompact.isBounded
  have hγ : f '' (ball c r ∩ sphere ζ ρ) ⊆ J := subset_closure.trans hcl
  have hlt : diam J < diam (f '' (ball c r \ closedBall ζ ρ)) := by
    have h₁ : diam J ≤ d / 2 := hdiamJ.trans (min_le_right _ _)
    have h₂ := hfar ρ hρmem.2.le
    linarith
  -- the separation hypothesis, read at the image of one point of the circular crosscut
  obtain ⟨z, hz⟩ := nonempty_ball_inter_sphere hζ hρmem.1 hρr
  have hp : f z ∈ f '' ball c r := mem_image_of_mem f hz.1
  have hin : f z ∈ closure (filledHull J \ J) := hsep J hJ (hγ (mem_image_of_mem f hz))
  have hAc : IsPreconnected (ball c r ∩ ball ζ ρ) :=
    (isConnected_ball_inter_ball hr hρmem.1
      (by rw [dist_comm, hζ]; linarith [hρmem.1])).isPreconnected
  have hBc : IsPreconnected (ball c r \ closedBall ζ ρ) :=
    (isConnected_ball_diff_closedBall hζ hρmem.1 hρr).isPreconnected
  calc diam (f '' (ball c r ∩ ball ζ ρ))
      ≤ diam J := diam_le_diam_of_subset_filledHull hJb
        (image_inter_ball_subset_filledHull_of_diam_lt isOpen_ball hf hinj hAc hBc hJb hγ
          hJsub hlt hp hin)
    _ ≤ ε := hdiamJ.trans (min_le_left _ _)

/-! ## The boundary limit -/

/-- **Such a map has at most one cluster value at each point of the bounding circle.** The Cauchy
criterion `TauCeti.subsingleton_clusterSetOn_of_forall_exists` applied to the width bound of
`TauCeti.exists_diam_image_ball_inter_ball_le_of_isJordanCurve_frontier`: two points of a crosscut
neighbourhood have images within its diameter of each other by `Metric.dist_le_diam_of_mem`. -/
theorem subsingleton_clusterSetOn_of_isJordanCurve_frontier
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) (hJf : IsJordanCurve (frontier (f '' ball c r)))
    (hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (filledHull J \ J))
    (hζ : dist ζ c = r) :
    (clusterSetOn f (ball c r) ζ).Subsingleton := by
  refine subsingleton_clusterSetOn_of_forall_exists fun ε hε => ?_
  obtain ⟨ρ, hρ, hdiam⟩ :=
    exists_diam_image_ball_inter_ball_le_of_isJordanCurve_frontier hr hf hinj hb hJf hsep hζ hε
  exact ⟨ρ, hρ, fun _ hx _ hy => (dist_le_diam_of_mem
    (hb.subset (image_mono inter_subset_left))
    (mem_image_of_mem f hx) (mem_image_of_mem f hy)).trans hdiam⟩

/-- **Such a map has a boundary limit at each point of the bounding circle.** The values of `f`
converge as the argument approaches `ζ` from inside the disc.

The cluster set at `ζ` is a subsingleton by
`TauCeti.subsingleton_clusterSetOn_of_isJordanCurve_frontier`, and it is nonempty because `f` maps
the disc into the compact closure of its bounded image, which is what
`TauCeti.exists_tendsto_of_clusterSetOn_subsingleton` needs; `Metric.closure_ball` puts `ζ` in the
closure of the disc. This is the pointwise form of
`TauCeti.exists_continuousOn_closedBall_eqOn_of_isJordanCurve_frontier`, and names the limit. -/
theorem exists_tendsto_nhdsWithin_of_isJordanCurve_frontier
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) (hJf : IsJordanCurve (frontier (f '' ball c r)))
    (hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (filledHull J \ J))
    (hζ : dist ζ c = r) :
    ∃ v, Tendsto f (𝓝[ball c r] ζ) (𝓝 v) :=
  exists_tendsto_of_clusterSetOn_subsingleton hb.isCompact_closure
    (fun w hw => subset_closure ⟨w, hw, rfl⟩)
    (by rw [closure_ball c hr.ne']; exact mem_closedBall.mpr hζ.le)
    (subsingleton_clusterSetOn_of_isJordanCurve_frontier hr hf hinj hb hJf hsep hζ)

/-- **Carathéodory's continuity theorem, on plane separation.** A holomorphic injection of a disc
onto a bounded region whose boundary is a Jordan curve extends continuously to the closed disc,
granted the plane-separation statement `hsep`.

Every boundary cluster set is a subsingleton by
`TauCeti.subsingleton_clusterSetOn_of_isJordanCurve_frontier`, which is exactly what the extension
theorem `TauCeti.exists_continuousOn_closure_eqOn_of_isBounded` asks of a map into a proper space
with bounded image; `Metric.frontier_ball` and `Metric.closure_ball` turn its `frontier` and
`closure` into the circle and the closed disc.

No injectivity is claimed for the extension on the circle, and none is needed for continuity. -/
theorem exists_continuousOn_closedBall_eqOn_of_isJordanCurve_frontier
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) (hJf : IsJordanCurve (frontier (f '' ball c r)))
    (hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (filledHull J \ J)) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closedBall c r) ∧ EqOn F f (ball c r) := by
  have h := exists_continuousOn_closure_eqOn_of_isBounded isOpen_ball hf.continuousOn hb
    fun w hw => subsingleton_clusterSetOn_of_isJordanCurve_frontier hr hf hinj hb hJf hsep
      (mem_sphere.mp (by rwa [frontier_ball c hr.ne'] at hw))
  rwa [closure_ball c hr.ne'] at h

/-! ## The Jordan-domain form -/

/-- **A bounded Jordan domain is the image of the disc under a holomorphic bijection continuous up
to the closed disc**, granted the plane-separation statement `hsep`. This is the form layer **L5**
of `TauCetiRoadmap/ConformalMapping/README.md` states its milestone in, minus the injectivity of the
boundary values.

The Riemann mapping theorem, in the shape
`TauCeti.exists_bijOn_ball_differentiableOn_invFunOn`, supplies a holomorphic bijection of `Ω` onto
the disc with holomorphic inverse; the inverse is the map extended. That `Ω` is a proper subset of
`ℂ` needs no separate hypothesis, `frontier univ` being empty while a Jordan curve is not. Simple
connectivity is a hypothesis and not a consequence of the boundary being a Jordan curve: deducing it
is the Schoenflies theorem, which this development does not have.

The extension is named as the map itself rather than beside it: replacing the inverse Riemann map by
its extension changes neither its holomorphy on the open disc nor its bijectivity onto `Ω`. -/
theorem exists_continuousOn_closedBall_bijOn_ball_of_isJordanCurve_frontier {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩb : IsBounded Ω)
    (hΩJ : IsJordanCurve (frontier Ω))
    (hsep : ∀ J : Set ℂ, IsJordanCurve J → J ⊆ closure (filledHull J \ J)) :
    ∃ g : ℂ → ℂ, ContinuousOn g (closedBall 0 1) ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn g (ball 0 1) Ω := by
  have hΩne : Ω ≠ univ := by
    rintro rfl
    rw [frontier_univ] at hΩJ
    exact not_nonempty_empty hΩJ.nonempty
  obtain ⟨φ, hφ, -, hgd, -, -⟩ :=
    exists_bijOn_ball_differentiableOn_invFunOn hΩo hΩc hΩne
  have hgbij : BijOn (Function.invFunOn φ Ω) (ball 0 1) Ω :=
    BijOn.symm hφ.invOn_invFunOn.symm hφ
  have himg : Function.invFunOn φ Ω '' ball 0 1 = Ω := hgbij.image_eq
  have hb : IsBounded (Function.invFunOn φ Ω '' ball 0 1) := by rw [himg]; exact hΩb
  have hJ : IsJordanCurve (frontier (Function.invFunOn φ Ω '' ball 0 1)) := by
    rw [himg]; exact hΩJ
  obtain ⟨G, hGc, hGeq⟩ :=
    exists_continuousOn_closedBall_eqOn_of_isJordanCurve_frontier one_pos hgd hgbij.injOn hb hJ
      hsep
  exact ⟨G, hGc, hgd.congr fun _ hz => hGeq hz, hgbij.congr fun _ hz => (hGeq hz).symm⟩

end TauCeti
