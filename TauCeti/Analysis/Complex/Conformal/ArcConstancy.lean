/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Removability.Circle
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Boundary uniqueness across a circular arc

A holomorphic function on a disc that extends continuously to an *arc* of the bounding circle and
is constant there is constant on the whole disc. Here an arc is `V ∩ sphere c r` for an open
`V ⊆ ℂ` meeting the circle — a relatively open, nonempty piece of the boundary — and no hypothesis
whatever is placed on the function along the rest of the circle.

The proof is Painlevé removability, not the identity principle applied to the boundary: the
boundary values are a set with no limit point *inside* the disc, so no uniqueness statement about
the disc alone can see them. Instead the function is continued past the arc by the trivial branch.
On a small ball `Ω` centred at a point of the arc, glue `f - a` inside the closed disc to the
constant `0` outside it. The two branches agree on `Ω ∩ sphere c r`, which is exactly the frontier
of the closed disc met by `Ω`, so the glued function is continuous on `Ω`; it is holomorphic off
the circle; and `TauCeti.differentiableOn_of_continuousOn_of_differentiableOn_diff_sphere` — the
circle case of Painlevé removability from `Conformal/Removability/Circle.lean` — makes it
holomorphic on all of `Ω`. It vanishes identically on the part of `Ω` outside the closed disc,
which is open and nonempty because `Ω` straddles the circle, so the identity principle kills it on
`Ω` and hence on the nonempty open set `Ω ∩ ball c r`; a second application of the identity
principle, this time inside `ball c r`, propagates `f = a` to the whole disc.

The point of the statement is its contrapositive for injective maps: a conformal map of the disc
that extends continuously to the closed disc is constant on *no* boundary arc, so each of its
boundary fibres has empty interior in the circle. That is the input that layer **L5** of the
conformal-mapping roadmap needs for boundary injectivity — the hypothesis
`TauCeti.injOn_closure_of_injOn_frontier` runs on, and which
`Conformal/ClusterSet.lean` records as not yet available. Carathéodory's argument identifying two
boundary points of a Jordan domain proceeds by producing an arc on which the extension is constant
and contradicting exactly the theorem proved here.

## Main results

* `TauCeti.eqOn_const_ball_of_eqOn_const_arc` — a holomorphic function continuous up to a boundary
  arc and constant on it is constant on the disc.
* `TauCeti.eqOn_ball_of_eqOn_arc` — the two-function form: holomorphic functions agreeing on a
  boundary arc agree on the disc.
* `TauCeti.not_eqOn_const_arc_of_injOn` — a conformal map is constant on no boundary arc.
* `TauCeti.interior_setOf_eq_eq_empty_of_injOn` — equivalently, each boundary fibre of a conformal
  map of the disc has empty interior in the circle.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and the
pinned Mathlib has neither a boundary uniqueness theorem of this shape nor Painlevé removability.
So this file is new Lean formalization rather than a temporary shim; it consumes only the L4
removability layer, which is likewise new.

## References

* L. V. Ahlfors, *Complex Analysis*, Ch. 6, §1.4 (the reflection and removability circle of ideas).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Ch. 2.
* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
-/

public section

namespace TauCeti

open Complex Metric Set Topology

variable {a c : ℂ} {r : ℝ} {V : Set ℂ} {f g : ℂ → ℂ}

/-- Distance from the centre `c` to the point of the ray through `w` at parameter `t`. -/
private lemma dist_radialPoint_center (c w : ℂ) (t : ℝ) :
    dist (c + (t : ℂ) * (w - c)) c = |t| * dist w c := by
  rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_eq_abs]

/-- Distance from `w` to the point of the ray from `c` through `w` at parameter `t`. -/
private lemma dist_radialPoint_self (c w : ℂ) (t : ℝ) :
    dist (c + (t : ℂ) * (w - c)) w = |t - 1| * dist w c := by
  have h : c + (t : ℂ) * (w - c) - w = ((t - 1 : ℝ) : ℂ) * (w - c) := by push_cast; ring
  rw [dist_eq_norm, h, norm_mul, Complex.norm_real, Real.norm_eq_abs, dist_eq_norm]

/-- Every ball centred at a point of a positive-radius sphere straddles that sphere: it meets both
the open ball and the complement of the closed ball. Both witnesses are taken on the radius
through the centre of the small ball, one just inside and one just outside. -/
private lemma exists_mem_ball_of_mem_sphere {c w : ℂ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hw : w ∈ sphere c r) :
    (∃ z ∈ ball w δ, z ∈ ball c r) ∧ ∃ z ∈ ball w δ, z ∉ closedBall c r := by
  have hr' : r ≠ 0 := hr.ne'
  have hwc : dist w c = r := hw
  set ε : ℝ := min (δ / (2 * r)) (1 / 2)
  have hε0 : 0 < ε := lt_min (by positivity) (by norm_num)
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  have hεδ : ε * r < δ := by
    have h1 : ε * r ≤ δ / (2 * r) * r := mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le
    have h2 : δ / (2 * r) * r = δ / 2 := by field_simp
    rw [h2] at h1
    linarith
  constructor
  · refine ⟨c + ((1 - ε : ℝ) : ℂ) * (w - c), ?_, ?_⟩
    · rw [mem_ball, dist_radialPoint_self, hwc]
      have : |(1 - ε) - 1| = ε := by rw [show (1 - ε) - 1 = -ε by ring, abs_neg, abs_of_pos hε0]
      rw [this]
      exact hεδ
    · rw [mem_ball, dist_radialPoint_center, hwc, abs_of_pos (by linarith)]
      nlinarith
  · refine ⟨c + ((1 + ε : ℝ) : ℂ) * (w - c), ?_, ?_⟩
    · rw [mem_ball, dist_radialPoint_self, hwc]
      have : |(1 + ε) - 1| = ε := by rw [show (1 + ε) - 1 = ε by ring, abs_of_pos hε0]
      rw [this]
      exact hεδ
    · rw [mem_closedBall, not_le, dist_radialPoint_center, hwc, abs_of_pos (by linarith)]
      nlinarith

/-- **Boundary uniqueness across a circular arc.** Let `f` be holomorphic on `ball c r`, continuous
up to the part of the closed disc lying in an open set `V`, and equal to the constant `a` on the
arc `V ∩ sphere c r`. If that arc is nonempty, then `f` is the constant `a` on the whole disc.

No hypothesis is placed on `f` along the rest of the circle: the arc alone determines the function.
The proof continues `f - a` past the arc by `0` and applies Painlevé removability across the
circle, then the identity principle twice; see the module docstring. -/
theorem eqOn_const_ball_of_eqOn_const_arc (hr : 0 < r) (hV : IsOpen V)
    (hcont : ContinuousOn f (V ∩ closedBall c r)) (hdiff : DifferentiableOn ℂ f (ball c r))
    (harc : EqOn f (fun _ => a) (V ∩ sphere c r)) (hne : (V ∩ sphere c r).Nonempty) :
    EqOn f (fun _ => a) (ball c r) := by
  classical
  obtain ⟨w, hwV, hwS⟩ := hne
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV w hwV
  set Ω : Set ℂ := ball w δ
  have hΩo : IsOpen Ω := isOpen_ball
  set G : ℂ → ℂ := (closedBall c r).piecewise (fun z => f z - a) 0 with hGdef
  -- The two branches agree on the circle, so the glued function is continuous on `Ω`.
  have hGcont : ContinuousOn G Ω := by
    refine ContinuousOn.piecewise (fun z hz => ?_) ?_ ?_
    · have hzS : z ∈ V ∩ sphere c r :=
        ⟨hδV hz.1, by rw [frontier_closedBall c hr.ne'] at hz; exact hz.2⟩
      simp [harc hzS]
    · rw [isClosed_closedBall.closure_eq]
      exact (hcont.mono (inter_subset_inter_left _ hδV)).sub continuousOn_const
    · exact continuousOn_const
  -- Off the circle each branch is holomorphic in its own right.
  have hGdiff : DifferentiableOn ℂ G (Ω \ sphere c r) := by
    intro z hz
    have hzne : dist z c ≠ r := fun h => hz.2 (mem_sphere.mpr h)
    rcases lt_or_gt_of_ne hzne with hlt | hgt
    · have hzb : z ∈ ball c r := mem_ball.mpr hlt
      have hev : G =ᶠ[𝓝 z] fun y => f y - a := by
        filter_upwards [isOpen_ball.mem_nhds hzb] with y hy
        exact Set.piecewise_eq_of_mem _ _ _ (ball_subset_closedBall hy)
      have hfd : DifferentiableAt ℂ f z := (hdiff z hzb).differentiableAt (isOpen_ball.mem_nhds hzb)
      exact ((hfd.sub_const a).congr_of_eventuallyEq hev).differentiableWithinAt
    · have hzc : z ∈ (closedBall c r)ᶜ := by
        simp only [mem_compl_iff, mem_closedBall, not_le]
        exact hgt
      have hev : G =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hzc] with y hy
        exact Set.piecewise_eq_of_notMem _ _ _ hy
      exact ((differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq hev).differentiableWithinAt
  have hGan : AnalyticOnNhd ℂ G Ω :=
    (differentiableOn_of_continuousOn_of_differentiableOn_diff_sphere hr hΩo hGcont
      hGdiff).analyticOnNhd hΩo
  obtain ⟨⟨z₀, hz₀Ω, hz₀in⟩, z₁, hz₁Ω, hz₁out⟩ := exists_mem_ball_of_mem_sphere hr hδ hwS
  -- The glued function vanishes on the outside part of `Ω`, hence on all of `Ω`.
  have hGzero : EqOn G 0 Ω := by
    refine hGan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball w δ).isPreconnected
      hz₁Ω ?_
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hz₁out] with y hy
    exact Set.piecewise_eq_of_notMem _ _ _ hy
  -- So `f` is the constant `a` near an interior point of `Ω`, and the identity principle finishes.
  have hfz₀ : f =ᶠ[𝓝 z₀] fun _ => a := by
    filter_upwards [(hΩo.inter isOpen_ball).mem_nhds ⟨hz₀Ω, hz₀in⟩] with y hy
    have hy0 := hGzero hy.1
    rw [hGdef, Set.piecewise_eq_of_mem _ _ _ (ball_subset_closedBall hy.2)] at hy0
    simpa [sub_eq_zero] using hy0
  exact (hdiff.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (convex_ball c r).isPreconnected hz₀in hfz₀

/-- **Boundary uniqueness on an arc, two-function form.** Holomorphic functions on `ball c r` that
extend continuously to a nonempty boundary arc `V ∩ sphere c r` and agree there agree on the whole
disc. This is `TauCeti.eqOn_const_ball_of_eqOn_const_arc` applied to the difference. -/
theorem eqOn_ball_of_eqOn_arc (hr : 0 < r) (hV : IsOpen V)
    (hfc : ContinuousOn f (V ∩ closedBall c r)) (hgc : ContinuousOn g (V ∩ closedBall c r))
    (hfd : DifferentiableOn ℂ f (ball c r)) (hgd : DifferentiableOn ℂ g (ball c r))
    (harc : EqOn f g (V ∩ sphere c r)) (hne : (V ∩ sphere c r).Nonempty) :
    EqOn f g (ball c r) := by
  have h : EqOn (fun z => f z - g z) (fun _ => 0) (ball c r) :=
    eqOn_const_ball_of_eqOn_const_arc hr hV (hfc.sub hgc) (hfd.sub hgd)
      (fun z hz => by simpa [sub_eq_zero] using harc hz) hne
  intro z hz
  simpa [sub_eq_zero] using h hz

/-- **A conformal map is constant on no boundary arc.** If `f` is holomorphic and injective on
`ball c r` and continuous up to a nonempty boundary arc `V ∩ sphere c r`, it takes no value
constantly on that arc.

Were it constant there, `TauCeti.eqOn_const_ball_of_eqOn_const_arc` would make it constant on the
disc, which has more than one point. This is the boundary non-degeneracy that layer L5 of the
conformal-mapping roadmap needs: Carathéodory's identification of two boundary points of a Jordan
domain is contradicted by exactly this statement. -/
theorem not_eqOn_const_arc_of_injOn (hr : 0 < r) (hV : IsOpen V)
    (hcont : ContinuousOn f (V ∩ closedBall c r)) (hdiff : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hne : (V ∩ sphere c r).Nonempty) (a : ℂ) :
    ¬ EqOn f (fun _ => a) (V ∩ sphere c r) := by
  intro harc
  have hconst := eqOn_const_ball_of_eqOn_const_arc hr hV hcont hdiff harc hne
  have hc : c ∈ ball c r := mem_ball_self hr
  have hc' : c + ((r / 2 : ℝ) : ℂ) ∈ ball c r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  have heq : c = c + ((r / 2 : ℝ) : ℂ) := hinj hc hc' (by rw [hconst hc, hconst hc'])
  have hzero : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination -heq
  exact absurd (Complex.ofReal_eq_zero.mp hzero) (by linarith)

/-- **The boundary fibres of a conformal map contain no arc.** For `f` holomorphic and injective on
`ball c r` and continuous on the closed disc, the set of boundary points at which `f` takes a fixed
value has empty interior in the circle.

This is the relative-topology packaging of `TauCeti.not_eqOn_const_arc_of_injOn`: a nonempty open
subset of `sphere c r` is precisely a nonempty arc `V ∩ sphere c r` for an open `V ⊆ ℂ`. -/
theorem interior_setOf_eq_eq_empty_of_injOn (hr : 0 < r) (hcont : ContinuousOn f (closedBall c r))
    (hdiff : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) (a : ℂ) :
    interior {z : sphere c r | f (z : ℂ) = a} = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨u, hu, hsub⟩ := (mem_nhds_subtype _ z _).mp (mem_interior_iff_mem_nhds.mp hz)
  obtain ⟨V, hVu, hVo, hzV⟩ := _root_.mem_nhds_iff.mp hu
  refine not_eqOn_const_arc_of_injOn hr hVo (hcont.mono inter_subset_right) hdiff hinj
    ⟨z, hzV, z.2⟩ a fun y hy => ?_
  exact hsub (show ((⟨y, hy.2⟩ : sphere c r) : ℂ) ∈ u from hVu hy.1)

end TauCeti
