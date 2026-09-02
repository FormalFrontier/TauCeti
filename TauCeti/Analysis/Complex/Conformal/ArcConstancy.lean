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

A holomorphic function on a disc that extends continuously to a relatively open piece of the
bounding circle and is constant there is constant on the whole disc. That piece is
`V ∩ sphere c r` for an open `V ⊆ ℂ` meeting the circle, and no hypothesis whatever is placed on
the function along the rest of the circle. Nothing forces `V ∩ sphere c r` to be connected, so the
declarations are named after that literal hypothesis, `inter_sphere`; the prose below calls such a
set a boundary *arc*, the case of interest, but no arc parameterization is assumed.

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

The point of the statement is its contrapositive: a function that is *not* the constant `a` on the
disc is not the constant `a` on any boundary arc, so — for an injective map, which is constant
nowhere — every boundary fibre has empty interior in the circle.

## What this does and does not supply towards L5

This is a prerequisite for layer **L5** of the conformal-mapping roadmap, not that layer's
boundary-injectivity step. Carathéodory's proof that the extension of a Riemann map of a Jordan
domain is injective on `frontier` argues by contradiction in two halves: two identified boundary
points cut the circle into two arcs, and the Jordan-curve geometry of the image forces the
extension to be constant on one of them; that constancy is then impossible. Only the second half
is proved here. Producing the constant arc from an identification of two boundary points is a
Jordan-curve argument about the image, and is **not** proved here, nor is the singleton
cluster-set property that produces the continuous extension in the first place —
`Conformal/ClusterSet.lean` records both as still missing, which is why
`TauCeti.injOn_closure_of_injOn_frontier` there carries boundary injectivity as a hypothesis. So no
boundary-injectivity claim is discharged by this file; what it adds is the analytic
non-degeneracy input that the missing step will consume.

The L5 milestone is now complete via `Conformal/Jordan/Approach.lean`, which takes the
Janiszewski route (preconnected approach regions) rather than the classical two-arc argument,
so this file's analytic input is consumed through a different path than described above.

## Main results

* `TauCeti.eqOn_const_ball_of_eqOn_const_inter_sphere` — a holomorphic function continuous up to a
  boundary arc and constant on it is constant on the disc.
* `TauCeti.eqOn_ball_of_eqOn_inter_sphere` — the two-function form: holomorphic functions agreeing
  on a boundary arc agree on the disc.
* `TauCeti.not_eqOn_const_inter_sphere_of_not_eqOn_const_ball` and
  `TauCeti.interior_setOf_eq_eq_empty_of_not_eqOn_const_ball` — the contrapositive, for a function
  that is not that constant on the disc, in the two forms.
* `TauCeti.not_eqOn_const_inter_sphere_of_injOn` and
  `TauCeti.interior_setOf_eq_eq_empty_of_injOn` — the roadmap-facing corollaries for a conformal
  map, which is constant on no boundary arc and each of whose boundary fibres therefore has empty
  interior in the circle.

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

/-- Every ball centred at a point of a positive-radius sphere straddles that sphere: it meets both
the open ball and the complement of the closed ball. The sphere is the frontier of each of those
two discs, and a frontier point lies in the closure of the set as well as of its complement. -/
private lemma exists_mem_ball_of_mem_sphere {c w : ℂ} {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hw : w ∈ sphere c r) :
    (∃ z ∈ ball w δ, z ∈ ball c r) ∧ ∃ z ∈ ball w δ, z ∉ closedBall c r := by
  have hin : w ∈ closure (ball c r) :=
    frontier_subset_closure (by rwa [frontier_ball c hr.ne'])
  have hout : w ∈ closure (closedBall c r)ᶜ := by
    have hfr : w ∈ frontier (closedBall c r) := by rwa [frontier_closedBall c hr.ne']
    rw [frontier_eq_closure_inter_closure] at hfr
    exact hfr.2
  constructor
  · obtain ⟨z, hz, hwz⟩ := Metric.mem_closure_iff.mp hin δ hδ
    exact ⟨z, mem_ball.mpr (by rwa [dist_comm]), hz⟩
  · obtain ⟨z, hz, hwz⟩ := Metric.mem_closure_iff.mp hout δ hδ
    exact ⟨z, mem_ball.mpr (by rwa [dist_comm]), hz⟩

/-- The function glued from `f - a` inside the closed disc and from `0` outside it is continuous on
any ball contained in `V`: the two branches agree along the circle, which is the frontier of the
closed disc, and there `f` is the constant `a` by hypothesis. -/
private lemma continuousOn_piecewise_sub_const {w : ℂ} {δ : ℝ}
    [∀ z, Decidable (z ∈ closedBall c r)] (hr : r ≠ 0) (hδV : ball w δ ⊆ V)
    (hcont : ContinuousOn f (V ∩ closedBall c r))
    (harc : EqOn f (fun _ => a) (V ∩ sphere c r)) :
    ContinuousOn ((closedBall c r).piecewise (fun z => f z - a) 0) (ball w δ) := by
  refine ContinuousOn.piecewise (fun z hz => ?_) ?_ ?_
  · have hzS : z ∈ V ∩ sphere c r :=
      ⟨hδV hz.1, by rw [frontier_closedBall c hr] at hz; exact hz.2⟩
    simp [harc hzS]
  · rw [isClosed_closedBall.closure_eq]
    exact (hcont.mono (inter_subset_inter_left _ hδV)).sub continuousOn_const
  · exact continuousOn_const

/-- Off the circle the glued function is holomorphic in its own right: near an interior point it
agrees with `f - a`, and near an exterior point with `0`. Only holomorphy of `f` on the open disc
is used — neither continuity up to the boundary nor the boundary values play any role here. -/
private lemma differentiableOn_piecewise_sub_const_compl_sphere
    [∀ z, Decidable (z ∈ closedBall c r)] (hdiff : DifferentiableOn ℂ f (ball c r)) :
    DifferentiableOn ℂ ((closedBall c r).piecewise (fun z => f z - a) 0) (sphere c r)ᶜ := by
  intro z hz
  have hzne : dist z c ≠ r := fun h => hz (mem_sphere.mpr h)
  rcases lt_or_gt_of_ne hzne with hlt | hgt
  · have hzb : z ∈ ball c r := mem_ball.mpr hlt
    have hev : (closedBall c r).piecewise (fun z => f z - a) 0 =ᶠ[𝓝 z] fun y => f y - a := by
      filter_upwards [isOpen_ball.mem_nhds hzb] with y hy
      exact Set.piecewise_eq_of_mem _ _ _ (ball_subset_closedBall hy)
    have hfd : DifferentiableAt ℂ f z := (hdiff z hzb).differentiableAt (isOpen_ball.mem_nhds hzb)
    exact ((hfd.sub_const a).congr_of_eventuallyEq hev).differentiableWithinAt
  · have hzc : z ∈ (closedBall c r)ᶜ := by
      simp only [mem_compl_iff, mem_closedBall, not_le]
      exact hgt
    have hev : (closedBall c r).piecewise (fun z => f z - a) 0 =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hzc] with y hy
      exact Set.piecewise_eq_of_notMem _ _ _ hy
    exact ((differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq hev).differentiableWithinAt

/-- **The local step of boundary uniqueness.** A single point `w` of the arc already forces `f` to
be the constant `a` on a neighbourhood of *some* interior point of the disc. Which interior point
is not recorded: the conclusion asserts only that one exists.

This is where Painlevé removability enters. On a ball `Ω` around `w` the glued function is
continuous and holomorphic off the circle, hence holomorphic on all of `Ω`; it vanishes on the part
of `Ω` outside the closed disc, which is open and nonempty because `Ω` straddles the circle, so the
identity principle kills it on `Ω`. The interior point produced is one of the points of
`Ω ∩ ball c r`, but only its existence is needed to run the identity principle on the disc. -/
private lemma exists_mem_ball_eventuallyEq_const (hr : 0 < r) (hV : IsOpen V)
    (hcont : ContinuousOn f (V ∩ closedBall c r)) (hdiff : DifferentiableOn ℂ f (ball c r))
    (harc : EqOn f (fun _ => a) (V ∩ sphere c r)) {w : ℂ} (hwV : w ∈ V) (hwS : w ∈ sphere c r) :
    ∃ z₀ ∈ ball c r, f =ᶠ[𝓝 z₀] fun _ => a := by
  classical
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV w hwV
  set G : ℂ → ℂ := (closedBall c r).piecewise (fun z => f z - a) 0 with hGdef
  have hΩo : IsOpen (ball w δ) := isOpen_ball
  have hGan : AnalyticOnNhd ℂ G (ball w δ) :=
    (differentiableOn_of_continuousOn_of_differentiableOn_diff_sphere hr hΩo
      (continuousOn_piecewise_sub_const hr.ne' hδV hcont harc)
      ((differentiableOn_piecewise_sub_const_compl_sphere hdiff).mono
        fun _ hz => hz.2)).analyticOnNhd hΩo
  obtain ⟨⟨z₀, hz₀Ω, hz₀in⟩, z₁, hz₁Ω, hz₁out⟩ := exists_mem_ball_of_mem_sphere hr hδ hwS
  have hGzero : EqOn G 0 (ball w δ) := by
    refine hGan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball w δ).isPreconnected
      hz₁Ω ?_
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hz₁out] with y hy
    exact Set.piecewise_eq_of_notMem _ _ _ hy
  refine ⟨z₀, hz₀in, ?_⟩
  filter_upwards [(hΩo.inter isOpen_ball).mem_nhds ⟨hz₀Ω, hz₀in⟩] with y hy
  have hy0 := hGzero hy.1
  rw [hGdef, Set.piecewise_eq_of_mem _ _ _ (ball_subset_closedBall hy.2)] at hy0
  simpa [sub_eq_zero] using hy0

/-- **Boundary uniqueness across a circular arc.** Let `f` be holomorphic on `ball c r`, continuous
up to the part of the closed disc lying in an open set `V`, and equal to the constant `a` on the
arc `V ∩ sphere c r`. If that arc is nonempty, then `f` is the constant `a` on the whole disc.

No hypothesis is placed on `f` along the rest of the circle: the arc alone determines the function.
The proof continues `f - a` past the arc by `0` and applies Painlevé removability across the
circle, then the identity principle twice; see the module docstring. -/
theorem eqOn_const_ball_of_eqOn_const_inter_sphere (hr : 0 < r) (hV : IsOpen V)
    (hcont : ContinuousOn f (V ∩ closedBall c r)) (hdiff : DifferentiableOn ℂ f (ball c r))
    (harc : EqOn f (fun _ => a) (V ∩ sphere c r)) (hne : (V ∩ sphere c r).Nonempty) :
    EqOn f (fun _ => a) (ball c r) := by
  obtain ⟨w, hwV, hwS⟩ := hne
  obtain ⟨z₀, hz₀in, hfz₀⟩ :=
    exists_mem_ball_eventuallyEq_const hr hV hcont hdiff harc hwV hwS
  exact (hdiff.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (convex_ball c r).isPreconnected hz₀in hfz₀

/-- **Boundary uniqueness on an arc, two-function form.** Holomorphic functions on `ball c r` that
extend continuously to a nonempty boundary arc `V ∩ sphere c r` and agree there agree on the whole
disc. This is `TauCeti.eqOn_const_ball_of_eqOn_const_inter_sphere` applied to the difference. -/
theorem eqOn_ball_of_eqOn_inter_sphere (hr : 0 < r) (hV : IsOpen V)
    (hfc : ContinuousOn f (V ∩ closedBall c r)) (hgc : ContinuousOn g (V ∩ closedBall c r))
    (hfd : DifferentiableOn ℂ f (ball c r)) (hgd : DifferentiableOn ℂ g (ball c r))
    (harc : EqOn f g (V ∩ sphere c r)) (hne : (V ∩ sphere c r).Nonempty) :
    EqOn f g (ball c r) := by
  have h : EqOn (fun z => f z - g z) (fun _ => 0) (ball c r) :=
    eqOn_const_ball_of_eqOn_const_inter_sphere hr hV (hfc.sub hgc) (hfd.sub hgd)
      (fun z hz => by simpa [sub_eq_zero] using harc hz) hne
  intro z hz
  simpa [sub_eq_zero] using h hz

/-- **A function nonconstant on the disc is constant on no boundary arc.** If `f` is holomorphic on
`ball c r`, continuous up to a nonempty boundary arc `V ∩ sphere c r`, and is not the constant `a`
on the disc, then it is not the constant `a` on that arc.

This is the contrapositive of `TauCeti.eqOn_const_ball_of_eqOn_const_inter_sphere`; injectivity of
`f` is not needed, only its failure to be this one constant. -/
theorem not_eqOn_const_inter_sphere_of_not_eqOn_const_ball (hr : 0 < r) (hV : IsOpen V)
    (hcont : ContinuousOn f (V ∩ closedBall c r)) (hdiff : DifferentiableOn ℂ f (ball c r))
    (hne : (V ∩ sphere c r).Nonempty) (hnc : ¬ EqOn f (fun _ => a) (ball c r)) :
    ¬ EqOn f (fun _ => a) (V ∩ sphere c r) := fun harc =>
  hnc (eqOn_const_ball_of_eqOn_const_inter_sphere hr hV hcont hdiff harc hne)

/-- **The boundary fibres of a nonconstant function contain no arc.** For `f` holomorphic on
`ball c r`, continuous on the closed disc and not the constant `a` on the disc, the set of boundary
points at which `f` takes the value `a` has empty interior in the circle.

This is the relative-topology packaging of
`TauCeti.not_eqOn_const_inter_sphere_of_not_eqOn_const_ball`: a nonempty open subset of
`sphere c r` is precisely a nonempty arc `V ∩ sphere c r` for an open `V ⊆ ℂ`. -/
theorem interior_setOf_eq_eq_empty_of_not_eqOn_const_ball (hr : 0 < r)
    (hcont : ContinuousOn f (closedBall c r)) (hdiff : DifferentiableOn ℂ f (ball c r))
    (hnc : ¬ EqOn f (fun _ => a) (ball c r)) :
    interior {z : sphere c r | f (z : ℂ) = a} = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨u, hu, hsub⟩ := (mem_nhds_subtype _ z _).mp (mem_interior_iff_mem_nhds.mp hz)
  obtain ⟨V, hVu, hVo, hzV⟩ := _root_.mem_nhds_iff.mp hu
  refine not_eqOn_const_inter_sphere_of_not_eqOn_const_ball hr hVo
    (hcont.mono inter_subset_right) hdiff ⟨z, hzV, z.2⟩ hnc fun y hy => ?_
  have hyu : (⟨y, hy.2⟩ : sphere c r) ∈ Subtype.val ⁻¹' u := Set.mem_preimage.mpr (hVu hy.1)
  exact hsub hyu

/-- An injective function is no constant on the disc: the disc has more than one point. -/
private lemma not_eqOn_const_ball_of_injOn (hr : 0 < r) (hinj : InjOn f (ball c r)) (a : ℂ) :
    ¬ EqOn f (fun _ => a) (ball c r) := by
  intro hconst
  have hc : c ∈ ball c r := mem_ball_self hr
  have hc' : c + ((r / 2 : ℝ) : ℂ) ∈ ball c r := by
    have hd : dist (c + ((r / 2 : ℝ) : ℂ)) c = r / 2 := by
      simp [dist_eq_norm, hr.le]
    rw [mem_ball, hd]
    linarith
  have heq : c = c + ((r / 2 : ℝ) : ℂ) := hinj hc hc' (by rw [hconst hc, hconst hc'])
  have hzero : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination -heq
  exact absurd (Complex.ofReal_eq_zero.mp hzero) (by linarith)

/-- **A conformal map is constant on no boundary arc.** If `f` is holomorphic and injective on
`ball c r` and continuous up to a nonempty boundary arc `V ∩ sphere c r`, it takes no value
constantly on that arc.

This is the roadmap-facing corollary of
`TauCeti.not_eqOn_const_inter_sphere_of_not_eqOn_const_ball`, an injective map being constant
nowhere. It is the boundary non-degeneracy that layer L5 of the conformal-mapping roadmap needs;
see the module docstring for what still separates it from boundary injectivity. -/
theorem not_eqOn_const_inter_sphere_of_injOn (hr : 0 < r) (hV : IsOpen V)
    (hcont : ContinuousOn f (V ∩ closedBall c r)) (hdiff : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hne : (V ∩ sphere c r).Nonempty) (a : ℂ) :
    ¬ EqOn f (fun _ => a) (V ∩ sphere c r) :=
  not_eqOn_const_inter_sphere_of_not_eqOn_const_ball hr hV hcont hdiff hne
    (not_eqOn_const_ball_of_injOn hr hinj a)

/-- **The boundary fibres of a conformal map contain no arc.** For `f` holomorphic and injective on
`ball c r` and continuous on the closed disc, the set of boundary points at which `f` takes a fixed
value has empty interior in the circle.

This is the roadmap-facing corollary of
`TauCeti.interior_setOf_eq_eq_empty_of_not_eqOn_const_ball`. -/
theorem interior_setOf_eq_eq_empty_of_injOn (hr : 0 < r) (hcont : ContinuousOn f (closedBall c r))
    (hdiff : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) (a : ℂ) :
    interior {z : sphere c r | f (z : ℂ) = a} = ∅ :=
  interior_setOf_eq_eq_empty_of_not_eqOn_const_ball hr hcont hdiff
    (not_eqOn_const_ball_of_injOn hr hinj a)

end TauCeti
