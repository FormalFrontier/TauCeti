/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.Analysis.Normed.Module.Ball.Cut
public import TauCeti.Topology.ClusterSet
import TauCeti.Topology.Circle.Metric

/-!
# The circular crosscut of a disc at a boundary point

Fix a disc `ball c r` and a point `ζ` of its boundary circle. For `0 < ρ < 2 * r` the circle
`sphere ζ ρ` meets the disc in an arc, the **circular crosscut** of `ball c r` at `ζ` of radius
`ρ`, and that arc cuts the disc in two: the *crosscut neighbourhood* `ball c r ∩ ball ζ ρ` of `ζ`,
and the rest, `ball c r \ closedBall ζ ρ`. This file proves that decomposition, and then uses the
crosscut neighbourhoods as the approach regions along which the boundary behaviour of a holomorphic
function is read off.

Both halves are needed for layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, the
Carathéodory boundary correspondence: the crosscut neighbourhoods are the regions the length–area
method estimates on, and the criterion below is what converts such an estimate into the continuous
extension the L5 milestone asks for.

## The decomposition

That `ball c r ∩ ball ζ ρ` is connected is immediate — it is an intersection of two balls, hence
convex — and is proved in a seminormed real vector space, together with the rest of what the
crosscut neighbourhood is, in `TauCeti/Analysis/Normed/Module/Ball/Cut.lean`. The other piece is
not convex,
and the proof is the **Möbius reduction** the roadmap
prescribes for circles: the inversion `z ↦ (z - ζ)⁻¹` at the boundary point `ζ` carries the disc to
a half-plane, because a circle through the centre of an inversion goes to a line. Concretely,
writing `a = c - ζ`, a point `z ≠ ζ` lies in `ball c r` exactly when `1 < 2 * (a * (z - ζ)⁻¹).re`
(`TauCeti.mem_ball_iff_one_lt_two_mul_re_mul_inv`): the disc becomes the open half-plane
`{w | 1 < 2 * (a * w).re}`. The inversion simultaneously turns the *complement* of `closedBall ζ ρ`
into the ball `ball 0 ρ⁻¹`, since `‖(z - ζ)⁻¹‖ = ‖z - ζ‖⁻¹`. So `ball c r \ closedBall ζ ρ` is
carried onto an intersection of a half-plane with a ball — convex, and nonempty exactly when
`ρ < 2 * r` — and is therefore connected, being the image of a connected set under the continuous
inverse inversion `w ↦ ζ + w⁻¹`.

The two pieces are open, disjoint and cover `ball c r \ sphere ζ ρ`, so they *are* its connected
components: a circular crosscut separates the disc into exactly two parts, and a connected subset
of the disc missing the crosscut lies entirely in one of them. That the crosscut neighbourhood is
one of the two components is
`TauCeti.connectedComponentIn_ball_diff_sphere_eq_ball_inter_ball` of
`TauCeti/Analysis/Normed/Module/Ball/Cut.lean`, which needs no complex structure; that the other
piece is the other component is
`TauCeti.connectedComponentIn_ball_diff_sphere_eq_ball_diff_closedBall` below, resting on the
Möbius reduction.

## The angular description

Which *angles* the crosscut occupies is settled in `TauCeti/Topology/Circle/Metric.lean`, where
nothing ties the cutting circle to the disc: writing `α = arg (c - ζ)` for the direction from `ζ`
to the centre and `d = dist ζ c`, the law of cosines `TauCeti.dist_circleMap_sq` puts the point of
`sphere ζ ρ` at angle `θ` at distance `ρ ^ 2 + d ^ 2 - 2 * ρ * d * cos (θ - α)`, squared, from `c`,
so it lies in the disc exactly when `ρ ^ 2 + d ^ 2 - r ^ 2 < 2 * ρ * d * cos (θ - α)`
(`TauCeti.circleMap_mem_ball_iff_sq`, with `TauCeti.circleMap_mem_closedBall_iff_sq` beside it),
and that condition holds throughout an interval of angles inside a period centred at `α` as soon
as it holds at both ends (`TauCeti.circleMap_mem_ball_of_mem_Icc`).

What this file adds is the *boundary-point* reading of that criterion, where `d = r`: the two
squared radii cancel and the condition becomes `ρ < 2 * r * cos (θ - α)`
(`TauCeti.circleMap_mem_ball_iff`, with the `simp`-normal form `TauCeti.dist_circleMap_lt_iff`
beside it), so for `0 < ρ < 2 * r` the crosscut consists of the angles *strictly* within
`arccos (ρ / (2 * r))` of `α`, while for `2 * r ≤ ρ` no angle satisfies the condition and
`sphere ζ ρ` misses the disc altogether. Rather than name that half-width, the arc statement is
left in its general form: the crosscut is an arc.

## The boundary criterion

The frontier of the crosscut neighbourhood is contained in the union of two pieces of circle
(`TauCeti.frontier_ball_inter_ball_subset` of `TauCeti/Analysis/Normed/Module/Ball/Cut.lean`, which
asks nothing of the ambient space beyond a pseudo-metric): the arc `closedBall c r ∩ sphere ζ ρ`,
and the cap
`sphere c r ∩ closedBall ζ ρ` cut off on the boundary of the disc. Equality can fail — for
`2 * r ≤ ρ` the crosscut neighbourhood is the whole disc, and its frontier misses the arc — but
containment is all a frontier bound needs. Since the crosscut neighbourhood
is bounded and open, the maximum modulus principle bounds `f` inside it by its values on those two
pieces (`TauCeti.norm_sub_le_of_mem_ball_inter_ball`).

That frontier form is not what a boundary criterion can be built on, because reading `f` on the cap
presupposes that `f` is continuous up to the boundary — and continuity up to the boundary *is* the
conclusion one is after, at `ζ` and everywhere else. So the estimate is re-run on the concentric
subdiscs `ball c s` with `s < r`, on whose closures a function holomorphic on `ball c r` is
automatically continuous, and their crosscut neighbourhoods exhaust `ball c r ∩ ball ζ ρ`. This
gives `TauCeti.norm_sub_le_of_mem_ball_inter_ball_of_differentiableOn`: only holomorphy on the open
disc is assumed, the arc bound is asked for on `ball c r ∩ sphere ζ ρ`, and the cap bound is
replaced by a bound on a *collar* `r₀ ≤ dist w c` of the boundary inside the crosscut
neighbourhood — all of it data about `f` inside the disc. Feeding those oscillation bounds, one for
each tolerance `ε`, to `TauCeti.subsingleton_clusterSetOn_of_forall_exists`, one gets:

> a bounded holomorphic function on a disc has a limit at a boundary point `ζ` as soon as, for
> every `ε > 0`, there is *some* radius `ρ > 0` at which `f` is within `ε` of a single value on
> the part `ball c r ∩ sphere ζ ρ` of the circle around `ζ` inside the disc and on a collar of
> the boundary.

The radius is quantified per `ε`, and need not tend to zero: it is `ε` that shrinks, while `ρ`
(along with the collar and the value approximated) is merely allowed to depend on it. Nor is `ρ`
asked to stay below `2 * r`, so a witness need not describe a circular crosscut: admitting the
larger radii too only weakens the hypothesis, and the crosscut radii the application supplies are
among the admissible ones.

This is `TauCeti.exists_tendsto_nhdsWithin_ball`, and `TauCeti.exists_continuousOn_closedBall_eqOn`
is its global form, a continuous extension to the closed disc. Boundedness alone is far from
sufficient — a bounded holomorphic function need not have a limit at a given boundary point — so
the estimate is what carries the content. Neither injectivity of `f` nor any hypothesis on the
image is used, and supplying that estimate for a Riemann map of a Jordan domain is precisely what
the remaining L5 work consists of. The length–area method delivers the bound on the arc; the bound
on the collar is where local connectedness of the image boundary enters.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything below is stated for `ℂ`. The three set lemmas that
split a set by a sphere use nothing but the containments between balls and spheres, so they live in
`TauCeti/Topology/MetricSpace/Cut.lean`, stated for an arbitrary pseudo-metric space, and are used
here at `ℂ`. Likewise the whole of the *near* side — that the crosscut neighbourhood is nonempty,
connected and a connected component of the cut disc, and the bound on its frontier — needs only
convexity of a ball, or for the frontier bound not even that, so it lives in
`TauCeti/Analysis/Normed/Module/Ball/Cut.lean` for a seminormed real vector space and a
pseudo-metric space respectively, and is used here at `ℂ`. For the rest the bar is not merely a
convenience: the decomposition of the *far* side is performed by the complex inversion
`z ↦ (z - ζ)⁻¹`, the
Möbius map the roadmap names for reducing circles to lines, and the analytic half is the maximum
modulus principle for holomorphic functions.

## Main results

* `TauCeti.mem_ball_iff_one_lt_two_mul_re_mul_inv` — the inversion at a boundary point carries a
  disc to a half-plane.
* `TauCeti.circleMap_mem_ball_iff` — the angular description of a circular crosscut, the
  boundary-point case of the criterion `TauCeti.circleMap_mem_ball_iff_sq` of
  `TauCeti/Topology/Circle/Metric.lean`, which also supplies the fact that the angles form an arc.
* `TauCeti.isConnected_ball_diff_closedBall` — the part of a disc outside a circular crosscut is
  connected.
* `TauCeti.connectedComponentIn_ball_diff_sphere_eq_ball_diff_closedBall` — together with its
  companion `TauCeti.connectedComponentIn_ball_diff_sphere_eq_ball_inter_ball` of
  `TauCeti/Analysis/Normed/Module/Ball/Cut.lean`, a circular crosscut separates the disc into
  exactly two connected components, the two sides being those cut out by
  `TauCeti.sdiff_sphere_eq_inter_ball_union_sdiff_closedBall` and
  `TauCeti.subset_inter_ball_or_subset_sdiff_closedBall` of
  `TauCeti/Topology/MetricSpace/Cut.lean`.
* `TauCeti.norm_sub_le_of_mem_ball_inter_ball` and
  `TauCeti.norm_sub_le_of_mem_ball_inter_ball_of_differentiableOn` — the maximum modulus principle
  on a crosscut neighbourhood: a bound on the arc and on the cap is a bound inside, and its
  boundary-free form, where only holomorphy on the open disc is assumed and the cap is replaced by
  a collar of the boundary.
* `TauCeti.exists_tendsto_nhdsWithin_ball` and `TauCeti.exists_continuousOn_closedBall_eqOn` — the
  crosscut criterion for a boundary limit, and for a continuous extension to the closed disc.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and
Mathlib has no boundary correspondence for conformal maps. So this file is new Lean formalization
rather than a temporary shim, and it consumes no L0–L3 shim: its analytic input is Mathlib's own
maximum modulus principle, `Complex.norm_le_of_forall_mem_frontier_norm_le`.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2 (crosscuts).
-/

public section

namespace TauCeti

open Bornology Complex Filter Metric Set Topology
open scoped Real

variable {c ζ z : ℂ} {r ρ : ℝ}

/-! ## The inversion at a boundary point -/

/-- **The inversion at a boundary point carries a disc to a half-plane.** If `ζ` lies on the circle
`sphere c r`, then a point `z ≠ ζ` lies in `ball c r` exactly when its image `(z - ζ)⁻¹` under the
inversion centred at `ζ` lies in the open half-plane `{w | 1 < 2 * ((c - ζ) * w).re}`.

This is the classical fact that a Möbius map sends a circle through the centre of the inversion to
a line, in the one form the crosscut decomposition needs: which *side* of that line the disc goes
to. The computation is `‖z - c‖ < r ↔ normSq (z - ζ) < 2 * ((z - ζ) * conj (c - ζ)).re`, obtained by
expanding `normSq ((z - ζ) - (c - ζ))` and cancelling `normSq (c - ζ) = r ^ 2`; dividing by
`normSq (z - ζ)` turns the left side into `1` and the right side into the half-plane condition. -/
theorem mem_ball_iff_one_lt_two_mul_re_mul_inv (hζ : dist ζ c = r) (hz : z ≠ ζ) :
    z ∈ ball c r ↔ 1 < 2 * ((c - ζ) * (z - ζ)⁻¹).re := by
  have hu : z - ζ ≠ 0 := sub_ne_zero.mpr hz
  have hns : 0 < normSq (z - ζ) := normSq_pos.mpr hu
  have hr : 0 ≤ r := hζ ▸ dist_nonneg
  have ha : normSq (c - ζ) = r ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, ← norm_neg, neg_sub, ← dist_eq_norm, hζ]
  -- the real part of the inverted point, cleared of its denominator
  have hre : ((c - ζ) * (z - ζ)⁻¹).re * normSq (z - ζ)
      = ((z - ζ) * (starRingEnd ℂ) (c - ζ)).re := by
    have hinv : (z - ζ)⁻¹ * ((normSq (z - ζ) : ℝ) : ℂ) = (starRingEnd ℂ) (z - ζ) := by
      rw [← Complex.mul_conj, inv_mul_cancel_left₀ hu]
    calc ((c - ζ) * (z - ζ)⁻¹).re * normSq (z - ζ)
        = ((c - ζ) * (z - ζ)⁻¹ * ((normSq (z - ζ) : ℝ) : ℂ)).re := by simp [Complex.mul_re]
      _ = ((c - ζ) * (starRingEnd ℂ) (z - ζ)).re := by rw [mul_assoc, hinv]
      _ = ((z - ζ) * (starRingEnd ℂ) (c - ζ)).re := by simp [Complex.mul_re]; ring
  -- the disc, in terms of `normSq`
  have hdisc : z ∈ ball c r ↔ normSq (z - c) < r ^ 2 := by
    rw [mem_ball, dist_eq_norm, Complex.normSq_eq_norm_sq]
    constructor
    · intro h; nlinarith [norm_nonneg (z - c)]
    · intro h; nlinarith [norm_nonneg (z - c)]
  have hsub : z - c = z - ζ - (c - ζ) := by ring
  rw [hdisc, hsub, Complex.normSq_sub, ha]
  rw [← hre]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-! ## The angular description of a circular crosscut -/

/-- **A circular crosscut is an arc of angles around the direction of the centre.** For `ζ` on the
circle `sphere c r` and `ρ > 0`, the point of `sphere ζ ρ` at angle `θ` lies in `ball c r` exactly
when `ρ < 2 * r * cos (θ - arg (c - ζ))`.

This is the general criterion `TauCeti.circleMap_mem_ball_iff_sq` of
`TauCeti/Topology/Circle/Metric.lean` at `dist ζ c = r`, where the two squared radii cancel and the
surviving condition `ρ ^ 2 < 2 * ρ * r * cos (θ - arg (c - ζ))` may be divided by `ρ > 0`.

Nothing is assumed of `r` beyond what `dist ζ c = r` forces; for `r = 0` both sides are false.

This is deliberately not a `simp` lemma: `Metric.mem_ball` already rewrites the left-hand side to
`dist (circleMap ζ ρ θ) c < r`, so the statement is not in `simp` normal form and the `simpNF`
linter rejects the attribute. The `simp`-normal companion is
`TauCeti.dist_circleMap_lt_iff`. -/
theorem circleMap_mem_ball_iff (hζ : dist ζ c = r) (hρ : 0 < ρ) (θ : ℝ) :
    circleMap ζ ρ θ ∈ ball c r ↔ ρ < 2 * r * Real.cos (θ - (c - ζ).arg) := by
  rw [circleMap_mem_ball_iff_sq (hζ ▸ dist_nonneg) ρ θ, hζ]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **A circular crosscut is an arc of angles around the direction of the centre**, stated in
`simp` normal form. This is `TauCeti.circleMap_mem_ball_iff` with the membership in `ball c r`
already unfolded by `Metric.mem_ball`, which is the form a `simp` call leaves the goal in. -/
@[simp]
theorem dist_circleMap_lt_iff (hζ : dist ζ c = r) (hρ : 0 < ρ) (θ : ℝ) :
    dist (circleMap ζ ρ θ) c < r ↔ ρ < 2 * r * Real.cos (θ - (c - ζ).arg) :=
  circleMap_mem_ball_iff hζ hρ θ

/-- Every point of a circle has an angular representative in the period of length `2 * π` centred
at any prescribed angle. This also covers radius zero; a negative-radius sphere is empty. -/
theorem exists_mem_Icc_circleMap_eq (α : ℝ) {z : ℂ} (hz : z ∈ sphere ζ ρ) :
    ∃ t ∈ Icc (-π) π, circleMap ζ ρ (α + t) = z := by
  have hρ : 0 ≤ ρ := Metric.nonneg_of_mem_sphere hz
  have hmem : z ∈ circleMap ζ ρ '' Icc (α - π) (α - π + 2 * π) := by
    rw [(periodic_circleMap ζ ρ).image_Icc Real.two_pi_pos, range_circleMap, abs_of_nonneg hρ]
    exact hz
  obtain ⟨θ, hθ, rfl⟩ := hmem
  refine ⟨θ - α, ?_, by congr 1; ring⟩
  constructor
  · linarith [hθ.1]
  · linarith [hθ.2]

/-! ## The far side of a circular crosscut

The *near* side `ball c r ∩ ball ζ ρ` is convex, and everything about it — that it is nonempty,
connected, and a connected component of the cut disc, and that its frontier lies on the two
circles — is proved without any complex structure in
`TauCeti/Analysis/Normed/Module/Ball/Cut.lean`. What follows is the far side, which is not convex
and is where the Möbius reduction is needed. -/

/-- The inversion model of a disc punctured by a crosscut: the intersection of the open half-plane
`{w | 1 < 2 * (a * w).re}` with `ball 0 R`. It is convex for every `a` and every `R`, being an
intersection of a half-space with a ball.

No nonemptiness is claimed, and none holds in general: the intersection is empty for `R ≤ 0`, and
the half-plane itself is empty for `a = 0`. Nonemptiness in the case at hand is
`TauCeti.nonempty_halfPlane_inter_ball`, which is where `ρ < 2 * r` is used. -/
private lemma convex_halfPlane_inter_ball (a : ℂ) (R : ℝ) :
    Convex ℝ ({w : ℂ | 1 < 2 * (a * w).re} ∩ ball 0 R) := by
  have hlin : IsLinearMap ℝ fun w : ℂ => 2 * (a * w).re :=
    { map_add := by intro x y; simp [mul_add, Complex.mul_re]
      map_smul := by intro s x; simp [Complex.real_smul, Complex.mul_re]; ring }
  exact (convex_halfSpace_gt hlin 1).inter (convex_ball _ _)

/-- A point of the half-plane `{w | 1 < 2 * (a * w).re}` is nonzero, since at `w = 0` the defining
quantity is `0`. The ball factor plays no part. -/
private lemma ne_zero_of_one_lt_two_mul_re_mul {a w : ℂ} (hw : 1 < 2 * (a * w).re) : w ≠ 0 := by
  rintro rfl
  rw [mul_zero, Complex.zero_re] at hw
  linarith

/-- **This is where `ρ < 2 * ‖a‖` is used.** The model region is nonempty exactly because the
crosscut radius is less than the diameter; a larger `ρ` would swallow the disc. The witness is a
real multiple `s / a` with `1 / 2 < s < ‖a‖ / ρ`, which is a nonempty range precisely under that
hypothesis. Neither `0 < ‖a‖` nor `a ≠ 0` is assumed: `0 < ρ < 2 * ‖a‖` forces both. -/
private lemma nonempty_halfPlane_inter_ball {a : ℂ} (hρ : 0 < ρ) (hρ' : ρ < 2 * ‖a‖) :
    ({w : ℂ | 1 < 2 * (a * w).re} ∩ ball 0 ρ⁻¹).Nonempty := by
  have hr : 0 < ‖a‖ := by linarith
  have ha0 : a ≠ 0 := norm_pos_iff.mp hr
  have hhalf : (1 : ℝ) / 2 < ‖a‖ / ρ := by rw [lt_div_iff₀ hρ]; linarith
  obtain ⟨s, hs1, hs2⟩ : ∃ s : ℝ, 1 / 2 < s ∧ s < ‖a‖ / ρ :=
    ⟨(1 / 2 + ‖a‖ / ρ) / 2, by linarith, by linarith⟩
  have hs0 : 0 < s := by linarith
  refine ⟨(s : ℂ) / a, ?_, ?_⟩
  · have ha : a * ((s : ℂ) / a) = (s : ℂ) := by field_simp
    rw [mem_ofPred_eq, ha, Complex.ofReal_re]
    linarith
  · rw [mem_ball, dist_zero_right, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs0, div_lt_iff₀ hr, inv_mul_eq_div]
    rw [lt_div_iff₀ hρ] at hs2 ⊢
    linarith

/-- The inversion `w ↦ ζ + w⁻¹` carries the model region onto the disc-minus-crosscut region. This
is the transport half of the Möbius reduction: the half-plane factor becomes `ball c r` by
`TauCeti.mem_ball_iff_one_lt_two_mul_re_mul_inv`, and the ball factor becomes the complement of
`closedBall ζ ρ`. -/
private lemma image_add_inv_halfPlane_inter_ball (hζ : dist ζ c = r) (hρ : 0 < ρ) :
    (fun w : ℂ => ζ + w⁻¹) '' ({w : ℂ | 1 < 2 * ((c - ζ) * w).re} ∩ ball 0 ρ⁻¹)
      = ball c r \ closedBall ζ ρ := by
  ext y
  constructor
  · rintro ⟨w, hwT, rfl⟩
    have hw0 : w ≠ 0 := ne_zero_of_one_lt_two_mul_re_mul hwT.1
    have hyζ : ζ + w⁻¹ - ζ = w⁻¹ := by ring
    have hne : ζ + w⁻¹ ≠ ζ := by
      simpa [hyζ, sub_eq_zero] using inv_ne_zero hw0
    have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    refine ⟨?_, ?_⟩
    · rw [mem_ball_iff_one_lt_two_mul_re_mul_inv hζ hne, hyζ, inv_inv]
      exact hwT.1
    · rw [mem_closedBall, dist_eq_norm, hyζ, norm_inv, not_le]
      have hball := hwT.2
      rw [mem_ball, dist_zero_right] at hball
      rw [lt_inv_comm₀ hρ hwnorm]
      exact hball
  · rintro ⟨hy1, hy2⟩
    rw [mem_closedBall, dist_eq_norm, not_le] at hy2
    have hyne : y ≠ ζ := by
      intro h
      rw [h, sub_self, norm_zero] at hy2
      linarith
    refine ⟨(y - ζ)⁻¹, ⟨?_, ?_⟩, by simp⟩
    · exact (mem_ball_iff_one_lt_two_mul_re_mul_inv hζ hyne).mp hy1
    · rw [mem_ball, dist_zero_right, norm_inv, inv_lt_inv₀ (by linarith) hρ]
      exact hy2

/-- **The part of a disc outside a circular crosscut is connected.** For `ζ` on the circle
`sphere c r` and `0 < ρ < 2 * r`, the set `ball c r \ closedBall ζ ρ` is connected — and nonempty,
which is where `ρ < 2 * r` is used: a larger `ρ` would swallow the disc.

The set is *not* convex, and the proof is the Möbius reduction of the module docstring. The
inversion `z ↦ (z - ζ)⁻¹` carries `ball c r` to the half-plane `{w | 1 < 2 * ((c - ζ) * w).re}` by
`TauCeti.mem_ball_iff_one_lt_two_mul_re_mul_inv`, and the complement of `closedBall ζ ρ` to
`ball 0 ρ⁻¹`; the intersection of those two is convex, and `w ↦ ζ + w⁻¹` carries it back
continuously, `0` not being in it.

Positivity of `r` is not a separate hypothesis: `0 < ρ < 2 * r` already forces it. -/
theorem isConnected_ball_diff_closedBall (hζ : dist ζ c = r) (hρ : 0 < ρ)
    (hρ' : ρ < 2 * r) : IsConnected (ball c r \ closedBall ζ ρ) := by
  have hac : ‖c - ζ‖ = r := by rw [← dist_eq_norm, dist_comm, hζ]
  rw [← image_add_inv_halfPlane_inter_ball hζ hρ]
  refine ((convex_halfPlane_inter_ball _ _).isConnected
    (nonempty_halfPlane_inter_ball hρ (by rw [hac]; exact hρ'))).image _ fun w hw => ?_
  exact (continuousAt_const.add
    (continuousAt_inv₀ (ne_zero_of_one_lt_two_mul_re_mul hw.1))).continuousWithinAt

/-- **The far side of a circular crosscut is a connected component of the cut disc.** The companion
of `TauCeti.connectedComponentIn_ball_diff_sphere_eq_ball_inter_ball` of
`TauCeti/Analysis/Normed/Module/Ball/Cut.lean`; here the connectedness of the piece is the
substantial `TauCeti.isConnected_ball_diff_closedBall` rather than convexity, which is why this
half stays in the plane. -/
theorem connectedComponentIn_ball_diff_sphere_eq_ball_diff_closedBall
    (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρ' : ρ < 2 * r) (hz : z ∈ ball c r \ closedBall ζ ρ) :
    connectedComponentIn (ball c r \ sphere ζ ρ) z = ball c r \ closedBall ζ ρ := by
  have hsub : ball c r \ closedBall ζ ρ ⊆ ball c r \ sphere ζ ρ :=
    sdiff_sphere_eq_inter_ball_union_sdiff_closedBall (x := ζ) (s := ball c r) ▸ subset_union_right
  refine Subset.antisymm ?_ ((isConnected_ball_diff_closedBall hζ hρ hρ').isPreconnected
    |>.subset_connectedComponentIn hz hsub)
  rcases subset_inter_ball_or_subset_sdiff_closedBall (x := ζ) (s := ball c r) isOpen_ball
    isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _) with h | h
  · exact absurd hz (Set.disjoint_left.mp disjoint_inter_ball_sdiff_closedBall
      (h (mem_connectedComponentIn (hsub hz))))
  · exact h

/-! ## The maximum modulus principle on a crosscut neighbourhood -/

variable {f : ℂ → ℂ} {a : ℂ} {C r₀ : ℝ}

/-- **The maximum modulus principle on a crosscut neighbourhood.** A function holomorphic on the
crosscut neighbourhood and continuous up to its closure that stays within `C` of a value `a` on the
closed crosscut arc and on the boundary cap stays within `C` of `a` on the whole crosscut
neighbourhood.

The crosscut neighbourhood is a bounded open set whose frontier is covered by those two pieces
(`TauCeti.frontier_ball_inter_ball_subset`), so this is Mathlib's
`Complex.norm_le_of_forall_mem_frontier_norm_le` applied to `f - a` on it. Neither injectivity of
`f` nor connectivity of anything is used. Regularity is asked for on the crosscut neighbourhood
alone rather than on the disc, which is all the maximum principle consumes; a caller holding
`DiffContOnCl ℂ f (ball c r)` supplies it by `DiffContOnCl.mono inter_subset_left`. -/
theorem norm_sub_le_of_mem_ball_inter_ball (hf : DiffContOnCl ℂ f (ball c r ∩ ball ζ ρ))
    (harc : ∀ w ∈ closedBall c r ∩ sphere ζ ρ, ‖f w - a‖ ≤ C)
    (hcap : ∀ w ∈ sphere c r ∩ closedBall ζ ρ, ‖f w - a‖ ≤ C)
    (hz : z ∈ ball c r ∩ ball ζ ρ) : ‖f z - a‖ ≤ C := by
  refine Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball.subset inter_subset_left) (hf.sub_const a)
    (fun w hw => ?_) (subset_closure hz)
  rcases frontier_ball_inter_ball_subset hw with h | h
  · exact hcap w h
  · exact harc w h

/-- **The maximum modulus principle on a crosscut neighbourhood, from interior values alone.** A
function holomorphic on `ball c r`, with *no* regularity assumed at the boundary circle, that stays
within `C` of a value `a` on the part `ball c r ∩ sphere ζ ρ` of the crosscut circle inside the disc
and on the collar `r₀ ≤ dist w c` of the crosscut neighbourhood, stays within `C` of `a` throughout
that neighbourhood.

This is `TauCeti.norm_sub_le_of_mem_ball_inter_ball` applied on a slightly smaller concentric disc
`ball c s`, on whose closure `f` is continuous for free: choosing `max r₀ (dist z c) < s < r` puts
the given point `z` inside `ball c s` and the whole cap `sphere c s ∩ closedBall ζ ρ` inside the
collar, and letting `s` exhaust `r` covers the crosscut neighbourhood.

It is this form, not the frontier form, that the boundary criteria below consume. Their hypotheses
then constrain only the values `f` takes *inside* the disc, so that a boundary limit is a
conclusion rather than a restatement of an assumed continuity up to the boundary: a hypothesis
of the shape `DiffContOnCl ℂ f (ball c r)` already contains `ContinuousOn f (closedBall c r)` and
so would make the criteria vacuous. Assuming continuity only on the closure of each crosscut
neighbourhood would not help, since that closure contains `ζ` itself; hence the exhaustion. -/
theorem norm_sub_le_of_mem_ball_inter_ball_of_differentiableOn
    (hd : DifferentiableOn ℂ f (ball c r)) (hr₀ : r₀ < r)
    (harc : ∀ w ∈ ball c r ∩ sphere ζ ρ, ‖f w - a‖ ≤ C)
    (hcap : ∀ w ∈ ball c r ∩ closedBall ζ ρ, r₀ ≤ dist w c → ‖f w - a‖ ≤ C)
    (hz : z ∈ ball c r ∩ ball ζ ρ) : ‖f z - a‖ ≤ C := by
  have hzr : dist z c < r := mem_ball.mp hz.1
  obtain ⟨s, hzs, hr₀s, hsr⟩ : ∃ s, dist z c < s ∧ r₀ ≤ s ∧ s < r :=
    ⟨(max r₀ (dist z c) + r) / 2, by
      have h₁ := le_max_left r₀ (dist z c)
      have h₂ := le_max_right r₀ (dist z c)
      have h₃ := max_lt hr₀ hzr
      exact ⟨by linarith, by linarith, by linarith⟩⟩
  have hsub : closedBall c s ⊆ ball c r := closedBall_subset_ball hsr
  refine norm_sub_le_of_mem_ball_inter_ball (r := s)
    ((hd.diffContOnCl_ball hsub).mono inter_subset_left)
    (fun w hw => harc w ⟨hsub hw.1, hw.2⟩) (fun w hw => ?_) ⟨mem_ball.mpr hzs, hz.2⟩
  have hwc : dist w c = s := mem_sphere.mp hw.1
  exact hcap w ⟨hsub (mem_closedBall.mpr hwc.le), hw.2⟩ (hwc ▸ hr₀s)

/-- **The oscillation of a holomorphic function on a crosscut neighbourhood** is at most twice a
bound holding on the crosscut arc and on the collar of the boundary. This is the form
`TauCeti.norm_sub_le_of_mem_ball_inter_ball_of_differentiableOn` is consumed in: what a Cauchy
criterion needs is a bound on distances between *pairs* of values, and the intermediate value `a`
disappears. -/
theorem dist_le_of_mem_ball_inter_ball (hd : DifferentiableOn ℂ f (ball c r)) (hr₀ : r₀ < r)
    (harc : ∀ w ∈ ball c r ∩ sphere ζ ρ, ‖f w - a‖ ≤ C)
    (hcap : ∀ w ∈ ball c r ∩ closedBall ζ ρ, r₀ ≤ dist w c → ‖f w - a‖ ≤ C)
    {x y : ℂ} (hx : x ∈ ball c r ∩ ball ζ ρ) (hy : y ∈ ball c r ∩ ball ζ ρ) :
    dist (f x) (f y) ≤ 2 * C := by
  have hx' := norm_sub_le_of_mem_ball_inter_ball_of_differentiableOn hd hr₀ harc hcap hx
  have hy' := norm_sub_le_of_mem_ball_inter_ball_of_differentiableOn hd hr₀ harc hcap hy
  have : dist (f x) (f y) = ‖f x - a - (f y - a)‖ := by rw [dist_eq_norm]; ring_nf
  rw [this]
  calc ‖f x - a - (f y - a)‖ ≤ ‖f x - a‖ + ‖f y - a‖ := norm_sub_le _ _
    _ ≤ 2 * C := by linarith

/-! ## The crosscut criterion for boundary behaviour -/

/-- **The crosscut criterion, cluster-set form.** If for every `ε > 0` there is *some* radius
`ρ > 0` at which the function `f` is within `ε` of a single value on the part
`ball c r ∩ sphere ζ ρ` of the circle around `ζ` inside the disc and on a collar of the boundary,
then `f` has at most one cluster value at `ζ` along the disc.

The maximum modulus principle turns each such estimate into an oscillation bound on the crosscut
neighbourhood `ball c r ∩ ball ζ ρ`
(`TauCeti.norm_sub_le_of_mem_ball_inter_ball_of_differentiableOn`), and those neighbourhoods are
exactly the traces on the disc of the balls around `ζ`, so
`TauCeti.subsingleton_clusterSetOn_of_forall_exists` applies verbatim. Only the values of `f` on
the *open* disc are constrained, and only holomorphy there is assumed; note that `ζ` need not be
on the boundary circle for this statement, that `ρ`, `r₀` and `a` may all depend on `ε`, and that
`ρ` is not bounded above by `2 * r`, so a witness need not cut a circular crosscut. -/
theorem subsingleton_clusterSetOn_ball (hd : DifferentiableOn ℂ f (ball c r))
    (h : ∀ ε > 0, ∃ ρ > 0, ∃ r₀ < r, ∃ a : ℂ, (∀ w ∈ ball c r ∩ sphere ζ ρ, ‖f w - a‖ ≤ ε) ∧
      ∀ w ∈ ball c r ∩ closedBall ζ ρ, r₀ ≤ dist w c → ‖f w - a‖ ≤ ε) :
    (clusterSetOn f (ball c r) ζ).Subsingleton := by
  refine subsingleton_clusterSetOn_of_forall_exists fun ε hε => ?_
  obtain ⟨ρ, hρ, r₀, hr₀, a, harc, hcap⟩ := h (ε / 2) (by positivity)
  refine ⟨ρ, hρ, fun x hx y hy => ?_⟩
  have := dist_le_of_mem_ball_inter_ball hd hr₀ harc hcap hx hy
  linarith

/-- **The crosscut criterion for a boundary limit.** A bounded holomorphic function on a disc has a
limit at a boundary point `ζ`, along the disc, as soon as for every `ε > 0` there is some radius
`ρ > 0` at which it is within `ε` of a single value on the part `ball c r ∩ sphere ζ ρ` of the
circle around `ζ` inside the disc and on a collar of the boundary. As in
`TauCeti.subsingleton_clusterSetOn_ball`, no upper bound on `ρ` is imposed, so a witness need not
cut a circular crosscut.

Nothing is assumed at the boundary circle itself: the input is the behaviour of `f` inside the
disc, and the limit is a conclusion. Boundedness alone is far from enough — a bounded holomorphic
function on a disc need not have any limit at a given boundary point — so the estimate `h` is what
carries the content; it is exactly the estimate the length–area method produces on the arc and
local connectedness of the image boundary produces on the collar.

The cluster set is a subsingleton by `TauCeti.subsingleton_clusterSetOn_ball`, and it is nonempty
because `f` maps the disc into the compact closure of its bounded image; that is exactly what
`TauCeti.exists_tendsto_of_clusterSetOn_subsingleton` needs. -/
theorem exists_tendsto_nhdsWithin_ball (hr : 0 < r) (hd : DifferentiableOn ℂ f (ball c r))
    (hb : IsBounded (f '' ball c r)) (hζ : dist ζ c = r)
    (h : ∀ ε > 0, ∃ ρ > 0, ∃ r₀ < r, ∃ a : ℂ, (∀ w ∈ ball c r ∩ sphere ζ ρ, ‖f w - a‖ ≤ ε) ∧
      ∀ w ∈ ball c r ∩ closedBall ζ ρ, r₀ ≤ dist w c → ‖f w - a‖ ≤ ε) :
    ∃ v, Tendsto f (𝓝[ball c r] ζ) (𝓝 v) := by
  refine exists_tendsto_of_clusterSetOn_subsingleton hb.isCompact_closure
    (fun w hw => subset_closure ⟨w, hw, rfl⟩) ?_ (subsingleton_clusterSetOn_ball hd h)
  rw [closure_ball c hr.ne']
  exact mem_closedBall.mpr hζ.le

/-- **The crosscut criterion for a continuous extension to the closed disc.** If the hypothesis of
`TauCeti.exists_tendsto_nhdsWithin_ball` holds at *every* point of the boundary circle, the bounded
holomorphic function `f` extends continuously to `closedBall c r`.

This is the shape in which the Carathéodory boundary correspondence is proved: whatever geometric
hypothesis is placed on the image, it is used only to produce, at each boundary point and each
`ε`, a radius `ρ > 0` — a crosscut radius in the application, though the statement imposes no
upper bound on it — along which `f` varies by at most `ε` on `ball c r ∩ sphere ζ ρ` and on the
collar. The extension is genuinely produced here rather than assumed, since only holomorphy and
boundedness on the *open* disc are hypotheses. Nothing here asserts that the extension is
injective, which is an independent matter. -/
theorem exists_continuousOn_closedBall_eqOn (hr : 0 < r) (hd : DifferentiableOn ℂ f (ball c r))
    (hb : IsBounded (f '' ball c r))
    (h : ∀ ζ ∈ sphere c r, ∀ ε > 0, ∃ ρ > 0, ∃ r₀ < r, ∃ a : ℂ,
      (∀ w ∈ ball c r ∩ sphere ζ ρ, ‖f w - a‖ ≤ ε) ∧
        ∀ w ∈ ball c r ∩ closedBall ζ ρ, r₀ ≤ dist w c → ‖f w - a‖ ≤ ε) :
    ∃ F : ℂ → ℂ, ContinuousOn F (closedBall c r) ∧ EqOn F f (ball c r) := by
  obtain ⟨F, hFc, hFe⟩ := exists_continuousOn_closure_eqOn_of_isBounded isOpen_ball
    hd.continuousOn hb fun ζ hζ => by
      refine subsingleton_clusterSetOn_ball hd (h ζ ?_)
      rwa [frontier_ball c hr.ne'] at hζ
  exact ⟨F, closure_ball c hr.ne' ▸ hFc, hFe⟩

end TauCeti
