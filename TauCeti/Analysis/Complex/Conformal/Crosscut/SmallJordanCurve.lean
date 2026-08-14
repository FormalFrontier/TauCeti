/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.JordanCurve.Basic
public import TauCeti.Analysis.Complex.Conformal.ShortCrosscut
import TauCeti.Analysis.Complex.Conformal.Crosscut.Arc
import TauCeti.Analysis.Complex.Conformal.Crosscut.Jordan
import TauCeti.Topology.JordanCurve.SmallArc

/-!
# Small Jordan curves through image crosscuts

Let `f` be a conformal map of a disc onto a bounded domain whose frontier is a Jordan curve. The
length--area method supplies, at every point `ζ` of the source circle, arbitrarily small circular
crosscuts with short images. This file closes such an image crosscut along the frontier of the image
domain and proves that the resulting Jordan curve is arbitrarily small.

There are two cases. If the two boundary ends of the closed image crosscut coincide, the crosscut
itself is a Jordan curve by
`TauCeti.isJordanCurve_closure_image_ball_inter_sphere_of_subsingleton`. Otherwise the crosscut is
an arc between two nearby points of the image frontier. The quantitative Jordan-curve theorem
`TauCeti.IsJordanCurve.exists_pos_forall_exists_path_injective_diam_le` joins those points by a
small injective path along the frontier, and
the distinct-end closing theorem from `Conformal/Crosscut/Arc.lean` closes the two arcs into a
Jordan curve. In both cases the curve lies in the closure of the image domain and contains the
closed image crosscut.

## Main result

* `TauCeti.exists_isJordanCurve_superset_closure_image_ball_inter_sphere_diam_le` -- below every
  prescribed radius, a short image crosscut lies on an arbitrarily small Jordan curve contained in
  the closure of the image domain.
* `TauCeti.exists_isJordanCurve_superset_closure_image_ball_inter_sphere_diam_le_of_isBounded` --
  the bounded-image form used for a Riemann map.

## Roadmap role

This is the last construction before the planar-separation step in layer **L5** of the
`ConformalMapping` roadmap, the Jordan-domain case of the Caratheodory boundary correspondence.
The remaining step is to show that the boundary piece of the crosscut neighbourhood lies on the
small Jordan curve chosen here. The existing crosscut criterion then bounds the cut-off image
piece and gives the continuous extension of the conformal map.

Layer L5 is absent from Mathlib's in-progress Riemann-mapping development, and the pinned Mathlib
has no Jordan-curve vocabulary. The proof follows the crosscut argument in Caratheodory's 1913
paper and the presentations in Pommerenke, Section 2.2--2.3, and Duren, Chapter 3.

## References

* C. Caratheodory, *Ueber die gegenseitige Beziehung der Raender bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Sections 2.2--2.3.
* P. L. Duren, *Univalent Functions*, Chapter 3.
-/

public section

namespace TauCeti

open Bornology Complex MeasureTheory Metric Set

variable {f : ℂ → ℂ} {c ζ : ℂ} {r : ℝ}

/-- **A short image crosscut lies on a small Jordan curve.** Let `f` be holomorphic and injective
on `ball c r`, with finite Dirichlet integral and Jordan-curve frontier. For every `ε > 0`, every
boundary point `ζ` of the disc, and every radius bound `R > 0`, there is a genuine circular
crosscut of radius `ρ < R` whose closed image is contained in a Jordan curve `J` satisfying

* `J ⊆ closure (f '' ball c r)`, and
* `Metric.diam J ≤ ε`.

The closed image crosscut may itself be the Jordan curve: this is the case in which its two ends
on `frontier (f '' ball c r)` coincide. When the ends are distinct, `J` is the union of the closed
image crosscut and a small injective path along that frontier.

No assertion is made about which component of the complement of `J` contains the crosscut
neighbourhood. Identifying that component is the planar-separation input still needed by the
Caratheodory boundary correspondence. -/
theorem exists_isJordanCurve_superset_closure_image_ball_inter_sphere_diam_le
    (hζ : dist ζ c = r) (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hdir : ∫⁻ z in ball c r, ‖deriv f z‖ₑ ^ 2 ≠ ⊤)
    (hfrontier : IsJordanCurve (frontier (f '' ball c r))) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, ρ < 2 * r ∧ ∃ J : Set ℂ,
      IsJordanCurve J ∧
        closure (f '' (ball c r ∩ sphere ζ ρ)) ⊆ J ∧
        J ⊆ closure (f '' (ball c r ∩ sphere ζ ρ)) ∪ frontier (f '' ball c r) ∧
        J ⊆ closure (f '' ball c r) ∧ diam J ≤ ε := by
  obtain ⟨δ, hδ, hpath⟩ :=
    hfrontier.exists_pos_forall_exists_path_injective_diam_le (by positivity : (0 : ℝ) < ε / 2)
  -- one scale `κ` serves both roles below: it caps the crosscut diameter at half the tolerance
  -- and keeps its two ends within the distance `δ` the path-joining theorem needs
  obtain ⟨κ, hκ, hκε, hκδ⟩ : ∃ κ : ℝ, 0 < κ ∧ κ ≤ ε / 2 ∧ κ < δ :=
    ⟨min (ε / 2) (δ / 2), lt_min (by positivity) (by positivity), min_le_left _ _,
      (min_le_right _ _).trans_lt (by linarith)⟩
  obtain ⟨ρ, hρmem, hlenFin, hcross, hcrossBounded⟩ :=
    exists_diam_image_ball_inter_sphere_le_and_circleImageLength_ne_top (ζ := ζ) hf hdir hκ
      (lt_min hR (by linarith : (0 : ℝ) < 2 * r))
  have hρ : ρ ∈ Ioo 0 R := ⟨hρmem.1, hρmem.2.trans_le (min_le_left _ _)⟩
  have hρr : ρ < 2 * r := hρmem.2.trans_le (min_le_right _ _)
  have hcrossSub : closure (f '' (ball c r ∩ sphere ζ ρ)) ⊆ closure (f '' ball c r) :=
    closure_mono (image_mono inter_subset_left)
  by_cases hends :
      (frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ))).Subsingleton
  · refine ⟨ρ, hρ, hρr, closure (f '' (ball c r ∩ sphere ζ ρ)), ?_,
      subset_rfl, subset_union_left, hcrossSub, ?_⟩
    · exact isJordanCurve_closure_image_ball_inter_sphere_of_subsingleton hζ hρ.1 hρr
        hf hinj hlenFin hends
    · rw [diam_closure]
      linarith
  · obtain ⟨u, v, huv, hpair, hclose⟩ :=
      exists_forall_isJordanCurve_closure_image_ball_inter_sphere_union_range_of_not_subsingleton
        hζ hρ.1 hρr hf hinj hlenFin hends
    have hu : u ∈ frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) :=
      hpair ▸ mem_insert u {v}
    have hv : v ∈ frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) :=
      hpair ▸ mem_insert_of_mem u (mem_singleton v)
    have huvδ : dist u v < δ := by
      refine (dist_le_diam_of_mem hcrossBounded.closure hu.2 hv.2).trans_lt ?_
      rw [diam_closure]
      exact hcross.trans_lt hκδ
    obtain ⟨γ, hγinj, hγsub, hγdiam⟩ := hpath hu.1 hv.1 huv huvδ
    refine ⟨ρ, hρ, hρr, closure (f '' (ball c r ∩ sphere ζ ρ)) ∪ range γ,
      hclose γ hγinj hγsub, subset_union_left, union_subset_union subset_rfl hγsub,
      union_subset hcrossSub (hγsub.trans frontier_subset_closure), ?_⟩
    have hinter : (closure (f '' (ball c r ∩ sphere ζ ρ)) ∩ range γ).Nonempty :=
      ⟨u, hu.2, ⟨0, γ.source⟩⟩
    calc
      diam (closure (f '' (ball c r ∩ sphere ζ ρ)) ∪ range γ)
          ≤ diam (closure (f '' (ball c r ∩ sphere ζ ρ))) + diam (range γ) :=
        diam_union' hinter
      _ = diam (f '' (ball c r ∩ sphere ζ ρ)) + diam (range γ) := by
        rw [diam_closure]
      _ ≤ κ + ε / 2 := add_le_add hcross hγdiam
      _ ≤ ε := by linarith

/-- **The bounded-image form of the small-Jordan-curve theorem.** A holomorphic injection of a
disc onto a bounded domain has finite Dirichlet integral by the conformal area formula, so for
every positive tolerance and radius bound, some closed image crosscut can be chosen on a Jordan
curve in the closure of the image domain whose diameter is at most the tolerance.

This is the form used for the Riemann map of a bounded Jordan domain. -/
theorem exists_isJordanCurve_superset_closure_image_ball_inter_sphere_diam_le_of_isBounded
    (hζ : dist ζ c = r) (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hb : IsBounded (f '' ball c r))
    (hfrontier : IsJordanCurve (frontier (f '' ball c r))) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) :
    ∃ ρ ∈ Ioo 0 R, ρ < 2 * r ∧ ∃ J : Set ℂ,
      IsJordanCurve J ∧
        closure (f '' (ball c r ∩ sphere ζ ρ)) ⊆ J ∧
        J ⊆ closure (f '' (ball c r ∩ sphere ζ ρ)) ∪ frontier (f '' ball c r) ∧
        J ⊆ closure (f '' ball c r) ∧ diam J ≤ ε :=
  exists_isJordanCurve_superset_closure_image_ball_inter_sphere_diam_le hζ hr hf hinj
    (lintegral_enorm_deriv_sq_ne_top_of_isBounded isOpen_ball hf
      measurableSet_ball.nullMeasurableSet subset_rfl hinj hb)
    hfrontier hε hR

end TauCeti
