/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Crosscut.Path
public import TauCeti.Topology.JordanCurve.Basic
import TauCeti.Analysis.Complex.Conformal.Crosscut.Endpoints
import TauCeti.Analysis.Complex.Conformal.Crosscut.Image
import TauCeti.Topology.JordanCurve.Path

/-!
# The distinct-end case of an image crosscut

A genuine circular crosscut of a disc is carried by a conformal map to a simple open arc in the
image domain, and when its image has finite length
`TauCeti.exists_path_range_eq_closure_image_ball_inter_sphere_of_injOn` packages the closure of
that arc as a path whose only possible repetition is a common value of its two endpoints.
`Conformal/Crosscut/Jordan.lean` settles the branch in which that repetition happens — the two ends
coincide and the closed image crosscut is a Jordan curve. This file settles the other branch.

If the closed image crosscut meets the boundary of the image domain in more than one point, the
path has no repetition at all: it is injective, so the closed image crosscut is an **arc**, the
range of an injective path, and its two endpoints are precisely the two points where it meets
`frontier (f '' ball c r)`
(`TauCeti.exists_injective_path_range_eq_closure_image_ball_inter_sphere_of_not_subsingleton`).
The hypothesis is the exact negation of the one `Conformal/Crosscut/Jordan.lean` runs on, so
between them the two files describe the closed image crosscut in every case.

## Which two points the arc ends at

`Conformal/Crosscut/BoundaryEnds.lean` already knows that the boundary piece
`frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ))` is a pair, but it does not say
which pair, and that is exactly what is needed here: the hypothesis on the boundary piece has to be
converted into a statement about the *path*. The identification comes from
`TauCeti.frontier_inter_closure_image_inter_sphere_eq_biUnion_clusterSetOn`, which writes the
boundary piece as the union of the cluster sets of `f` over `sphere c r ∩ sphere ζ ρ` — the two
angular ends of the crosscut, by `TauCeti.sphere_inter_sphere_eq_pair_circleMap` — together with
the two endpoint limits the path theorem hands out, which
`TauCeti.clusterSetOn_eq_singleton_of_tendsto` turns into those cluster sets. So the boundary piece
is `{u, v}` for `u` and `v` the endpoints of the path, and the hypothesis that it is not a
subsingleton says exactly `u ≠ v`.

## Closing the arc up

The point of producing an arc is that an arc can be closed into a Jordan curve. Any arc `B` of the
image boundary running between the same two ends meets the closed image crosscut only there —
`B` lies in `frontier (f '' ball c r)`, so the intersection lies in the boundary piece `{u, v}` —
and `TauCeti.isJordanCurve_range_union_range_of_inter_eq_pair` glues the two arcs along those two
points. That is
`exists_forall_isJordanCurve_closure_image_ball_inter_sphere_union_range_of_not_subsingleton`.

Which arc of the boundary to take, and which of the two pieces the crosscut cuts the domain into is
enclosed by the resulting Jordan curve, is a planar separation question and is not settled here; the
statement below is deliberately universally quantified over the boundary arc, and asserts nothing
about the region the curve encloses.

## Main results

* `TauCeti.exists_injective_path_range_eq_closure_image_ball_inter_sphere_of_not_subsingleton` —
  a finite-length image crosscut meeting the image boundary in more than one point closes to an
  arc, whose two endpoints are exactly the two points of that meeting.
* `exists_forall_isJordanCurve_closure_image_ball_inter_sphere_union_range_of_not_subsingleton` —
  that arc together with any arc of the image boundary joining its two ends is a Jordan curve.

## Roadmap role

This advances layer **L5** of `TauCetiRoadmap/ConformalMapping/README.md`, the Jordan-domain case of
the Carathéodory boundary correspondence. `Conformal/Crosscut/Jordan.lean` names the remaining step
as "treat the Jordan curve produced here when the ends coincide, and join the crosscut to one of the
two boundary arcs when they are distinct, in order to bound the whole boundary of the cut-off image
piece". The second half of that — the joining — is what is done here; the boundary arcs themselves
come from `TauCeti.IsJordanCurve.exists_pos_forall_exists_diam_le` of
`TauCeti/Topology/JordanCurve/SmallArc.lean`, and are small because the two ends are close by
`TauCeti.exists_frontier_inter_closure_image_ball_inter_sphere_eq_pair_dist_le_of_isBounded`. What
remains after this file is the separation argument choosing between the two boundary arcs.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and the
pinned Mathlib has no boundary correspondence for conformal maps and no Jordan-curve vocabulary. So
this file is new Lean formalization rather than a temporary shim. Through
`Conformal/Crosscut/Image.lean` it consumes the L0–L3 shim
`TauCeti.isOpen_image_of_differentiableOn_of_injOn`, to be refactored onto Mathlib's open mapping
API once the upstream work lands. No Mathlib source is vendored.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2–2.3.
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open Complex Filter Metric Set Topology
open scoped Real

variable {f : ℂ → ℂ} {c ζ : ℂ} {r ρ : ℝ}

/-! ## The closed image crosscut as an arc -/

/-- **A finite-length image crosscut with two boundary ends closes to an arc.**
Let `f` be holomorphic and injective on `ball c r`, and let `ball c r ∩ sphere ζ ρ` be a genuine
circular crosscut at a boundary point `ζ` whose image has finite length. If the boundary piece

`frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ))`

has more than one point, then it is a pair `{u, v}` of distinct points and the closure of the image
crosscut is the range of an injective path from `u` to `v`.

The hypothesis is the exact negation of the one
`TauCeti.isJordanCurve_closure_image_ball_inter_sphere_of_subsingleton` runs on, and, like it, it
is deliberately stated on the boundary piece rather than presuming the planar separation argument
that would decide which of the two branches occurs.

Only two things have to be added to the path theorem
`TauCeti.exists_path_range_eq_closure_image_ball_inter_sphere_of_injOn`. First, the boundary piece
is identified with the pair of endpoints of that path, by writing it as the union of the cluster
sets at the two angular ends of the crosscut and evaluating those cluster sets at the endpoint
limits the path theorem supplies. Second, that identification turns the hypothesis into `u ≠ v`,
which excludes the only repetition the path theorem leaves open. -/
theorem exists_injective_path_range_eq_closure_image_ball_inter_sphere_of_not_subsingleton
    (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hfin : circleImageLength f (ball c r) ζ ρ ≠ ⊤)
    (hends : ¬ (frontier (f '' ball c r) ∩
      closure (f '' (ball c r ∩ sphere ζ ρ))).Subsingleton) :
    ∃ u v, u ≠ v ∧
      frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) = {u, v} ∧
      ∃ γ : Path u v, Function.Injective γ ∧
        range γ = closure (f '' (ball c r ∩ sphere ζ ρ)) := by
  obtain ⟨u, v, γ, hγrange, htu, htv, -, -, hγsimple, -⟩ :=
    exists_path_range_eq_closure_image_ball_inter_sphere_of_injOn hζ hρ hρr hf hinj hfin
  have hr : 0 < r := by linarith
  have hφ0 := arccos_div_two_mul_pos hr hρr
  -- Each angular end of the crosscut is adherent to it, so the endpoint limit is its cluster set.
  have hcluster : ∀ {θ : ℝ} {w : ℂ},
      (θ = (c - ζ).arg - Real.arccos (ρ / (2 * r)) ∨
        θ = (c - ζ).arg + Real.arccos (ρ / (2 * r))) →
      Tendsto f (𝓝[ball c r ∩ sphere ζ ρ] (circleMap ζ ρ θ)) (𝓝 w) →
      clusterSetOn f (ball c r ∩ sphere ζ ρ) (circleMap ζ ρ θ) = {w} := by
    intro θ w hθ hw
    refine clusterSetOn_eq_singleton_of_tendsto ?_ hw
    rw [closure_ball_inter_sphere hζ hρ hρr,
      closedBall_inter_sphere_eq_circleMap_image_Icc hζ hρ hρr]
    refine ⟨θ, ?_, rfl⟩
    rcases hθ with rfl | rfl
    · exact ⟨le_rfl, by linarith⟩
    · exact ⟨by linarith, le_rfl⟩
  -- The boundary piece is the pair of endpoints of the path.
  have hpair : frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) = {u, v} := by
    rw [frontier_inter_closure_image_inter_sphere_eq_biUnion_clusterSetOn isOpen_ball hf hinj,
      frontier_ball c hr.ne', sphere_inter_sphere_eq_pair_circleMap hζ hρ hρr, biUnion_pair,
      hcluster (Or.inl rfl) htu, hcluster (Or.inr rfl) htv, singleton_union]
  -- So the hypothesis says the two ends are distinct.
  have huv : u ≠ v := by
    rintro rfl
    exact hends (by rw [hpair, pair_eq_singleton]; exact subsingleton_singleton)
  -- Distinct ends leave the path no repetition at all.
  refine ⟨u, v, huv, hpair, γ, fun a b hab => ?_, hγrange⟩
  rcases hγsimple hab with h | h | h
  · exact h
  · rw [h.1, h.2, γ.source, γ.target] at hab
    exact absurd hab huv
  · rw [h.1, h.2, γ.source, γ.target] at hab
    exact absurd hab.symm huv

/-! ## Closing the arc with an arc of the image boundary -/

/-- **A finite-length image crosscut with two boundary ends closes to a Jordan curve against any
arc of the image boundary joining them.** Under the hypotheses of
`TauCeti.exists_injective_path_range_eq_closure_image_ball_inter_sphere_of_not_subsingleton`, the
boundary piece is a pair `{u, v}` of distinct points, and for *every* injective path `δ` from `u`
to `v` whose range lies on `frontier (f '' ball c r)` the union

`closure (f '' (ball c r ∩ sphere ζ ρ)) ∪ range δ`

is a Jordan curve.

The two arcs meet exactly in `{u, v}`: an intersection point lies on the image boundary because it
lies on `range δ`, and on the closed image crosscut because it lies on the other arc, so it lies in
the boundary piece; conversely `u` and `v` are endpoints of both. That is precisely the hypothesis
of `TauCeti.isJordanCurve_range_union_range_of_inter_eq_pair`.

Nothing is claimed about which of the two arcs the image boundary is cut into by `u` and `v` should
be used, nor about the region the resulting Jordan curve encloses: both are planar separation
questions. What the statement supplies is that whichever arc a separation argument selects, the
closed curve it produces is a Jordan curve. -/
theorem exists_forall_isJordanCurve_closure_image_ball_inter_sphere_union_range_of_not_subsingleton
    (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hfin : circleImageLength f (ball c r) ζ ρ ≠ ⊤)
    (hends : ¬ (frontier (f '' ball c r) ∩
      closure (f '' (ball c r ∩ sphere ζ ρ))).Subsingleton) :
    ∃ u v, u ≠ v ∧
      frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) = {u, v} ∧
      ∀ δ : Path u v, Function.Injective δ → range δ ⊆ frontier (f '' ball c r) →
        IsJordanCurve (closure (f '' (ball c r ∩ sphere ζ ρ)) ∪ range δ) := by
  obtain ⟨u, v, huv, hpair, γ, hγinj, hγrange⟩ :=
    exists_injective_path_range_eq_closure_image_ball_inter_sphere_of_not_subsingleton hζ hρ hρr
      hf hinj hfin hends
  refine ⟨u, v, huv, hpair, fun δ hδinj hδsub => ?_⟩
  rw [← hγrange]
  refine isJordanCurve_range_union_range_of_inter_eq_pair hγinj hδinj (subset_antisymm ?_ ?_)
  · rintro w ⟨hwγ, hwδ⟩
    exact hpair ▸ ⟨hδsub hwδ, hγrange ▸ hwγ⟩
  · intro w hw
    simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact ⟨⟨0, γ.source⟩, ⟨0, δ.source⟩⟩
    · exact ⟨⟨1, γ.target⟩, ⟨1, δ.target⟩⟩

end TauCeti
