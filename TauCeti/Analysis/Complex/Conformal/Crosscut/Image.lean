/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.CutDiameter
public import TauCeti.Topology.UniformlyLocallyConnected
import TauCeti.Analysis.Complex.Conformal.ClusterSet
import TauCeti.Analysis.Complex.Conformal.Crosscut.Endpoints

/-!
# How a circular crosscut splits the image of a disc, and its boundary

`Conformal/Crosscut/Basic.lean` cuts a disc `ball c r` at a boundary point `ζ` by the circle
`sphere ζ ρ` and proves that the two sides `ball c r ∩ ball ζ ρ` and `ball c r \ closedBall ζ ρ`
are the two connected components of what is left. `Conformal/CutDiameter.lean` transports the
two sides to a conformal image and bounds their width by the width of the image crosscut together
with the boundary piece cut off. This file completes that picture on the image side: it splits
`frontier (f '' ball c r)`, and it supplies — from local connectedness of that frontier — a small
connected boundary set enclosing the part of that frontier which clings to the image crosscut.

## The decomposition

Write `Ω = f '' ball c r`, `A = f '' (ball c r ∩ ball ζ ρ)`, `B = f '' (ball c r \ closedBall ζ ρ)`
for the images of the two sides, and `γ = f '' (ball c r ∩ sphere ζ ρ)` for the image crosscut, `f`
being holomorphic and injective on the disc. Then `Ω = A ∪ γ ∪ B`
(`TauCeti.image_ball_eq_union_image_crosscut`), and the frontier of a union is covered by the
frontiers of its parts, so a frontier point of `Ω` is a frontier point of `A`, a frontier point of
`B`, or an adherent point of `γ`:

> `frontier Ω = frontier Ω ∩ frontier A ∪ frontier Ω ∩ closure γ ∪ frontier Ω ∩ frontier B`

(`TauCeti.frontier_image_ball_eq_union`). This is the sense in which a crosscut *cuts the image
boundary in two*: the two boundary pieces `frontier Ω ∩ frontier A` and `frontier Ω ∩ frontier B`
cover `frontier Ω` apart from a middle piece no wider than the image crosscut itself
(`TauCeti.diam_frontier_inter_closure_image_ball_inter_sphere_le`), which by the length–area
estimate of `Conformal/ShortCrosscut.lean` can be made as small as desired.

## The middle piece, and the connected boundary set enclosing it

The middle piece is not merely small, it is *nonempty*
(`TauCeti.nonempty_frontier_inter_closure_image_ball_inter_sphere`): the crosscut has an endpoint on
`sphere c r`, and along that endpoint `f` has a cluster value, which is adherent to `γ` and — a
conformal map being proper — is not attained, hence lies on `frontier Ω`. That is a statement about
the *one* endpoint the proof selects, and all that is claimed: nothing below says where the other
end goes, nor that the two ends are joined.

That nonemptiness is what the last theorem consumes. If `frontier Ω` is uniformly locally connected
— which by `TauCeti.IsCompact.isUniformlyLocallyConnected` is exactly local connectedness,
`frontier Ω` being compact — then for every `ε > 0` there is a single `δ > 0`, independent of the
boundary point `ζ` and of the crosscut radius `ρ`, such that an image crosscut of diameter less than
`δ` has its whole middle piece enclosed in a *connected* subset of `frontier Ω` of diameter at most
`ε` (`TauCeti.exists_isConnected_subset_frontier_image_ball_of_diam_lt`), the general enclosure
statement `TauCeti.IsUniformlyLocallyConnected.exists_isConnected_superset` applied to the middle
piece. This is where the local connectedness of `∂Ω` that `Conformal/CutDiameter.lean` names as one
of its two geometric inputs enters, the other being the length–area estimate.

What is **not** proved here, and is what still separates layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md` from its milestone, is that the resulting connected set
encloses the boundary piece: that `frontier Ω ∩ frontier A` is contained in it together with the
image crosscut. Classically that is a separation argument about the closed curve formed by the image
crosscut and the boundary set, and no part of it is claimed below.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything here is stated for maps of `ℂ`. The two inputs that
are not about conformality are stated at their own generality elsewhere: `TauCeti.diam_frontier`
for an arbitrary real normed space and `TauCeti.IsUniformlyLocallyConnected` for an arbitrary
pseudometric space.

## Main results

* `TauCeti.image_ball_eq_union_image_crosscut` — the image of the disc is the union of the images
  of the two sides of a crosscut and of the crosscut itself.
* `TauCeti.frontier_image_ball_subset_union` and `TauCeti.frontier_image_ball_eq_union` — a
  crosscut cuts the boundary of the image into two pieces and a middle piece adherent to the image
  crosscut.
* `TauCeti.diam_frontier_inter_closure_image_ball_inter_sphere_le` and
  `TauCeti.nonempty_frontier_inter_closure_image_ball_inter_sphere` — the middle piece is nonempty
  and no wider than the image crosscut.
* `TauCeti.exists_isConnected_subset_frontier_image_ball_of_diam_lt` — a uniformly locally
  connected image boundary encloses the middle piece of every short image crosscut in a small
  connected boundary set, at a rate independent of the boundary point and the crosscut radius.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself, and the
pinned Mathlib has no boundary correspondence for conformal maps. So this file is new Lean
formalization rather than a temporary shim.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2–2.3.
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open Bornology Complex Filter Metric Set Topology

variable {f : ℂ → ℂ} {c ζ : ℂ} {r ρ : ℝ}

/-! ## The three pieces of the image -/

/-- **A circular crosscut splits the image of a disc into three pieces**: the images of the two
sides and the image crosscut. This is `TauCeti.ball_diff_sphere_eq_union` — the corresponding
identity in the disc — pushed forward, and needs nothing of `f`. -/
theorem image_ball_eq_union_image_crosscut (f : ℂ → ℂ) (c ζ : ℂ) (r ρ : ℝ) :
    f '' ball c r =
      f '' (ball c r ∩ ball ζ ρ) ∪ f '' (ball c r ∩ sphere ζ ρ) ∪
        f '' (ball c r \ closedBall ζ ρ) := by
  rw [← image_union, ← image_union]
  congr 1
  rw [union_right_comm, ← ball_diff_sphere_eq_union, sdiff_union_inter]

/-! ## The crosscut cuts the boundary of the image in two -/

/-- **The boundary of the image of a disc is covered by the boundaries of the two sides of a
crosscut together with the closure of the image crosscut.**

Like the decomposition itself this needs nothing of `f`: the image of the disc is the union of the
three pieces by `TauCeti.image_ball_eq_union_image_crosscut`, the frontier of a union is covered by
the frontiers of the two parts by `frontier_union_subset`, and the frontier of the image crosscut
lies in its closure. -/
theorem frontier_image_ball_subset_union (f : ℂ → ℂ) (c ζ : ℂ) (r ρ : ℝ) :
    frontier (f '' ball c r) ⊆
      frontier (f '' (ball c r ∩ ball ζ ρ)) ∪ closure (f '' (ball c r ∩ sphere ζ ρ)) ∪
        frontier (f '' (ball c r \ closedBall ζ ρ)) := by
  have hunion : ∀ s t : Set ℂ, frontier (s ∪ t) ⊆ frontier s ∪ frontier t := fun s t =>
    (frontier_union_subset s t).trans (union_subset_union inter_subset_left inter_subset_right)
  rw [image_ball_eq_union_image_crosscut f c ζ r ρ]
  exact (hunion _ _).trans (union_subset_union
    ((hunion _ _).trans (union_subset_union subset_rfl frontier_subset_closure)) subset_rfl)

/-- **A circular crosscut cuts the boundary of the image into two pieces and a middle piece.** The
equality form of `TauCeti.frontier_image_ball_subset_union`: `frontier (f '' ball c r)` is the union
of the two *boundary pieces* the crosscut determines — its intersections with the frontiers of the
images of the two sides — and of the part of it adherent to the image crosscut, which
`TauCeti.diam_frontier_inter_closure_image_ball_inter_sphere_le` shows to be no wider than the
image crosscut itself. -/
theorem frontier_image_ball_eq_union (f : ℂ → ℂ) (c ζ : ℂ) (r ρ : ℝ) :
    frontier (f '' ball c r) =
      frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ)) ∪
        frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) ∪
        frontier (f '' ball c r) ∩ frontier (f '' (ball c r \ closedBall ζ ρ)) := by
  rw [← inter_union_distrib_left, ← inter_union_distrib_left]
  exact (inter_eq_left.mpr (frontier_image_ball_subset_union f c ζ r ρ)).symm

/-! ## The middle piece -/

/-- **The middle piece is no wider than the image crosscut.** It is contained in the closure of the
image crosscut, and closing a set does not change its diameter. -/
theorem diam_frontier_inter_closure_image_ball_inter_sphere_le (hb : IsBounded (f '' ball c r))
    (ζ : ℂ) (ρ : ℝ) :
    diam (frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)))
      ≤ diam (f '' (ball c r ∩ sphere ζ ρ)) := by
  have harc : IsBounded (f '' (ball c r ∩ sphere ζ ρ)) := hb.subset (image_mono inter_subset_left)
  calc diam (frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)))
      ≤ diam (closure (f '' (ball c r ∩ sphere ζ ρ))) := diam_mono inter_subset_right harc.closure
    _ = diam (f '' (ball c r ∩ sphere ζ ρ)) := diam_closure _

/-- **The middle piece is nonempty**: for `f` holomorphic and injective on `ball c r` with bounded
image, and a genuine circular crosscut at a boundary point `ζ`, the set
`frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ))` has a point. So the image
crosscut does cling to the boundary of the image — at the one endpoint the proof selects; where the
other end of the crosscut goes is not asserted.

The crosscut has an endpoint `e` on `sphere c r`, adherent to it by
`TauCeti.closure_ball_inter_sphere`. Along `e` the map has a cluster value, the image being confined
to the compact `closure (f '' ball c r)`; that value is adherent to the image crosscut by
construction, and by `TauCeti.clusterSetOn_subset_frontier_image` — properness of a conformal map —
it is a boundary value of the image rather than one of its points. -/
theorem nonempty_frontier_inter_closure_image_ball_inter_sphere
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r)) (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r) :
    (frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ))).Nonempty := by
  have hr : 0 < r := by linarith
  -- one of the two endpoints of the crosscut
  have hemem : circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
      ∈ sphere c r ∩ sphere ζ ρ := by
    rw [sphere_inter_sphere_eq_pair_circleMap hζ hρ hρr]
    exact Or.inl rfl
  have hecl : circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
      ∈ closure (ball c r ∩ sphere ζ ρ) := by
    rw [closure_ball_inter_sphere hζ hρ hρr]
    exact ⟨sphere_subset_closedBall hemem.1, hemem.2⟩
  have hefr : circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r))) ∈ frontier (ball c r) := by
    rw [frontier_ball c hr.ne']
    exact hemem.1
  -- a cluster value of `f` along the crosscut at that endpoint
  obtain ⟨v, hv⟩ := clusterSetOn_nonempty hb.isCompact_closure
    (fun z hz => subset_closure (mem_image_of_mem f (inter_subset_left hz))) hecl
  exact ⟨v, clusterSetOn_subset_frontier_image isOpen_ball hd hinj hefr
    (clusterSetOn_mono inter_subset_left hv), clusterSetOn_subset_closure_image hv⟩

/-! ## The small connected set enclosing the middle piece -/

/-- **A uniformly locally connected image boundary encloses the middle piece of every short image
crosscut in a small connected boundary set.** For `f` holomorphic and injective on `ball c r` with
bounded image and `frontier (f '' ball c r)` uniformly locally connected, every `ε > 0` admits a
single `δ > 0` — independent of the boundary point `ζ` and of the crosscut radius `ρ` — such that
an image crosscut of diameter less than `δ` has its middle piece contained in a connected subset of
`frontier (f '' ball c r)` of diameter at most `ε`.

This is where the local connectedness of `∂Ω` that
`TauCeti.exists_continuousOn_closedBall_eqOn_of_forall_exists_diam_union_le` needs enters, the other
of its two geometric inputs being the length–area estimate
`TauCeti.exists_diam_image_ball_inter_sphere_le`. It does not by itself discharge that criterion,
whose enclosing set has to contain the whole boundary piece
`frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ))` and not only the middle piece.

Everything topological is in `TauCeti.IsUniformlyLocallyConnected.exists_isConnected_superset`, the
statement that a uniformly locally connected set encloses each of its small subsets in a small
connected subset. What remains is that the middle piece is a subset of `frontier (f '' ball c r)`
that is bounded, nonempty by
`TauCeti.nonempty_frontier_inter_closure_image_ball_inter_sphere`, and of diameter less than `δ` by
`TauCeti.diam_frontier_inter_closure_image_ball_inter_sphere_le`. -/
theorem exists_isConnected_subset_frontier_image_ball_of_diam_lt
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r))
    (hulc : IsUniformlyLocallyConnected (frontier (f '' ball c r))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ζ : ℂ, dist ζ c = r → ∀ ρ : ℝ, 0 < ρ → ρ < 2 * r →
      diam (f '' (ball c r ∩ sphere ζ ρ)) < δ →
        ∃ S ⊆ frontier (f '' ball c r), IsConnected S ∧
          frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) ⊆ S ∧ diam S ≤ ε := by
  obtain ⟨δ, hδ, hencl⟩ := hulc.exists_isConnected_superset hε
  refine ⟨δ, hδ, fun ζ hζ ρ hρ hρr hdiam => ?_⟩
  refine hencl _ inter_subset_left
    (((hb.subset (image_mono inter_subset_left)).closure).subset inter_subset_right)
    (nonempty_frontier_inter_closure_image_ball_inter_sphere hd hinj hb hζ hρ hρr) ?_
  exact lt_of_le_of_lt (diam_frontier_inter_closure_image_ball_inter_sphere_le hb ζ ρ) hdiam

end TauCeti
