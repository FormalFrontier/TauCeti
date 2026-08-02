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
*near* side to a conformal image and bounds its width by the width of the image crosscut together
with the boundary piece cut off. This file completes that picture on the image side: it splits
`frontier (f '' ball c r)`, and it supplies — from local connectedness of that frontier — the small
connected set joining the two ends of the image crosscut.

## The decomposition

Write `Ω = f '' ball c r`, `A = f '' (ball c r ∩ ball ζ ρ)`, `B = f '' (ball c r \ closedBall ζ ρ)`
for the images of the two sides, and `γ = f '' (ball c r ∩ sphere ζ ρ)` for the image crosscut, `f`
being holomorphic and injective on the disc. Then `Ω = A ∪ γ ∪ B`
(`TauCeti.image_ball_eq_union_image_crosscut`), and the two sides are open, so a frontier point of
`Ω` — which lies in `closure Ω` but not in `Ω` — is a frontier point of `A`, a frontier point of
`B`, or an adherent point of `γ`:

> `frontier Ω = frontier Ω ∩ frontier A ∪ frontier Ω ∩ closure γ ∪ frontier Ω ∩ frontier B`

(`TauCeti.frontier_image_ball_eq_union`). This is the sense in which a crosscut *cuts the image
boundary in two*: the two boundary pieces `frontier Ω ∩ frontier A` and `frontier Ω ∩ frontier B`
cover `frontier Ω` apart from a middle piece no wider than the image crosscut itself
(`TauCeti.diam_frontier_inter_closure_image_ball_inter_sphere_le`), which by the length–area
estimate of `Conformal/ShortCrosscut.lean` can be made as small as desired.

The far side is bounded by its own boundary piece exactly as the near side is: the frontier of `B`
lies on the image crosscut and on `frontier Ω`
(`TauCeti.frontier_image_ball_diff_closedBall_subset`), so an enclosing set for
`frontier Ω ∩ frontier B` bounds the width of `B`
(`TauCeti.diam_image_ball_diff_closedBall_le`), mirroring
`TauCeti.diam_image_ball_inter_ball_le`. Either side may therefore be the one that is shown small.

## The ends of the image crosscut, and the set joining them

The middle piece is not merely small, it is *nonempty*
(`TauCeti.nonempty_frontier_inter_closure_image_ball_inter_sphere`): the crosscut runs from one
endpoint on `sphere c r` to the other, and along such an endpoint `f` has a cluster value, which is
adherent to `γ` and — a conformal map being proper — is not attained, hence lies on `frontier Ω`.
So the ends of the image crosscut really do land on the boundary of the image.

That is what the last theorem consumes. If `frontier Ω` is uniformly locally connected — which by
`TauCeti.IsCompact.isUniformlyLocallyConnected` is exactly local connectedness, `frontier Ω` being
compact — then for every `ε > 0` there is a single `δ > 0`, independent of the boundary point `ζ`
and of the crosscut radius `ρ`, such that an image crosscut of diameter less than `δ` has its whole
middle piece enclosed in a *connected* subset of `frontier Ω` of diameter at most `ε`
(`TauCeti.exists_isConnected_subset_frontier_image_ball_of_diam_lt`). This is the second of the two
geometric inputs that `Conformal/CutDiameter.lean` names — "local connectedness of `∂Ω` supplies
the small connected `E` joining its two ends" — the first being the length–area estimate.

What is **not** proved here, and is what still separates layer **L5** of
`TauCetiRoadmap/ConformalMapping/README.md` from its milestone, is that the resulting `E` encloses
the boundary piece: that `frontier Ω ∩ frontier A` is contained in the small connected set together
with the image crosscut. Classically that is a separation argument about the closed curve formed by
the image crosscut and the joining boundary set, and no part of it is claimed below.

## Generality

In accordance with the generality bar of `ConformalMapping/README.md`, which fixes scalar `ℂ` for
every theorem added in layers L0–L6, everything here is stated for maps of `ℂ`. The two inputs that
are not about conformality are stated at their own generality elsewhere: `TauCeti.diam_frontier`
for an arbitrary real normed space and `TauCeti.IsUniformlyLocallyConnected` for an arbitrary
pseudometric space.

## Main results

* `TauCeti.image_ball_eq_union_image_crosscut` — the image of the disc is the union of the images
  of the two sides of a crosscut and of the crosscut itself.
* `TauCeti.frontier_image_ball_diff_closedBall_subset` and
  `TauCeti.diam_image_ball_diff_closedBall_le` — the far-side companions of
  `TauCeti.frontier_image_ball_inter_ball_subset` and `TauCeti.diam_image_ball_inter_ball_le`.
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
formalization rather than a temporary shim. It consumes the L0–L3 shim
`TauCeti.isOpen_image_of_differentiableOn_of_injOn`, to be refactored onto Mathlib's open mapping
API once the upstream work lands.

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
  refine Subset.antisymm (fun y hy => ?_) fun y hy => ?_
  · rcases lt_trichotomy (dist y ζ) ρ with h | h | h
    · exact Or.inl (Or.inl ⟨hy, mem_ball.mpr h⟩)
    · exact Or.inl (Or.inr ⟨hy, mem_sphere.mpr h⟩)
    · exact Or.inr ⟨hy, fun hc => absurd (mem_closedBall.mp hc) (not_le.mpr h)⟩
  · rcases hy with (⟨hy, -⟩ | ⟨hy, -⟩) | ⟨hy, -⟩ <;> exact hy

/-! ## The far side of the crosscut -/

/-- **The boundary of the image of the far side of a crosscut lies on the image crosscut and on the
boundary of the image domain.** The mirror of `TauCeti.frontier_image_ball_inter_ball_subset`, with
the same proof read across the crosscut: a frontier point of `f '' (ball c r \ closedBall ζ ρ)`
that is not a frontier point of `f '' ball c r` is a value `f w` with `dist w ζ = ρ`, the case
`dist w ζ > ρ` placing it inside an open set disjoint from its own frontier and the case
`dist w ζ < ρ` placing it inside an open set that injectivity makes disjoint from a set it is in
the closure of. -/
theorem frontier_image_ball_diff_closedBall_subset (hd : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) :
    frontier (f '' (ball c r \ closedBall ζ ρ))
      ⊆ f '' (ball c r ∩ sphere ζ ρ) ∪ frontier (f '' ball c r) := by
  have hBopen : IsOpen (f '' (ball c r \ closedBall ζ ρ)) :=
    isOpen_image_of_differentiableOn_of_injOn (isOpen_ball.sdiff isClosed_closedBall)
      (hd.mono sdiff_subset) (hinj.mono sdiff_subset)
  intro p hp
  have hpΩ : p ∈ closure (f '' ball c r) := closure_mono (image_mono sdiff_subset) hp.1
  rw [closure_eq_self_union_frontier] at hpΩ
  rcases hpΩ with hpin | hpfr
  · obtain ⟨w, hw, rfl⟩ := hpin
    rcases lt_trichotomy (dist w ζ) ρ with hlt | heq | hgt
    · exfalso
      have hAopen : IsOpen (f '' (ball c r ∩ ball ζ ρ)) :=
        isOpen_image_of_differentiableOn_of_injOn (isOpen_ball.inter isOpen_ball)
          (hd.mono inter_subset_left) (hinj.mono inter_subset_left)
      have hwA : f w ∈ f '' (ball c r ∩ ball ζ ρ) := ⟨w, ⟨hw, mem_ball.mpr hlt⟩, rfl⟩
      obtain ⟨q, ⟨u, hu, hfu⟩, ⟨v, hv, hfv⟩⟩ := mem_closure_iff.mp hp.1 _ hAopen hwA
      have huv : u = v := hinj hu.1 hv.1 (hfu.trans hfv.symm)
      subst huv
      exact hv.2 (ball_subset_closedBall hu.2)
    · exact Or.inl ⟨w, ⟨hw, mem_sphere.mpr heq⟩, rfl⟩
    · exact absurd
        ⟨⟨w, ⟨hw, fun hc => absurd (mem_closedBall.mp hc) (not_le.mpr hgt)⟩, rfl⟩, hp⟩
        (eq_empty_iff_forall_notMem.mp hBopen.inter_frontier_eq (f w))
  · exact Or.inr hpfr

/-- **The image of the far side of a crosscut is no wider than the image crosscut together with the
boundary piece it cuts off.** The mirror of `TauCeti.diam_image_ball_inter_ball_le`: whichever of
the two sides a boundary piece is supplied for, that side is the one bounded. -/
theorem diam_image_ball_diff_closedBall_le (hd : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hb : IsBounded (f '' ball c r)) {E : Set ℂ} (hE : IsBounded E)
    (hEsub : frontier (f '' ball c r) ∩ frontier (f '' (ball c r \ closedBall ζ ρ)) ⊆ E) :
    diam (f '' (ball c r \ closedBall ζ ρ)) ≤ diam (f '' (ball c r ∩ sphere ζ ρ) ∪ E) := by
  have harc : IsBounded (f '' (ball c r ∩ sphere ζ ρ)) := hb.subset (image_mono inter_subset_left)
  rw [← diam_frontier (hb.subset (image_mono sdiff_subset))]
  refine diam_mono (fun p hp => ?_) (harc.union hE)
  rcases frontier_image_ball_diff_closedBall_subset hd hinj hp with h | h
  · exact Or.inl h
  · exact Or.inr (hEsub ⟨h, hp⟩)

/-! ## The crosscut cuts the boundary of the image in two -/

/-- **The boundary of the image of a disc is covered by the boundaries of the two sides of a
crosscut together with the closure of the image crosscut.**

A frontier point of the open set `f '' ball c r` lies in its closure but not in it, so by
`TauCeti.image_ball_eq_union_image_crosscut` it is adherent to one of the three pieces while
belonging to none of them; for the two sides, which are open, being adherent and not belonging is
exactly being on the frontier. -/
theorem frontier_image_ball_subset_union (hd : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) :
    frontier (f '' ball c r) ⊆
      frontier (f '' (ball c r ∩ ball ζ ρ)) ∪ closure (f '' (ball c r ∩ sphere ζ ρ)) ∪
        frontier (f '' (ball c r \ closedBall ζ ρ)) := by
  have hΩopen : IsOpen (f '' ball c r) :=
    isOpen_image_of_differentiableOn_of_injOn isOpen_ball hd hinj
  have hAopen : IsOpen (f '' (ball c r ∩ ball ζ ρ)) :=
    isOpen_image_of_differentiableOn_of_injOn (isOpen_ball.inter isOpen_ball)
      (hd.mono inter_subset_left) (hinj.mono inter_subset_left)
  have hBopen : IsOpen (f '' (ball c r \ closedBall ζ ρ)) :=
    isOpen_image_of_differentiableOn_of_injOn (isOpen_ball.sdiff isClosed_closedBall)
      (hd.mono sdiff_subset) (hinj.mono sdiff_subset)
  intro p hp
  have hpn : p ∉ f '' ball c r := by
    rw [hΩopen.frontier_eq] at hp
    exact hp.2
  have hpc : p ∈ closure (f '' ball c r) := hp.1
  rw [image_ball_eq_union_image_crosscut f c ζ r ρ, closure_union, closure_union] at hpc
  rcases hpc with (h | h) | h
  · refine Or.inl (Or.inl ?_)
    rw [hAopen.frontier_eq]
    exact ⟨h, fun hc => hpn (image_mono inter_subset_left hc)⟩
  · exact Or.inl (Or.inr h)
  · refine Or.inr ?_
    rw [hBopen.frontier_eq]
    exact ⟨h, fun hc => hpn (image_mono sdiff_subset hc)⟩

/-- **A circular crosscut cuts the boundary of the image into two pieces and a middle piece.** The
equality form of `TauCeti.frontier_image_ball_subset_union`: `frontier (f '' ball c r)` is the union
of the two *boundary pieces* the crosscut determines — its intersections with the frontiers of the
images of the two sides — and of the part of it adherent to the image crosscut, which
`TauCeti.diam_frontier_inter_closure_image_ball_inter_sphere_le` shows to be no wider than the
image crosscut itself. -/
theorem frontier_image_ball_eq_union (hd : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) :
    frontier (f '' ball c r) =
      frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ)) ∪
        frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) ∪
        frontier (f '' ball c r) ∩ frontier (f '' (ball c r \ closedBall ζ ρ)) := by
  rw [← inter_union_distrib_left, ← inter_union_distrib_left]
  exact (inter_eq_left.mpr (frontier_image_ball_subset_union hd hinj)).symm

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

/-- **The ends of the image crosscut land on the boundary of the image.** For `f` holomorphic and
injective on `ball c r` with bounded image, and a genuine circular crosscut at a boundary point `ζ`,
the middle piece `frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ))` is nonempty.

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

/-! ## The small connected set joining the ends -/

/-- **A uniformly locally connected image boundary encloses the middle piece of every short image
crosscut in a small connected boundary set.** For `f` holomorphic and injective on `ball c r` with
bounded image and `frontier (f '' ball c r)` uniformly locally connected, every `ε > 0` admits a
single `δ > 0` — independent of the boundary point `ζ` and of the crosscut radius `ρ` — such that
an image crosscut of diameter less than `δ` has its middle piece contained in a connected subset of
`frontier (f '' ball c r)` of diameter at most `ε`.

This is the second of the two geometric inputs of
`TauCeti.exists_continuousOn_closedBall_eqOn_of_forall_exists_diam_union_le`, the first being the
length–area estimate `TauCeti.exists_diam_image_ball_inter_sphere_le`. It does not by itself
discharge that criterion, whose enclosing set has to contain the whole boundary piece
`frontier (f '' ball c r) ∩ frontier (f '' (ball c r ∩ ball ζ ρ))` and not only the middle piece.

The joining set is built by taking every candidate at once, as in
`TauCeti.IsUniformlyLocallyConnected.locallyConnectedSpace`: fix a point `a` of the middle piece,
which is nonempty by `TauCeti.nonempty_frontier_inter_closure_image_ball_inter_sphere`, and unite
all preconnected subsets of the boundary that contain `a` and stay within `ε / 2` of it. The union
is preconnected because its members share `a`, has diameter at most `ε` by the triangle inequality,
and swallows the middle piece because the middle piece has diameter less than `δ`, so uniform local
connectedness joins each of its points to `a` by such a set. -/
theorem exists_isConnected_subset_frontier_image_ball_of_diam_lt
    (hd : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hb : IsBounded (f '' ball c r))
    (hulc : IsUniformlyLocallyConnected (frontier (f '' ball c r))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ζ : ℂ, dist ζ c = r → ∀ ρ : ℝ, 0 < ρ → ρ < 2 * r →
      diam (f '' (ball c r ∩ sphere ζ ρ)) < δ →
        ∃ S ⊆ frontier (f '' ball c r), IsConnected S ∧
          frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ)) ⊆ S ∧ diam S ≤ ε := by
  obtain ⟨δ, hδ, hjoin⟩ := hulc.exists_isConnected (by linarith : (0 : ℝ) < ε / 2)
  refine ⟨δ, hδ, fun ζ hζ ρ hρ hρr hdiam => ?_⟩
  obtain ⟨a, ha⟩ :=
    nonempty_frontier_inter_closure_image_ball_inter_sphere hd hinj hb hζ hρ hρr
  have hPb : IsBounded (frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ))) :=
    ((hb.subset (image_mono inter_subset_left)).closure).subset inter_subset_right
  have hPdiam : diam (frontier (f '' ball c r) ∩ closure (f '' (ball c r ∩ sphere ζ ρ))) < δ :=
    lt_of_le_of_lt (diam_frontier_inter_closure_image_ball_inter_sphere_le hb ζ ρ) hdiam
  -- every preconnected boundary set through `a` that stays within `ε / 2` of it
  set 𝒞 : Set (Set ℂ) := {T : Set ℂ | T ⊆ frontier (f '' ball c r) ∧ IsPreconnected T ∧ a ∈ T ∧
    ∀ x ∈ T, dist x a ≤ ε / 2} with h𝒞
  have haS : a ∈ ⋃₀ 𝒞 :=
    ⟨{a}, ⟨singleton_subset_iff.mpr ha.1, isPreconnected_singleton, rfl,
      fun x hx => by rw [mem_singleton_iff.mp hx, dist_self]; linarith⟩, rfl⟩
  refine ⟨⋃₀ 𝒞, ?_, ⟨⟨a, haS⟩, isPreconnected_sUnion a 𝒞 (fun T hT => hT.2.2.1)
    fun T hT => hT.2.1⟩, ?_, ?_⟩
  · rintro x ⟨T, hT, hxT⟩
    exact hT.1 hxT
  · intro b hbP
    obtain ⟨C, hCs, hCconn, hCa, hCb, hCsmall⟩ := hjoin a ha.1 b hbP.1
      (lt_of_le_of_lt (dist_le_diam_of_mem hPb ha hbP) hPdiam)
    exact ⟨C, ⟨hCs, hCconn.isPreconnected, hCa, fun x hx => hCsmall x hx a hCa⟩, hCb⟩
  · refine diam_le_of_forall_dist_le hε.le ?_
    rintro x ⟨T, hT, hxT⟩ y ⟨T', hT', hyT'⟩
    have hx : dist x a ≤ ε / 2 := hT.2.2.2 x hxT
    have hy : dist y a ≤ ε / 2 := hT'.2.2.2 y hyT'
    calc dist x y ≤ dist x a + dist a y := dist_triangle x a y
      _ ≤ ε / 2 + ε / 2 := by rw [dist_comm a y]; linarith
      _ = ε := by ring

end TauCeti
