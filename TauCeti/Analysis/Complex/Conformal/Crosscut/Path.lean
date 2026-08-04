/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.Path
public import TauCeti.Analysis.Complex.Conformal.Crosscut.EndpointLimit
import TauCeti.Analysis.Complex.Conformal.Crosscut.Endpoints
import TauCeti.Analysis.Complex.Conformal.ShortCrosscut
import TauCeti.Analysis.Complex.Conformal.ClusterSet

/-!
# A finite-length image crosscut as a path

`Conformal/Crosscut/EndpointLimit.lean` proves that the image of a circular crosscut of finite
length has an honest limit at each of its two ends, and identifies its closure set-theoretically as
the open image crosscut together with those ends. This file packages the same curve as a
`Path`: its range is exactly that closure, it follows the usual angular parametrisation in its
interior, and that interior is injective when the holomorphic map is injective on the disc.

This is a topological input to layer **L5** of the conformal-mapping roadmap
(`TauCetiRoadmap/ConformalMapping/README.md`), the Carathéodory boundary correspondence. The next
separation step joins a closed image crosscut to one of the two arcs that its endpoints cut from
the Jordan boundary. The set-level description of the closure does not by itself supply the
continuous parametrisation that such an argument needs; the path below does.

## Construction

Write

`a = arg (c - ζ) - arccos (ρ / (2r))` and
`b = arg (c - ζ) + arccos (ρ / (2r))`.

The open interval `Ioo a b` parametrises `ball c r ∩ sphere ζ ρ`. At every point of its frontier,
the endpoint-limit theorem gives a limit of `f` along the crosscut. Composing with `circleMap`
gives a limit in the angular parameter, so the general cluster-set extension criterion produces a
continuous extension on `Icc a b`. Reparametrising that extension by
`AffineMap.lineMap a b : [0, 1] → [a, b]` gives the path.

The range statement follows from compactness: the image of `Icc a b`, the closure of `Ioo a b`,
is the closure of the image of `Ioo a b`. Interior injectivity uses only the injectivity of `f`,
Mathlib's `Complex.eq_of_circleMap_eq`, and the fact that `b - a < 2π`.

## Main result

* `TauCeti.exists_path_range_eq_closure_image_ball_inter_sphere` — a finite-length circular image
  crosscut of a holomorphic injection is the interior of a path whose range is its closure.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself. Mathlib
supplies `Path`, affine segments, and the injectivity of `circleMap` on an interval shorter than a
full turn; it has no boundary-crosscut or endpoint-limit result. No Mathlib source is vendored.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2–2.3.
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open Bornology Complex Filter Metric Set Topology
open scoped Real

variable {f : ℂ → ℂ} {c ζ : ℂ} {r ρ : ℝ}

/-- The affine parametrisation from the unit interval to `Icc a b` sends its interior into
`Ioo a b`. -/
private theorem lineMap_mem_Ioo {a b : ℝ} (hab : a < b) {t : unitInterval}
    (ht : t ∈ Ioo (0 : unitInterval) 1) : AffineMap.lineMap a b (t : ℝ) ∈ Ioo a b := by
  rw [← openSegment_eq_Ioo hab]
  exact lineMap_mem_openSegment ℝ a b (by simpa using ht)

/-- A point of the unit interval is an endpoint or lies in its interior. -/
private theorem unitInterval_eq_zero_or_eq_one_or_mem_Ioo (t : unitInterval) :
    t = 0 ∨ t = 1 ∨ t ∈ Ioo (0 : unitInterval) 1 := by
  by_cases h0 : t = 0
  · exact Or.inl h0
  by_cases h1 : t = 1
  · exact Or.inr (Or.inl h1)
  exact Or.inr (Or.inr ⟨lt_of_le_of_ne t.2.1 (fun h => h0 h.symm),
    lt_of_le_of_ne t.2.2 h1⟩)

/-- **A finite-length circular image crosscut is the interior of a path.** Let `ζ` lie on
`sphere c r`, and let `0 < ρ < 2r`, so that `ball c r ∩ sphere ζ ρ` is a genuine circular
crosscut. If `f` is holomorphic and injective on `ball c r` and the image crosscut has finite
`TauCeti.circleImageLength`, then there are endpoints `u`, `v` and a path from `u` to `v` such
that

* the range of the path is exactly `closure (f '' (ball c r ∩ sphere ζ ρ))`;
* its two endpoints lie on `frontier (f '' ball c r)`;
* its only possible repeated value is the common value of its two endpoints; and
* on the open unit interval it is the usual angular parametrisation of the image crosscut.

The endpoints are not asserted to be distinct. This is necessary: the hypotheses available before
the Carathéodory boundary theorem do not exclude an image crosscut closing up at the boundary. The
interior remains injective; `Conformal/Crosscut/BoundaryEnds.lean` separately identifies its two
endpoint limits as boundary points.
-/
theorem exists_path_range_eq_closure_image_ball_inter_sphere (hζ : dist ζ c = r)
    (hρ : 0 < ρ) (hρr : ρ < 2 * r) (hf : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) (hfin : circleImageLength f (ball c r) ζ ρ ≠ ⊤) :
    ∃ u v, ∃ γ : Path u v,
      range γ = closure (f '' (ball c r ∩ sphere ζ ρ)) ∧
        u ∈ frontier (f '' ball c r) ∧ v ∈ frontier (f '' ball c r) ∧
        (∀ ⦃x y⦄, γ x = γ y →
          x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)) ∧
        ∀ t ∈ Ioo (0 : unitInterval) 1,
          γ t = f (circleMap ζ ρ
            (AffineMap.lineMap
              ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
              ((c - ζ).arg + Real.arccos (ρ / (2 * r))) (t : ℝ))) := by
  let φ : ℝ := Real.arccos (ρ / (2 * r))
  let a : ℝ := (c - ζ).arg - φ
  let b : ℝ := (c - ζ).arg + φ
  let g : ℝ → ℂ := fun θ => f (circleMap ζ ρ θ)
  have hφ0 : 0 < φ := by
    exact Real.arccos_pos.mpr ((div_lt_one (by linarith)).mpr hρr)
  have hφπ2 : φ < π / 2 := by
    exact Real.arccos_lt_pi_div_two.mpr (div_pos hρ (by linarith))
  have hab : a < b := by simp only [a, b]; linarith
  have hab2π : b - a < 2 * π := by simp only [a, b]; linarith [Real.pi_pos]
  have hcrosscut : ball c r ∩ sphere ζ ρ = circleMap ζ ρ '' Ioo a b := by
    simpa only [a, b, φ] using ball_inter_sphere_eq_circleMap_image_Ioo hζ hρ hρr
  have hclosedCrosscut : closedBall c r ∩ sphere ζ ρ = circleMap ζ ρ '' Icc a b := by
    simpa only [a, b, φ] using closedBall_inter_sphere_eq_circleMap_image_Icc hζ hρ hρr
  have hmaps : MapsTo (circleMap ζ ρ) (Ioo a b) (ball c r) := by
    intro θ hθ
    have : circleMap ζ ρ θ ∈ ball c r ∩ sphere ζ ρ := by
      rw [hcrosscut]
      exact ⟨θ, hθ, rfl⟩
    exact this.1
  have hgcont : ContinuousOn g (Ioo a b) := by
    intro θ hθ
    simpa only [g, Function.comp_def] using
      (hf.continuousOn _ (hmaps hθ)).comp
        (continuous_circleMap ζ ρ).continuousAt.continuousWithinAt hmaps
  have hgb : IsBounded (g '' Ioo a b) := by
    have hb := isBounded_image_ball_inter_sphere_of_circleImageLength_ne_top hζ hρ hf hfin
    rw [hcrosscut, image_image] at hb
    simpa only [g, Function.comp_def] using hb
  have hgsub : ∀ θ ∈ frontier (Ioo a b), (clusterSetOn g (Ioo a b) θ).Subsingleton := by
    intro θ hθ
    have hθcl : θ ∈ closure (Ioo a b) := frontier_subset_closure hθ
    have hθIcc : θ ∈ Icc a b := by
      rwa [closure_Ioo hab.ne] at hθcl
    have he : circleMap ζ ρ θ ∈ closedBall c r ∩ sphere ζ ρ := by
      rw [hclosedCrosscut]
      exact ⟨θ, hθIcc, rfl⟩
    obtain ⟨v, hv⟩ :=
      exists_tendsto_nhdsWithin_ball_inter_sphere hζ hρ hρr hf hfin he
    have hcircle : Tendsto (circleMap ζ ρ) (𝓝[Ioo a b] θ)
        (𝓝[circleMap ζ ρ '' Ioo a b] (circleMap ζ ρ θ)) :=
      (continuous_circleMap ζ ρ).continuousAt.continuousWithinAt.tendsto_nhdsWithin_image
    have hlim : Tendsto g (𝓝[Ioo a b] θ) (𝓝 v) := by
      rw [hcrosscut] at hv
      simpa only [g, Function.comp_def] using hv.comp hcircle
    rw [clusterSetOn_eq_singleton_of_tendsto hθcl hlim]
    exact subsingleton_singleton
  obtain ⟨F, hFc, hFg⟩ :=
    exists_continuousOn_closure_eqOn_of_isBounded isOpen_Ioo hgcont hgb hgsub
  have hcl : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  have hFcIcc : ContinuousOn F (Icc a b) := by simpa only [hcl] using hFc
  have hr : 0 < r := by linarith
  have hFfrontier : ∀ θ ∈ frontier (Ioo a b), F θ ∈ frontier (f '' ball c r) := by
    intro θ hθ
    have hθcl : θ ∈ closure (Ioo a b) := frontier_subset_closure hθ
    have hθIcc : θ ∈ Icc a b := by rwa [hcl] at hθcl
    have heclosed : circleMap ζ ρ θ ∈ closedBall c r ∩ sphere ζ ρ := by
      rw [hclosedCrosscut]
      exact ⟨θ, hθIcc, rfl⟩
    have hecl : circleMap ζ ρ θ ∈ closure (ball c r ∩ sphere ζ ρ) := by
      rw [closure_ball_inter_sphere hζ hρ hρr]
      exact heclosed
    have hθends : θ = a ∨ θ = b := by
      rw [frontier_Ioo hab] at hθ
      simpa only [mem_insert_iff, mem_singleton_iff] using hθ
    have hesphere : circleMap ζ ρ θ ∈ sphere c r ∩ sphere ζ ρ := by
      rw [sphere_inter_sphere_eq_pair_circleMap hζ hρ hρr]
      rcases hθends with rfl | rfl
      · simpa only [a, b, φ] using mem_insert
          (circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r))))
          {circleMap ζ ρ ((c - ζ).arg + Real.arccos (ρ / (2 * r)))}
      · simpa only [a, b, φ] using mem_insert_of_mem
          (circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r))))
          (mem_singleton _)
    have hefrontier : circleMap ζ ρ θ ∈ frontier (ball c r) := by
      rw [frontier_ball c hr.ne']
      exact hesphere.1
    obtain ⟨v, hv⟩ :=
      exists_tendsto_nhdsWithin_ball_inter_sphere hζ hρ hρr hf hfin heclosed
    have hcircle : Tendsto (circleMap ζ ρ) (𝓝[Ioo a b] θ)
        (𝓝[circleMap ζ ρ '' Ioo a b] (circleMap ζ ρ θ)) :=
      (continuous_circleMap ζ ρ).continuousAt.continuousWithinAt.tendsto_nhdsWithin_image
    have hvangle : Tendsto g (𝓝[Ioo a b] θ) (𝓝 v) := by
      rw [hcrosscut] at hv
      simpa only [g, Function.comp_def] using hv.comp hcircle
    have hFangle : Tendsto g (𝓝[Ioo a b] θ) (𝓝 (F θ)) := by
      exact ((hFc θ hθcl).mono subset_closure).congr'
        (hFg.eventuallyEq_of_mem self_mem_nhdsWithin)
    have hne : (𝓝[Ioo a b] θ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hθcl
    have hFv : F θ = v := tendsto_nhds_unique' hne hFangle hvangle
    have hvcluster : v ∈ clusterSetOn f (ball c r ∩ sphere ζ ρ) (circleMap ζ ρ θ) := by
      rw [clusterSetOn_eq_singleton_of_tendsto hecl hv]
      exact mem_singleton v
    rw [hFv]
    exact clusterSetOn_subset_frontier_image isOpen_ball hf hinj hefrontier
      (clusterSetOn_mono inter_subset_left hvcluster)
  let γ : Path (F a) (F b) :=
    { toFun := fun t => F (AffineMap.lineMap a b (t : ℝ))
      continuous_toFun := by
        refine hFcIcc.comp_continuous ?_ ?_
        · fun_prop
        · intro t
          rw [← segment_eq_Icc hab.le]
          exact lineMap_mem_segment ℝ a b t.2
      source' := by simp
      target' := by simp }
  have hγformula : ∀ t ∈ Ioo (0 : unitInterval) 1,
      γ t = f (circleMap ζ ρ (AffineMap.lineMap a b (t : ℝ))) := by
    intro t ht
    exact hFg (lineMap_mem_Ioo hab ht)
  have hγrange : range γ = F '' Icc a b := by
    apply Set.Subset.antisymm
    · rintro y ⟨t, rfl⟩
      refine ⟨AffineMap.lineMap a b (t : ℝ), ?_, rfl⟩
      rw [← segment_eq_Icc hab.le]
      exact lineMap_mem_segment ℝ a b t.2
    · rintro y ⟨θ, hθ, rfl⟩
      have hlineImage : AffineMap.lineMap a b '' Icc (0 : ℝ) 1 = Icc a b := by
        rw [← segment_eq_image_lineMap ℝ a b, segment_eq_Icc hab.le]
      rw [← hlineImage] at hθ
      obtain ⟨t, ht, rfl⟩ := hθ
      exact ⟨⟨t, ht⟩, rfl⟩
  have hFimage : F '' Icc a b = closure (g '' Ioo a b) := by
    calc
      F '' Icc a b = F '' closure (Ioo a b) := by rw [hcl]
      _ = closure (F '' Ioo a b) :=
        image_closure_of_isCompact (by simpa only [hcl] using isCompact_Icc) hFc
      _ = closure (g '' Ioo a b) := by rw [hFg.image_eq]
  have hgimage : g '' Ioo a b = f '' (ball c r ∩ sphere ζ ρ) := by
    rw [hcrosscut, image_image]
  have hγinj : InjOn γ (Ioo (0 : unitInterval) 1) := by
    intro x hx y hy hxy
    have hxIoo := lineMap_mem_Ioo hab hx
    have hyIoo := lineMap_mem_Ioo hab hy
    have hxcross : circleMap ζ ρ (AffineMap.lineMap a b (x : ℝ)) ∈
        ball c r ∩ sphere ζ ρ := by
      rw [hcrosscut]
      exact ⟨_, hxIoo, rfl⟩
    have hycross : circleMap ζ ρ (AffineMap.lineMap a b (y : ℝ)) ∈
        ball c r ∩ sphere ζ ρ := by
      rw [hcrosscut]
      exact ⟨_, hyIoo, rfl⟩
    rw [hγformula x hx, hγformula y hy] at hxy
    have hcircle := hinj hxcross.1 hycross.1 hxy
    have hangle : AffineMap.lineMap a b (x : ℝ) = AffineMap.lineMap a b (y : ℝ) := by
      apply eq_of_circleMap_eq hρ.ne' _ hcircle
      rw [abs_lt]
      constructor <;> linarith [hab2π, hxIoo.1, hxIoo.2, hyIoo.1, hyIoo.2]
    exact Subtype.ext ((AffineMap.lineMap_injective ℝ hab.ne) hangle)
  have ha : a ∈ frontier (Ioo a b) := by rw [frontier_Ioo hab]; exact mem_insert a {b}
  have hb : b ∈ frontier (Ioo a b) := by
    rw [frontier_Ioo hab]
    exact mem_insert_of_mem a (mem_singleton b)
  have hFa : F a ∈ frontier (f '' ball c r) := hFfrontier a ha
  have hFb : F b ∈ frontier (f '' ball c r) := hFfrontier b hb
  have hγzero : γ 0 ∈ frontier (f '' ball c r) := by
    simpa only [Path.source] using hFa
  have hγone : γ 1 ∈ frontier (f '' ball c r) := by
    simpa only [Path.target] using hFb
  have himageOpen : IsOpen (f '' ball c r) :=
    isOpen_image_of_differentiableOn_of_injOn isOpen_ball hf hinj
  have hγmem : ∀ t ∈ Ioo (0 : unitInterval) 1, γ t ∈ f '' ball c r := by
    intro t ht
    rw [hγformula t ht]
    exact ⟨circleMap ζ ρ (AffineMap.lineMap a b (t : ℝ)),
      hmaps (lineMap_mem_Ioo hab ht), rfl⟩
  have hγsimple : ∀ ⦃x y⦄, γ x = γ y →
      x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
    intro x y hxy
    rcases unitInterval_eq_zero_or_eq_one_or_mem_Ioo x with rfl | rfl | hx
    · rcases unitInterval_eq_zero_or_eq_one_or_mem_Ioo y with rfl | rfl | hy
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exfalso
        exact (himageOpen.frontier_eq ▸ hγzero).2 (by rw [hxy]; exact hγmem y hy)
    · rcases unitInterval_eq_zero_or_eq_one_or_mem_Ioo y with rfl | rfl | hy
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inl rfl
      · exfalso
        exact (himageOpen.frontier_eq ▸ hγone).2 (by rw [hxy]; exact hγmem y hy)
    · rcases unitInterval_eq_zero_or_eq_one_or_mem_Ioo y with rfl | rfl | hy
      · exfalso
        exact (himageOpen.frontier_eq ▸ hγzero).2 (by rw [← hxy]; exact hγmem x hx)
      · exfalso
        exact (himageOpen.frontier_eq ▸ hγone).2 (by rw [← hxy]; exact hγmem x hx)
      · exact Or.inl (hγinj hx hy hxy)
  refine ⟨F a, F b, γ, ?_, hFa, hFb, hγsimple, ?_⟩
  · rw [hγrange, hFimage, hgimage]
  · simpa only [a, b, φ] using hγformula

end TauCeti
