/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import TauCeti.Analysis.Complex.Conformal.Crosscut.EndpointLimit
import TauCeti.Analysis.Complex.Conformal.Crosscut.Endpoints
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
turns those into limits of the angular composite at `a` and at `b`, which is what
`continuousOn_Icc_extendFrom_Ioo` asks for: `extendFrom (Ioo a b)` is then continuous on `Icc a b`
and agrees with the composite on `Ioo a b`. Pushing Mathlib's straight-line path `Path.segment a b`
forward along that extension with `Path.map'` gives the path, parametrised by
`AffineMap.lineMap a b : [0, 1] → [a, b]`.

The range statement follows from compactness: the image of `Icc a b`, the closure of `Ioo a b`,
is the closure of the image of `Ioo a b`. This construction does not need injectivity. When `f`
is injective on the disc, a companion theorem also places the endpoints on the image frontier and
shows that only the two endpoints can be identified. Interior injectivity uses only the
injectivity of `f`, Mathlib's `Complex.injOn_circleMap_of_abs_sub_le`, and the fact that
`b - a < 2π`.

## Main result

* `TauCeti.exists_path_range_eq_closure_image_ball_inter_sphere` — a finite-length circular image
  crosscut is the interior of a path whose range is its closure.
* `TauCeti.exists_path_range_eq_closure_image_ball_inter_sphere_of_injOn` — for a holomorphic
  injection, the path endpoints lie on the image frontier and no other values repeat.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself. Mathlib
supplies `Path`, affine segments, the `extendFrom` extension across an interval, and the injectivity
of `circleMap` on an interval shorter than a full turn; it has no boundary-crosscut or
endpoint-limit result. No Mathlib source is vendored.

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

/-- **The angular parametrisation of a finite-length image crosscut extends continuously to the
closed arc.** The composite `θ ↦ f (circleMap ζ ρ θ)` is continuous on `Ioo a b` and has a limit at
each endpoint, so `extendFrom` extends it to `closure (Ioo a b)`. -/
private theorem exists_continuousOn_closure_eqOn_comp_circleMap {a b : ℝ} (hab : a < b)
    (hgcont : ContinuousOn (fun θ => f (circleMap ζ ρ θ)) (Ioo a b))
    (hglim : ∀ θ ∈ frontier (Ioo a b), ∃ v,
      Tendsto (fun θ => f (circleMap ζ ρ θ)) (𝓝[Ioo a b] θ) (𝓝 v)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (closure (Ioo a b)) ∧
      EqOn F (fun θ => f (circleMap ζ ρ θ)) (Ioo a b) := by
  obtain ⟨la, hla⟩ := hglim a (by simp [frontier_Ioo hab])
  obtain ⟨lb, hlb⟩ := hglim b (by simp [frontier_Ioo hab])
  rw [nhdsWithin_Ioo_eq_nhdsGT hab] at hla
  rw [nhdsWithin_Ioo_eq_nhdsLT hab] at hlb
  exact ⟨extendFrom (Ioo a b) fun θ => f (circleMap ζ ρ θ),
    closure_Ioo hab.ne ▸ continuousOn_Icc_extendFrom_Ioo hgcont hla hlb,
    extendFrom_extends hgcont⟩

/-- **At any angle landing on the closed crosscut, the limit is reached along both approaches.**
The limit of `f` along the crosscut at `circleMap ζ ρ θ` is also the limit of the angular
composite `θ ↦ f (circleMap ζ ρ θ)` along `Ioo a b`.

The angle `θ` is constrained only through `he`: it may be any angle whose point lies on the closed
crosscut, not merely one of the two endpoints. The frontier case is all that is used. -/
private theorem exists_tendsto_nhdsWithin_and_tendsto_comp_circleMap
    (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (hf : DifferentiableOn ℂ f (ball c r))
    (hfin : circleImageLength f (ball c r) ζ ρ ≠ ⊤) {a b θ : ℝ}
    (hcrosscut : ball c r ∩ sphere ζ ρ = circleMap ζ ρ '' Ioo a b)
    (he : circleMap ζ ρ θ ∈ closedBall c r ∩ sphere ζ ρ) :
    ∃ v, Tendsto f (𝓝[ball c r ∩ sphere ζ ρ] (circleMap ζ ρ θ)) (𝓝 v) ∧
      Tendsto (fun θ => f (circleMap ζ ρ θ)) (𝓝[Ioo a b] θ) (𝓝 v) := by
  obtain ⟨v, hv⟩ := exists_tendsto_nhdsWithin_ball_inter_sphere hζ hρ hρr hf hfin he
  have hcircle : Tendsto (circleMap ζ ρ) (𝓝[Ioo a b] θ)
      (𝓝[circleMap ζ ρ '' Ioo a b] (circleMap ζ ρ θ)) :=
    (continuous_circleMap ζ ρ).continuousAt.continuousWithinAt.tendsto_nhdsWithin_image
  refine ⟨v, hv, ?_⟩
  rw [hcrosscut] at hv
  simpa only [Function.comp_def] using hv.comp hcircle

/-- **A finite-length circular image crosscut is the interior of a path.** Let `ζ` lie on
`sphere c r`, and let `0 < ρ < 2r`, so that `ball c r ∩ sphere ζ ρ` is a genuine circular
crosscut. If `f` is holomorphic on `ball c r` and the image crosscut has finite
`TauCeti.circleImageLength`, then there are endpoints `u`, `v` and a path from `u` to `v` whose
range is exactly `closure (f '' (ball c r ∩ sphere ζ ρ))` and which has the usual angular
parametrisation on the open unit interval.

The two additional `Tendsto` conclusions identify `u` and `v` with the endpoint limits of the
crosscut. No injectivity is needed for this construction. The companion theorem
`TauCeti.exists_path_range_eq_closure_image_ball_inter_sphere_of_injOn` records the stronger
frontier and no-repetition properties available when `f` is injective.
-/
theorem exists_path_range_eq_closure_image_ball_inter_sphere (hζ : dist ζ c = r)
    (hρ : 0 < ρ) (hρr : ρ < 2 * r) (hf : DifferentiableOn ℂ f (ball c r))
    (hfin : circleImageLength f (ball c r) ζ ρ ≠ ⊤) :
    ∃ u v, ∃ γ : Path u v,
      range γ = closure (f '' (ball c r ∩ sphere ζ ρ)) ∧
        Tendsto f
          (𝓝[ball c r ∩ sphere ζ ρ]
            (circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r))))) (𝓝 u) ∧
        Tendsto f
          (𝓝[ball c r ∩ sphere ζ ρ]
            (circleMap ζ ρ ((c - ζ).arg + Real.arccos (ρ / (2 * r))))) (𝓝 v) ∧
        ∀ t ∈ Ioo (0 : unitInterval) 1,
          γ t = f (circleMap ζ ρ
            (AffineMap.lineMap
              ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
              ((c - ζ).arg + Real.arccos (ρ / (2 * r))) (t : ℝ))) := by
  let φ : ℝ := Real.arccos (ρ / (2 * r))
  let a : ℝ := (c - ζ).arg - φ
  let b : ℝ := (c - ζ).arg + φ
  let g : ℝ → ℂ := fun θ => f (circleMap ζ ρ θ)
  have hφ0 : 0 < φ := Real.arccos_pos.mpr ((div_lt_one (by linarith)).mpr hρr)
  have hab : a < b := by simp only [a, b]; linarith
  have hcrosscut : ball c r ∩ sphere ζ ρ = circleMap ζ ρ '' Ioo a b := by
    simpa only [a, b, φ] using ball_inter_sphere_eq_circleMap_image_Ioo hζ hρ hρr
  have hclosedCrosscut : closedBall c r ∩ sphere ζ ρ = circleMap ζ ρ '' Icc a b := by
    simpa only [a, b, φ] using closedBall_inter_sphere_eq_circleMap_image_Icc hζ hρ hρr
  have hglim : ∀ θ ∈ frontier (Ioo a b), ∃ v,
      Tendsto f (𝓝[ball c r ∩ sphere ζ ρ] (circleMap ζ ρ θ)) (𝓝 v) ∧
        Tendsto g (𝓝[Ioo a b] θ) (𝓝 v) := fun θ hθ =>
    exists_tendsto_nhdsWithin_and_tendsto_comp_circleMap hζ hρ hρr hf hfin hcrosscut
      (hclosedCrosscut.ge ⟨θ, closure_Ioo hab.ne ▸ frontier_subset_closure hθ, rfl⟩)
  have hmaps : MapsTo (circleMap ζ ρ) (Ioo a b) (ball c r) := fun θ hθ =>
    (hcrosscut.ge ⟨θ, hθ, rfl⟩).1
  have hgcont : ContinuousOn g (Ioo a b) := fun θ hθ => by
    simpa only [Function.comp_def] using (hf.continuousOn _ (hmaps hθ)).comp
      (continuous_circleMap ζ ρ).continuousAt.continuousWithinAt hmaps
  obtain ⟨F, hFc, hFg⟩ :=
    exists_continuousOn_closure_eqOn_comp_circleMap hab hgcont
      fun θ hθ => (hglim θ hθ).imp fun _ h => h.2
  have hcl : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  have hFends : ∀ θ ∈ frontier (Ioo a b),
      Tendsto f (𝓝[ball c r ∩ sphere ζ ρ] (circleMap ζ ρ θ)) (𝓝 (F θ)) := by
    intro θ hθ
    obtain ⟨v, hv, hvangle⟩ := hglim θ hθ
    have hθcl : θ ∈ closure (Ioo a b) := frontier_subset_closure hθ
    rwa [tendsto_nhds_unique' (mem_closure_iff_nhdsWithin_neBot.mp hθcl)
      (((hFc θ hθcl).mono subset_closure).congr'
        (hFg.eventuallyEq_of_mem self_mem_nhdsWithin)) hvangle]
  -- Traverse `Icc a b` by `Path.segment a b`, then push it forward along `F` with `Path.map'`.
  have hFcseg : ContinuousOn F (range (Path.segment a b)) := by
    rw [Path.range_segment, segment_eq_Icc hab.le, ← hcl]; exact hFc
  -- Mathlib has `Path.map_coe` for `Path.map` but no `map'_coe`, so unfold pointwise.
  have hcoe : ⇑((Path.segment a b).map' hFcseg) = F ∘ ⇑(Path.segment a b) := by ext t; rfl
  have hγformula : ∀ t ∈ Ioo (0 : unitInterval) 1, ((Path.segment a b).map' hFcseg) t
      = f (circleMap ζ ρ (AffineMap.lineMap a b (t : ℝ))) := fun t ht => by
    rw [hcoe, Function.comp_apply, Path.segment_apply]
    exact hFg (lineMap_mem_Ioo hab ht)
  have hFimage : F '' Icc a b = closure (g '' Ioo a b) := by
    rw [← hcl, image_closure_of_isCompact (hcl ▸ isCompact_Icc) hFc, hFg.image_eq]
  refine ⟨F a, F b, (Path.segment a b).map' hFcseg, ?_, ?_, ?_, ?_⟩
  · rw [hcoe, range_comp, Path.range_segment, segment_eq_Icc hab.le, hFimage, hcrosscut,
      image_image]
  · simpa only [a, b, φ] using hFends a (by simp [frontier_Ioo hab])
  · simpa only [a, b, φ] using hFends b (by simp [frontier_Ioo hab])
  · simpa only [a, b, φ] using hγformula

/-- **A path given by `g ∘ circleMap` along an affine reparametrisation is injective.** If the arc
`Ioo a b` spans at most a full turn and `g` is injective on a set the arc maps into, then the path
is injective on the open interval.

Injectivity of `circleMap` on the arc is what `b - a ≤ 2 * π` buys; `g` supplies the rest. Nothing
is assumed of the codomain, and `g` need only be injective on the set the arc lands in. -/
private theorem injOn_Ioo_of_eq_circleMap_lineMap {X : Type*} {S : Set ℂ} {g : ℂ → X}
    {γ : unitInterval → X} {a b : ℝ} (hab : a < b) (hab2π : b - a ≤ 2 * π) (hρ : ρ ≠ 0)
    (hinj : InjOn g S) (hmaps : MapsTo (circleMap ζ ρ) (Ioo a b) S)
    (hγformula : ∀ t ∈ Ioo (0 : unitInterval) 1,
      γ t = g (circleMap ζ ρ (AffineMap.lineMap a b (t : ℝ)))) :
    InjOn γ (Ioo (0 : unitInterval) 1) := by
  intro x hx y hy hxy
  have hxIoo := lineMap_mem_Ioo hab hx
  have hyIoo := lineMap_mem_Ioo hab hy
  rw [hγformula x hx, hγformula y hy] at hxy
  have hcircle := hinj (hmaps hxIoo) (hmaps hyIoo) hxy
  have hangle := injOn_circleMap_of_abs_sub_le (c := ζ) hρ
    (by rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hab)]; exact hab2π)
    (by rw [uIoc_of_le hab.le]; exact ⟨hxIoo.1, hxIoo.2.le⟩)
    (by rw [uIoc_of_le hab.le]; exact ⟨hyIoo.1, hyIoo.2.le⟩) hcircle
  exact Subtype.ext ((AffineMap.lineMap_injective ℝ hab.ne) hangle)

/-- **An endpoint limit of a circular image crosscut lies on the frontier of the image.** For `f`
differentiable and injective on `ball c r`, a limit of `f` along the crosscut at either endpoint of
its defining arc is a boundary point of `f '' ball c r`.

The endpoints are named by the arccos formula rather than through a local abbreviation, so the
statement stands on its own. -/
private theorem mem_frontier_image_ball_of_tendsto_arc_endpoint
    (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r)) {θ : ℝ}
    (hθends : θ = (c - ζ).arg - Real.arccos (ρ / (2 * r)) ∨
      θ = (c - ζ).arg + Real.arccos (ρ / (2 * r)))
    {w : ℂ} (hw : Tendsto f (𝓝[ball c r ∩ sphere ζ ρ] (circleMap ζ ρ θ)) (𝓝 w)) :
    w ∈ frontier (f '' ball c r) := by
  have hφ0 : 0 < Real.arccos (ρ / (2 * r)) :=
    Real.arccos_pos.mpr ((div_lt_one (by linarith)).mpr hρr)
  have heclosed : circleMap ζ ρ θ ∈ closedBall c r ∩ sphere ζ ρ := by
    rw [closedBall_inter_sphere_eq_circleMap_image_Icc hζ hρ hρr]
    refine ⟨θ, ?_, rfl⟩
    rcases hθends with rfl | rfl
    · exact ⟨le_rfl, by linarith⟩
    · exact ⟨by linarith, le_rfl⟩
  have hecl : circleMap ζ ρ θ ∈ closure (ball c r ∩ sphere ζ ρ) := by
    rw [closure_ball_inter_sphere hζ hρ hρr]
    exact heclosed
  have hesphere : circleMap ζ ρ θ ∈ sphere c r ∩ sphere ζ ρ := by
    rw [sphere_inter_sphere_eq_pair_circleMap hζ hρ hρr]
    rcases hθends with rfl | rfl
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ (mem_singleton _)
  have hr : 0 < r := by linarith
  have hefrontier : circleMap ζ ρ θ ∈ frontier (ball c r) := by
    rw [frontier_ball c hr.ne']
    exact hesphere.1
  have hwcluster : w ∈ clusterSetOn f (ball c r ∩ sphere ζ ρ) (circleMap ζ ρ θ) := by
    rw [clusterSetOn_eq_singleton_of_tendsto hecl hw]
    exact mem_singleton w
  exact (clusterSetOn_inter_sphere_subset_frontier_inter_closure_image (U := ball c r) (ζ := ζ)
    (ρ := ρ) isOpen_ball hf hinj hefrontier hwcluster).1

/-- **A path repeats only at its endpoints when its interior avoids both endpoint values.**
If `γ` maps the open interval into `S`, neither endpoint value lies in `S`, and `γ` is injective on
the open interval, then any repeated value is a common value of the two endpoints.

Purely a statement about function values: neither `γ` nor `S` carries any topology, and a `Path`
specializes automatically through its coercion. The frontier/open-set form is derived at the call
site. -/
private theorem eq_or_eq_endpoints_of_notMem_of_forall_mem_Ioo {X : Type*}
    {γ : unitInterval → X} {S : Set X}
    (hzero : γ 0 ∉ S) (hone : γ 1 ∉ S)
    (hmem : ∀ t ∈ Ioo (0 : unitInterval) 1, γ t ∈ S)
    (hinj : InjOn γ (Ioo (0 : unitInterval) 1)) ⦃x y : unitInterval⦄ (hxy : γ x = γ y) :
    x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  rcases unitInterval_eq_zero_or_eq_one_or_mem_Ioo x with rfl | rfl | hx
  · rcases unitInterval_eq_zero_or_eq_one_or_mem_Ioo y with rfl | rfl | hy
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact absurd (by rw [hxy]; exact hmem y hy) hzero
  · rcases unitInterval_eq_zero_or_eq_one_or_mem_Ioo y with rfl | rfl | hy
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inl rfl
    · exact absurd (by rw [hxy]; exact hmem y hy) hone
  · rcases unitInterval_eq_zero_or_eq_one_or_mem_Ioo y with rfl | rfl | hy
    · exact absurd (by rw [← hxy]; exact hmem x hx) hzero
    · exact absurd (by rw [← hxy]; exact hmem x hx) hone
    · exact Or.inl (hinj hx hy hxy)

/-- **An injective finite-length circular image crosscut has no repetitions except possibly at its
endpoints.** Under the hypotheses of
`TauCeti.exists_path_range_eq_closure_image_ball_inter_sphere`, assume additionally that `f` is
injective on `ball c r`. Then the endpoints of the resulting path lie on
`frontier (f '' ball c r)` and remain identified by their endpoint limits, its interior is
injective, and no endpoint value occurs in the interior. Thus the only possible repeated value is
a common value of the two endpoints.

The endpoints need not be distinct: before the Carathéodory boundary theorem, the hypotheses do
not exclude an image crosscut closing up at the boundary.
-/
theorem exists_path_range_eq_closure_image_ball_inter_sphere_of_injOn
    (hζ : dist ζ c = r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hinj : InjOn f (ball c r))
    (hfin : circleImageLength f (ball c r) ζ ρ ≠ ⊤) :
    ∃ u v, ∃ γ : Path u v,
      range γ = closure (f '' (ball c r ∩ sphere ζ ρ)) ∧
        Tendsto f
          (𝓝[ball c r ∩ sphere ζ ρ]
            (circleMap ζ ρ ((c - ζ).arg - Real.arccos (ρ / (2 * r))))) (𝓝 u) ∧
        Tendsto f
          (𝓝[ball c r ∩ sphere ζ ρ]
            (circleMap ζ ρ ((c - ζ).arg + Real.arccos (ρ / (2 * r))))) (𝓝 v) ∧
        u ∈ frontier (f '' ball c r) ∧ v ∈ frontier (f '' ball c r) ∧
        (∀ ⦃x y⦄, γ x = γ y →
          x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)) ∧
        ∀ t ∈ Ioo (0 : unitInterval) 1,
          γ t = f (circleMap ζ ρ
            (AffineMap.lineMap
              ((c - ζ).arg - Real.arccos (ρ / (2 * r)))
              ((c - ζ).arg + Real.arccos (ρ / (2 * r))) (t : ℝ))) := by
  obtain ⟨u, v, γ, hγrange, hu, hv, hγformula⟩ :=
    exists_path_range_eq_closure_image_ball_inter_sphere hζ hρ hρr hf hfin
  let φ : ℝ := Real.arccos (ρ / (2 * r))
  let a : ℝ := (c - ζ).arg - φ
  let b : ℝ := (c - ζ).arg + φ
  have hφ0 : 0 < φ := by
    exact Real.arccos_pos.mpr ((div_lt_one (by linarith)).mpr hρr)
  have hab : a < b := by simp only [a, b]; linarith
  have hφπ2 : φ < π / 2 := by
    exact Real.arccos_lt_pi_div_two.mpr (div_pos hρ (by linarith))
  have hab2π : b - a < 2 * π := by simp only [a, b]; linarith [Real.pi_pos]
  have hcrosscut : ball c r ∩ sphere ζ ρ = circleMap ζ ρ '' Ioo a b := by
    simpa only [a, b, φ] using ball_inter_sphere_eq_circleMap_image_Ioo hζ hρ hρr
  have hmaps : MapsTo (circleMap ζ ρ) (Ioo a b) (ball c r) := by
    intro θ hθ
    have : circleMap ζ ρ θ ∈ ball c r ∩ sphere ζ ρ := by
      rw [hcrosscut]
      exact ⟨θ, hθ, rfl⟩
    exact this.1
  have hr : 0 < r := by linarith
  have hua : Tendsto f (𝓝[ball c r ∩ sphere ζ ρ] (circleMap ζ ρ a)) (𝓝 u) := by
    simpa only [a, φ] using hu
  have hvb : Tendsto f (𝓝[ball c r ∩ sphere ζ ρ] (circleMap ζ ρ b)) (𝓝 v) := by
    simpa only [b, φ] using hv
  have hufrontier : u ∈ frontier (f '' ball c r) :=
    mem_frontier_image_ball_of_tendsto_arc_endpoint hζ hρ hρr hf hinj (Or.inl rfl) hua
  have hvfrontier : v ∈ frontier (f '' ball c r) :=
    mem_frontier_image_ball_of_tendsto_arc_endpoint hζ hρ hρr hf hinj (Or.inr rfl) hvb
  have hγformula' : ∀ t ∈ Ioo (0 : unitInterval) 1,
      γ t = f (circleMap ζ ρ (AffineMap.lineMap a b (t : ℝ))) := by
    simpa only [a, b, φ] using hγformula
  have hγinj : InjOn γ (Ioo (0 : unitInterval) 1) :=
    injOn_Ioo_of_eq_circleMap_lineMap hab hab2π.le hρ.ne' hinj hmaps hγformula'
  have hγzero : γ 0 ∈ frontier (f '' ball c r) := by
    simpa only [Path.source] using hufrontier
  have hγone : γ 1 ∈ frontier (f '' ball c r) := by
    simpa only [Path.target] using hvfrontier
  have himageOpen : IsOpen (f '' ball c r) :=
    isOpen_image_of_differentiableOn_of_injOn isOpen_ball hf hinj
  have hγmem : ∀ t ∈ Ioo (0 : unitInterval) 1, γ t ∈ f '' ball c r := by
    intro t ht
    rw [hγformula' t ht]
    exact ⟨circleMap ζ ρ (AffineMap.lineMap a b (t : ℝ)),
      hmaps (lineMap_mem_Ioo hab ht), rfl⟩
  have hγsimple := eq_or_eq_endpoints_of_notMem_of_forall_mem_Ioo
    (himageOpen.frontier_eq ▸ hγzero).2 (himageOpen.frontier_eq ▸ hγone).2 hγmem hγinj
  exact ⟨u, v, γ, hγrange, hu, hv, hufrontier, hvfrontier, hγsimple, hγformula⟩

end TauCeti
