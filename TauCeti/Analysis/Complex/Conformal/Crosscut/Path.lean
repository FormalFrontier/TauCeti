/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Topology.Path
public import TauCeti.Analysis.Complex.Conformal.Crosscut.EndpointLimit
import TauCeti.Analysis.Complex.Conformal.Crosscut.Endpoints
import TauCeti.Analysis.Complex.Conformal.ClusterSet
import TauCeti.Topology.Path.ExtendIoo

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
turns those into limits of the angular composite `g = f ∘ circleMap ζ ρ` at `a` and at `b`, which
is exactly the data `TauCeti.Path.ofContinuousOnIoo` of `TauCeti/Topology/Path/ExtendIoo.lean`
consumes: a function continuous on an open interval with a limit at each end traces a path between
those two limits, whose range is the closure of the curve
(`TauCeti.Path.range_ofContinuousOnIoo`) and which follows `g` along
`AffineMap.lineMap a b : [0, 1] → [a, b]` in the interior
(`TauCeti.Path.ofContinuousOnIoo_apply_of_mem_Ioo`). All the holomorphy is spent before that
point, in producing the two endpoint limits.

This construction does not need injectivity. When `f` is injective on the disc, a companion
theorem also places the endpoints on the image frontier and shows that only the two endpoints can
be identified. Interior injectivity uses only the injectivity of `f`, Mathlib's
`Complex.injOn_circleMap_of_abs_sub_le`, the fact that `b - a < 2π`, and the injectivity of
`AffineMap.lineMap a b`; the last step, that a curve injective on the interior and avoiding both
endpoint values there can repeat only between its endpoints, is
`TauCeti.eq_or_eq_endpoints_of_notMem_of_forall_mem_Ioo` of the same file.

## Main result

* `TauCeti.exists_path_range_eq_closure_image_ball_inter_sphere` — a finite-length circular image
  crosscut is the interior of a path whose range is its closure.
* `TauCeti.exists_path_range_eq_closure_image_ball_inter_sphere_of_injOn` — for a holomorphic
  injection, the path endpoints lie on the image frontier and no other values repeat.

## Coordination with upstream Mathlib

Layer L5 is absent from
[mathlib4#33505](https://github.com/leanprover-community/mathlib4/pull/33505), the in-progress
human-curated Riemann-mapping-theorem effort, which stops at the mapping theorem itself. Mathlib
supplies `Path` and the injectivity of `circleMap` on an interval shorter than a full turn; the
extension of a curve across the two ends of an open interval is packaged as a path in
`TauCeti/Topology/Path/ExtendIoo.lean`. Mathlib has no boundary-crosscut or endpoint-limit result.
No Mathlib source is vendored.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, §2.2–2.3.
* P. L. Duren, *Univalent Functions*, Ch. 3.
-/

public section

namespace TauCeti

open Bornology Complex Filter Metric Set Topology
open scoped Real

variable {f : ℂ → ℂ} {c ζ : ℂ} {r ρ : ℝ}

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
  have hr : 0 < r := by linarith
  have hφ0 : 0 < φ := arccos_div_two_mul_pos hr hρr
  have hab : a < b := by simp only [a, b]; linarith
  have hcrosscut : ball c r ∩ sphere ζ ρ = circleMap ζ ρ '' Ioo a b := by
    simpa only [a, b, φ] using ball_inter_sphere_eq_circleMap_image_Ioo hζ hρ hρr
  have hclosedCrosscut : closedBall c r ∩ sphere ζ ρ = circleMap ζ ρ '' Icc a b := by
    simpa only [a, b, φ] using closedBall_inter_sphere_eq_circleMap_image_Icc hζ hρ hρr
  have hmaps : MapsTo (circleMap ζ ρ) (Ioo a b) (ball c r) := fun θ hθ =>
    (hcrosscut.ge ⟨θ, hθ, rfl⟩).1
  have hgcont : ContinuousOn g (Ioo a b) := fun θ hθ => by
    simpa only [Function.comp_def] using (hf.continuousOn _ (hmaps hθ)).comp
      (continuous_circleMap ζ ρ).continuousAt.continuousWithinAt hmaps
  -- The endpoint-limit theorem at the two ends of the arc, read both along the crosscut and along
  -- the angle: the latter is what `TauCeti.Path.ofContinuousOnIoo` consumes.
  obtain ⟨u, hu, huangle⟩ :=
    exists_tendsto_nhdsWithin_and_tendsto_comp_circleMap hζ hρ hρr hf hfin hcrosscut
      (hclosedCrosscut.ge ⟨a, left_mem_Icc.mpr hab.le, rfl⟩)
  obtain ⟨v, hv, hvangle⟩ :=
    exists_tendsto_nhdsWithin_and_tendsto_comp_circleMap hζ hρ hρr hf hfin hcrosscut
      (hclosedCrosscut.ge ⟨b, right_mem_Icc.mpr hab.le, rfl⟩)
  rw [nhdsWithin_Ioo_eq_nhdsGT hab] at huangle
  rw [nhdsWithin_Ioo_eq_nhdsLT hab] at hvangle
  refine ⟨u, v, Path.ofContinuousOnIoo hab hgcont huangle hvangle, ?_, ?_, ?_, ?_⟩
  · rw [Path.range_ofContinuousOnIoo, hcrosscut, image_image]
  · simpa only [a, φ] using hu
  · simpa only [b, φ] using hv
  · exact fun t ht => Path.ofContinuousOnIoo_apply_of_mem_Ioo hab hgcont huangle hvangle ht

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
  have hφ0 := arccos_div_two_mul_pos (show (0 : ℝ) < r by linarith) hρr
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

/-- **A path traced along an arc by an injective map is injective on the open unit interval, and
sends it into the image.** For a circle of nonzero radius `ρ`, suppose `g` is injective on `S`,
the arc `circleMap ζ ρ '' Ioo a b` stays inside `S` and is no longer than a full turn, and `γ` is
given on `Ioo 0 1` by `g` composed with the affine parametrisation of `Ioo a b`. Then `γ` is
injective on `Ioo 0 1` and maps it into `g '' S`.

Nothing is asserted at the two endpoints, where `γ` may well repeat a value. -/
private theorem injOn_Ioo_and_mapsTo_image_of_eq_circleMap_lineMap {X : Type*} {S : Set ℂ}
    {g : ℂ → X} {γ : unitInterval → X} {a b : ℝ} (hab : a < b) (hab2π : b - a ≤ 2 * π)
    (hρ : ρ ≠ 0) (hinj : InjOn g S) (hmaps : MapsTo (circleMap ζ ρ) (Ioo a b) S)
    (hγformula : ∀ t ∈ Ioo (0 : unitInterval) 1,
      γ t = g (circleMap ζ ρ (AffineMap.lineMap a b (t : ℝ)))) :
    InjOn γ (Ioo (0 : unitInterval) 1) ∧
      ∀ t ∈ Ioo (0 : unitInterval) 1, γ t ∈ g '' S := by
  have hline : ∀ t ∈ Ioo (0 : unitInterval) 1,
      AffineMap.lineMap a b (t : ℝ) ∈ Ioo a b := fun t ht => by
    rw [← openSegment_eq_Ioo hab]
    exact lineMap_mem_openSegment ℝ a b (by simpa using ht)
  -- `circleMap` is injective on an arc no longer than a full turn, so the angular composite is
  -- injective on `Ioo a b`; the affine parametrisation then carries that to `γ`
  have hcircle : InjOn (circleMap ζ ρ) (Ioo a b) :=
    (injOn_circleMap_of_abs_sub_le (c := ζ) hρ
      (by rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hab)]; exact hab2π)).mono
      (by rw [uIoc_of_le hab.le]; exact Ioo_subset_Ioc_self)
  have hginj : InjOn (g ∘ circleMap ζ ρ) (Ioo a b) := hinj.comp hcircle hmaps
  refine ⟨fun x hx y hy hxy => ?_, fun t ht => ?_⟩
  · rw [hγformula x hx, hγformula y hy] at hxy
    exact Subtype.ext
      (AffineMap.lineMap_injective ℝ hab.ne (hginj (hline x hx) (hline y hy) hxy))
  · rw [hγformula t ht]
    exact ⟨circleMap ζ ρ _, hmaps (hline t ht), rfl⟩

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
  have hr : 0 < r := by linarith
  have hφ0 : 0 < φ := arccos_div_two_mul_pos hr hρr
  have hab : a < b := by simp only [a, b]; linarith
  have hφπ2 : φ < π / 2 := arccos_div_two_mul_lt_pi_div_two hρ hr
  have hab2π : b - a < 2 * π := by simp only [a, b]; linarith [Real.pi_pos]
  have hcrosscut : ball c r ∩ sphere ζ ρ = circleMap ζ ρ '' Ioo a b := by
    simpa only [a, b, φ] using ball_inter_sphere_eq_circleMap_image_Ioo hζ hρ hρr
  have hmaps : MapsTo (circleMap ζ ρ) (Ioo a b) (ball c r) := fun θ hθ =>
    (hcrosscut.ge ⟨θ, hθ, rfl⟩).1
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
  obtain ⟨hγinj, hγmem⟩ :=
    injOn_Ioo_and_mapsTo_image_of_eq_circleMap_lineMap hab hab2π.le hρ.ne' hinj hmaps hγformula'
  have hγzero : γ 0 ∈ frontier (f '' ball c r) := by
    simpa only [Path.source] using hufrontier
  have hγone : γ 1 ∈ frontier (f '' ball c r) := by
    simpa only [Path.target] using hvfrontier
  have himageOpen : IsOpen (f '' ball c r) :=
    isOpen_image_of_differentiableOn_of_injOn isOpen_ball hf hinj
  have hγsimple := eq_or_eq_endpoints_of_notMem_of_forall_mem_Ioo
    (himageOpen.frontier_eq ▸ hγzero).2 (himageOpen.frontier_eq ▸ hγone).2 hγmem hγinj
  exact ⟨u, v, γ, hγrange, hu, hv, hufrontier, hvfrontier, hγsimple, hγformula⟩

end TauCeti
