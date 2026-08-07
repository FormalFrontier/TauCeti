/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.Order.ExtendFrom
public import Mathlib.Topology.Path
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# The path traced by a function on an open interval

A curve is often produced not as a `Path` but as a function `g : ℝ → X` defined on an *open*
interval `Ioo a b`, continuous there, and converging at each of the two ends. This file turns such
a function into an honest `Path` between its two limits, `TauCeti.Path.ofContinuousOnIoo`, and
records the three facts a consumer of that path needs: what its values are on the interior of the
unit interval, what its range is, and when it repeats a value.

The construction is Mathlib's `extendFrom` composed with the affine reparametrisation
`AffineMap.lineMap a b : [0, 1] → [a, b]`. Mathlib's `continuousOn_Icc_extendFrom_Ioo` says that
`extendFrom (Ioo a b) g` is continuous on the *closed* interval as soon as `g` is continuous on the
open one and has a limit at each end, and `eq_lim_at_left_extendFrom_Ioo` /
`eq_lim_at_right_extendFrom_Ioo` identify its two endpoint values with those limits; the
reparametrisation carries all of that to the unit interval. Nothing else is needed: the two
endpoint limits are exactly the data that a `Path` between them requires.

The range is `closure (g '' Ioo a b)` rather than `g '' Ioo a b`: the path traverses the closed
interval, and the image of a compact set under a map continuous on it is the closure of the image
of the dense open part. So the closure of a curve given on an open interval is automatically
path-connected, with the curve itself as the interior of the traversal — which is what makes this
construction useful, since the endpoints are in general *not* values of `g`.

## Simplicity

Whether the path is simple is not a matter of the extension but of `g` and of the endpoints, and
is treated here in the reparametrisation-only form, with no topology on `X` at all:

* `TauCeti.injOn_Ioo_of_eq_lineMap` — the path is injective on the interior of the unit interval
  as soon as `g` is injective on `Ioo a b`, because `AffineMap.lineMap a b` is;
* `TauCeti.eq_or_eq_endpoints_of_notMem_of_forall_mem_Ioo` — if in addition the interior stays
  inside a set that neither endpoint value belongs to, the only repetition left is between the two
  endpoints. That is the statement "the path is a simple arc, except that it may be a loop".

Both are stated for a bare function `unitInterval → X` satisfying the parametrisation formula,
rather than for `TauCeti.Path.ofContinuousOnIoo` itself, because a consumer typically receives its
path from an existential and knows only the formula.

## Main declarations

* `TauCeti.Path.ofContinuousOnIoo` — the path traced by a function continuous on `Ioo a b` with a
  limit at each end, from the limit at `a` to the limit at `b`.
* `TauCeti.Path.ofContinuousOnIoo_apply` and
  `TauCeti.Path.ofContinuousOnIoo_apply_of_mem_Ioo` — its values, in general and on the interior.
* `TauCeti.Path.range_ofContinuousOnIoo` — its range is `closure (g '' Ioo a b)`.
* `TauCeti.mapsTo_Ioo_of_eq_lineMap`, `TauCeti.injOn_Ioo_of_eq_lineMap` and
  `TauCeti.eq_or_eq_endpoints_of_notMem_of_forall_mem_Ioo` — the reparametrisation-only lemmas
  above; the last of them runs on Mathlib's trichotomy
  `Set.eq_endpoints_or_mem_Ioo_of_mem_Icc`, read on the unit interval.

## Generality

The construction asks `X` to be regular (for `continuousOn_Icc_extendFrom_Ioo`) and Hausdorff (for
`extendFrom` to pin the endpoint values down and for the range computation), which is what Mathlib
asks of the ingredients; a metric space, the case every consumer here instantiates, satisfies both.
The simplicity lemmas assume nothing about `X`. The interval is a real one, as `AffineMap.lineMap`
and `unitInterval` are.
-/

public section

namespace TauCeti

open Filter Set Topology
open scoped unitInterval

section Reparametrisation

variable {X : Type*} {a b : ℝ} {g : ℝ → X} {γ : I → X}

/-- The affine parametrisation from the unit interval to `Icc a b` sends the whole unit interval
into `Icc a b`. -/
private theorem lineMap_mem_Icc (hab : a ≤ b) (t : I) :
    AffineMap.lineMap a b (t : ℝ) ∈ Icc a b :=
  segment_eq_Icc hab ▸ lineMap_mem_segment ℝ a b t.2

/-- The affine parametrisation from the unit interval to `Icc a b` sends its interior into
`Ioo a b`. -/
private theorem lineMap_mem_Ioo (hab : a < b) {t : I}
    (ht : t ∈ Ioo (0 : I) 1) : AffineMap.lineMap a b (t : ℝ) ∈ Ioo a b := by
  rw [← openSegment_eq_Ioo hab]
  exact lineMap_mem_openSegment ℝ a b (by simpa using ht)

/-- **The interior of an affinely reparametrised curve stays where the curve does.** If `γ` follows
`g` along `AffineMap.lineMap a b` on the interior of the unit interval and `g` maps `Ioo a b` into
`S`, then `γ` maps that interior into `S`. -/
theorem mapsTo_Ioo_of_eq_lineMap {S : Set X} (hab : a < b) (hmaps : MapsTo g (Ioo a b) S)
    (hγ : ∀ t ∈ Ioo (0 : I) 1, γ t = g (AffineMap.lineMap a b (t : ℝ))) :
    MapsTo γ (Ioo (0 : I) 1) S := fun _t ht =>
  (hγ _ ht) ▸ hmaps (lineMap_mem_Ioo hab ht)

/-- **An affinely reparametrised curve is injective on the interior of the unit interval whenever
the curve is injective on the open interval.** Only injectivity of `AffineMap.lineMap a b` is spent,
so nothing is assumed of `X`. -/
theorem injOn_Ioo_of_eq_lineMap (hab : a < b) (hinj : InjOn g (Ioo a b))
    (hγ : ∀ t ∈ Ioo (0 : I) 1, γ t = g (AffineMap.lineMap a b (t : ℝ))) :
    InjOn γ (Ioo (0 : I) 1) := by
  intro x hx y hy hxy
  rw [hγ x hx, hγ y hy] at hxy
  exact Subtype.ext ((AffineMap.lineMap_injective ℝ hab.ne)
    (hinj (lineMap_mem_Ioo hab hx) (lineMap_mem_Ioo hab hy) hxy))

/-- **A path repeats only at its endpoints when its interior avoids both endpoint values.**
If `γ` maps the open interval into `S`, neither endpoint value lies in `S`, and `γ` is injective on
the open interval, then any repeated value is a common value of the two endpoints.

Purely a statement about function values: neither `γ` nor `S` carries any topology, and a `Path`
specializes automatically through its coercion. The frontier/open-set form is derived at the call
site. -/
theorem eq_or_eq_endpoints_of_notMem_of_forall_mem_Ioo {S : Set X}
    (hzero : γ 0 ∉ S) (hone : γ 1 ∉ S)
    (hmem : ∀ t ∈ Ioo (0 : I) 1, γ t ∈ S)
    (hinj : InjOn γ (Ioo (0 : I) 1)) ⦃x y : I⦄ (hxy : γ x = γ y) :
    x = y ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc (a := (0 : I)) (b := 1) x.2 with rfl | rfl | hx
  · rcases eq_endpoints_or_mem_Ioo_of_mem_Icc (a := (0 : I)) (b := 1) y.2 with rfl | rfl | hy
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact absurd (by rw [hxy]; exact hmem y hy) hzero
  · rcases eq_endpoints_or_mem_Ioo_of_mem_Icc (a := (0 : I)) (b := 1) y.2 with rfl | rfl | hy
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inl rfl
    · exact absurd (by rw [hxy]; exact hmem y hy) hone
  · rcases eq_endpoints_or_mem_Ioo_of_mem_Icc (a := (0 : I)) (b := 1) y.2 with rfl | rfl | hy
    · exact absurd (by rw [← hxy]; exact hmem x hx) hzero
    · exact absurd (by rw [← hxy]; exact hmem x hx) hone
    · exact Or.inl (hinj hx hy hxy)

end Reparametrisation

namespace Path

variable {X : Type*} [TopologicalSpace X] [RegularSpace X] [T2Space X]
  {a b : ℝ} {u v : X} {g : ℝ → X}

/-- **The path traced by a function on an open interval.** If `g` is continuous on `Ioo a b`, tends
to `u` at `a` from the right and to `v` at `b` from the left, then `g` traverses a path from `u` to
`v`: the continuous extension `extendFrom (Ioo a b) g` of `g` to `Icc a b`, read along the affine
parametrisation `AffineMap.lineMap a b` of `Icc a b` by the unit interval.

Its values on the interior of the unit interval are those of `g`
(`TauCeti.Path.ofContinuousOnIoo_apply_of_mem_Ioo`) and its range is `closure (g '' Ioo a b)`
(`TauCeti.Path.range_ofContinuousOnIoo`); the endpoints `u` and `v` need not themselves be values
of `g`.

The definition is not exposed; `TauCeti.Path.ofContinuousOnIoo_apply` characterizes it. -/
noncomputable def ofContinuousOnIoo (hab : a < b) (hg : ContinuousOn g (Ioo a b))
    (hu : Tendsto g (𝓝[>] a) (𝓝 u)) (hv : Tendsto g (𝓝[<] b) (𝓝 v)) : Path u v where
  toFun t := extendFrom (Ioo a b) g (AffineMap.lineMap a b (t : ℝ))
  continuous_toFun :=
    (continuousOn_Icc_extendFrom_Ioo hg hu hv).comp_continuous
      (by simp only [AffineMap.lineMap_apply_ring]; fun_prop)
      fun t => lineMap_mem_Icc hab.le t
  source' := by
    simpa only [Set.Icc.coe_zero, AffineMap.lineMap_apply_zero] using
      eq_lim_at_left_extendFrom_Ioo hab hu
  target' := by
    simpa only [Set.Icc.coe_one, AffineMap.lineMap_apply_one] using
      eq_lim_at_right_extendFrom_Ioo hab hv

/-- The path traced by `g` is the continuous extension of `g` read along the affine parametrisation
of `Icc a b` by the unit interval. -/
theorem ofContinuousOnIoo_apply (hab : a < b) (hg : ContinuousOn g (Ioo a b))
    (hu : Tendsto g (𝓝[>] a) (𝓝 u)) (hv : Tendsto g (𝓝[<] b) (𝓝 v)) (t : I) :
    ofContinuousOnIoo hab hg hu hv t = extendFrom (Ioo a b) g (AffineMap.lineMap a b (t : ℝ)) :=
  (rfl)

/-- **On the interior of the unit interval the path traced by `g` is `g` itself**, along the affine
parametrisation. The endpoints are excluded because there `g` need not be defined at all; that is
what makes the construction more than a reparametrisation. -/
theorem ofContinuousOnIoo_apply_of_mem_Ioo (hab : a < b) (hg : ContinuousOn g (Ioo a b))
    (hu : Tendsto g (𝓝[>] a) (𝓝 u)) (hv : Tendsto g (𝓝[<] b) (𝓝 v)) {t : I}
    (ht : t ∈ Ioo (0 : I) 1) :
    ofContinuousOnIoo hab hg hu hv t = g (AffineMap.lineMap a b (t : ℝ)) :=
  extendFrom_extends hg _ (lineMap_mem_Ioo hab ht)

/-- **The range of the path traced by `g` is the closure of the curve.** The path traverses the
closed interval `Icc a b`, which is the closure of `Ioo a b` and compact, so its image under a map
continuous there is the closure of the image of `Ioo a b`. In particular the closure of a curve
defined on an open interval and converging at both ends is path-connected. -/
theorem range_ofContinuousOnIoo (hab : a < b) (hg : ContinuousOn g (Ioo a b))
    (hu : Tendsto g (𝓝[>] a) (𝓝 u)) (hv : Tendsto g (𝓝[<] b) (𝓝 v)) :
    range (ofContinuousOnIoo hab hg hu hv) = closure (g '' Ioo a b) := by
  have hcl : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  have hparam : range (fun t : I => AffineMap.lineMap a b (t : ℝ)) = Icc a b := by
    rw [show (fun t : I => AffineMap.lineMap a b (t : ℝ))
        = AffineMap.lineMap a b ∘ (Subtype.val : I → ℝ) from rfl, range_comp,
      Subtype.range_coe_subtype, ofPred_mem_eq, ← segment_eq_image_lineMap ℝ a b,
      segment_eq_Icc hab.le]
  have hcont : ContinuousOn (extendFrom (Ioo a b) g) (closure (Ioo a b)) :=
    hcl ▸ continuousOn_Icc_extendFrom_Ioo hg hu hv
  have heq : EqOn (extendFrom (Ioo a b) g) g (Ioo a b) := fun x hx => extendFrom_extends hg x hx
  rw [show (⇑(ofContinuousOnIoo hab hg hu hv)) =
      extendFrom (Ioo a b) g ∘ fun t : I => AffineMap.lineMap a b (t : ℝ) from rfl,
    range_comp, hparam, ← hcl, image_closure_of_isCompact (hcl ▸ isCompact_Icc) hcont,
    heq.image_eq]

end Path

end TauCeti
