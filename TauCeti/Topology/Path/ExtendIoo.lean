/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Path
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Hausdorff

/-!
# The path traced by a function on an open interval

A curve is often produced not as a `Path` but as a function `g : ℝ → X` defined on an *open*
interval `Ioo a b`, continuous there, and converging at each of the two ends. This file turns such
a function into an honest `Path` between its two limits, `TauCeti.Path.ofContinuousOnIoo`, and
records what its values are on the interior of the unit interval and what its range is.

The construction is the extension `TauCeti.extendIoo a b u v g` of `g` across the two ends of the
interval by the prescribed values `u` and `v`, composed with the affine reparametrisation
`AffineMap.lineMap a b : [0, 1] → [a, b]`. Because those two values are *given* rather than
recovered as limits, the continuity of the extension on `Icc a b`
(`TauCeti.continuousOn_Icc_extendIoo`) needs no separation assumption on `X`, unlike Mathlib's
`continuousOn_Icc_extendFrom_Ioo` for `extendFrom`, which must locate the limits and so asks for a
regular codomain, and `eq_lim_at_left_extendFrom_Ioo`, which asks for a Hausdorff one. Nothing else
is needed: the two endpoint limits are exactly the data that a `Path` between them requires.

The range is `closure (g '' Ioo a b)` rather than `g '' Ioo a b`: the path traverses the closed
interval, and the image of a compact set under a map continuous on it is the closure of the image
of the dense open part. So the closure of a curve given on an open interval is automatically
path-connected, with the curve itself as the interior of the traversal — which is what makes this
construction useful, since the endpoints are in general *not* values of `g`.

## Simplicity

Whether the path is simple is not a matter of the extension but of `g` and of the endpoints, and
the one step of that argument which is not a plain composition is recorded here, in the
reparametrisation-only form and with no topology on `X` at all:
`TauCeti.eq_or_eq_endpoints_of_notMem_of_forall_mem_Ioo` says that if a curve on the unit interval
is injective on the interior, and that interior stays inside a set to which neither endpoint value
belongs, then the only repetition left is between the two endpoints. That is the statement "the
path is a simple arc, except that it may be a loop".

It is stated for a bare function `unitInterval → X`, with no hypothesis relating it to `g` or to
the extension, rather than for `TauCeti.Path.ofContinuousOnIoo` itself: a consumer typically
receives its path from an existential and knows only a parametrisation formula for it, which it
uses to establish the membership and injectivity hypotheses; a `Path` specializes through its
coercion. Injectivity on the interior is likewise left to the call site, being the injectivity of
`g` composed with that of `AffineMap.lineMap a b`.

## Main declarations

* `TauCeti.extendIoo` — a function on `Ioo a b`, extended across both ends by prescribed values,
  with `TauCeti.extendIoo_apply_of_mem_Ioo`, `TauCeti.extendIoo_apply_of_le_left` and
  `TauCeti.extendIoo_apply_of_left_lt_of_right_le` computing it at every point, and
  `TauCeti.continuousOn_Icc_extendIoo`, its continuity on `Icc a b`.
* `TauCeti.Path.ofContinuousOnIoo` — the path traced by a function continuous on `Ioo a b` with a
  limit at each end, from the limit at `a` to the limit at `b`.
* `TauCeti.Path.ofContinuousOnIoo_apply` and
  `TauCeti.Path.ofContinuousOnIoo_apply_of_mem_Ioo` — its values, in general and on the interior.
* `TauCeti.Path.range_ofContinuousOnIoo` — its range is `closure (g '' Ioo a b)`.
* `TauCeti.eq_or_eq_endpoints_of_notMem_of_forall_mem_Ioo` — the simplicity lemma above; it runs on
  Mathlib's trichotomy `Set.eq_endpoints_or_mem_Ioo_of_mem_Icc`, read on the unit interval.

## Generality

The extension and its continuity are stated over an arbitrary linearly ordered domain with an
order-closed topology; only the path is real, `AffineMap.lineMap` and `unitInterval` being so. The
path and its values ask nothing of `X` beyond a topology; only the range computation is Hausdorff,
the image of a compact set having to be closed there. The simplicity lemma assumes nothing about
`X` at all.
-/

public section

namespace TauCeti

open Filter Set Topology
open scoped unitInterval

section Reparametrisation

variable {X : Type*} {a b : ℝ} {γ : I → X}

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

section Extend

variable {X α : Type*} [LinearOrder α] {a b x : α} {u v : X} {g : α → X}

/-- **A function on an open interval, extended across both of its ends by prescribed values.**
`TauCeti.extendIoo a b u v g` agrees with `g` on `Ioo a b` and takes the value `u` on `Iic a`; when
`a < b` it takes the value `v` on `Ici b`, so that in particular it is `u` at `a` and `v` at `b`.
The two outer branches run over the whole of `Iic a` and `Ici b`, rather than over the endpoints
alone, so that the definition computes everywhere and carries no side condition. The
nondegeneracy `a < b` is not part of the definition, and is needed for the right-hand branch only:
if instead `b ≤ a`, the interval is empty and the extension is `u` on `Iic a` and `v` on `Ioi a`,
so that `b` itself is sent to `u`. The value is therefore computed at every point of `α`,
degenerate intervals included, by `TauCeti.extendIoo_apply_of_mem_Ioo`,
`TauCeti.extendIoo_apply_of_le_left` and `TauCeti.extendIoo_apply_of_left_lt_of_right_le`, whose
hypotheses are exactly the three branch conditions.

Mathlib's `extendFrom` instead *recovers* the end values as limits, which is why its continuity
theorem `continuousOn_Icc_extendFrom_Ioo` asks for a regular codomain and its identification
theorem `eq_lim_at_left_extendFrom_Ioo` for a Hausdorff one. Here the end values are given, and
`TauCeti.continuousOn_Icc_extendIoo` needs neither. -/
noncomputable def extendIoo (a b : α) (u v : X) (g : α → X) : α → X :=
  fun x => if x ≤ a then u else if b ≤ x then v else g x

/-- Inside the open interval the extension is the function itself. -/
@[simp]
theorem extendIoo_apply_of_mem_Ioo (hx : x ∈ Ioo a b) : extendIoo a b u v g x = g x := by
  simp [extendIoo, hx.1.not_ge, hx.2.not_ge]

/-- At and below the left end the extension takes the prescribed value `u`. -/
@[simp]
theorem extendIoo_apply_of_le_left (hx : x ≤ a) : extendIoo a b u v g x = u := by
  simp [extendIoo, hx]

/-- Above the left end and at or above the right end the extension takes the prescribed value `v`.
These are exactly the conditions of the second branch, so together with
`TauCeti.extendIoo_apply_of_mem_Ioo` and `TauCeti.extendIoo_apply_of_le_left` this computes the
extension at every point, degenerate intervals included. -/
@[simp]
theorem extendIoo_apply_of_left_lt_of_right_le (hax : a < x) (hx : b ≤ x) :
    extendIoo a b u v g x = v := by
  simp [extendIoo, hax.not_ge, hx]

/-- **A function continuous on an open interval and converging at both ends extends continuously
to the closed interval.** The extension is `TauCeti.extendIoo` by the two limits; being handed
them, the proof glues at the two ends and asks nothing of `X` beyond a topology. -/
theorem continuousOn_Icc_extendIoo [TopologicalSpace α] [OrderClosedTopology α]
    [TopologicalSpace X] (hab : a < b)
    (hg : ContinuousOn g (Ioo a b)) (hu : Tendsto g (𝓝[>] a) (𝓝 u))
    (hv : Tendsto g (𝓝[<] b) (𝓝 v)) : ContinuousOn (extendIoo a b u v g) (Icc a b) := by
  have hleft : ContinuousWithinAt (extendIoo a b u v g) (Icc a b) a := by
    refine ContinuousWithinAt.mono ?_ Icc_subset_Ici_self
    rw [← Ioi_insert, continuousWithinAt_insert_self]
    have heq : g =ᶠ[𝓝[>] a] extendIoo a b u v g := by
      filter_upwards [Ioo_mem_nhdsGT hab] with y hy using (extendIoo_apply_of_mem_Ioo hy).symm
    simpa only [ContinuousWithinAt, extendIoo_apply_of_le_left le_rfl] using hu.congr' heq
  have hright : ContinuousWithinAt (extendIoo a b u v g) (Icc a b) b := by
    refine ContinuousWithinAt.mono ?_ Icc_subset_Iic_self
    rw [← Iio_insert, continuousWithinAt_insert_self]
    have heq : g =ᶠ[𝓝[<] b] extendIoo a b u v g := by
      filter_upwards [Ioo_mem_nhdsLT hab] with y hy using (extendIoo_apply_of_mem_Ioo hy).symm
    simpa only [ContinuousWithinAt, extendIoo_apply_of_left_lt_of_right_le hab le_rfl] using
      hv.congr' heq
  intro x hx
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hx with rfl | rfl | hx
  · exact hleft
  · exact hright
  · have hmem : Ioo a b ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx
    refine ContinuousAt.continuousWithinAt ((hg.continuousAt hmem).congr ?_)
    filter_upwards [hmem] with y hy using (extendIoo_apply_of_mem_Ioo hy).symm

end Extend

namespace Path

variable {X : Type*} [TopologicalSpace X] {a b : ℝ} {u v : X} {g : ℝ → X}

/-- **The path traced by a function on an open interval.** If `g` is continuous on `Ioo a b`, tends
to `u` at `a` from the right and to `v` at `b` from the left, then `g` traverses a path from `u` to
`v`: the extension `TauCeti.extendIoo a b u v g` of `g` across the two ends, read along the affine
parametrisation `AffineMap.lineMap a b` of `Icc a b` by the unit interval.

Its values on the interior of the unit interval are those of `g`
(`TauCeti.Path.ofContinuousOnIoo_apply_of_mem_Ioo`) and its range is `closure (g '' Ioo a b)`
(`TauCeti.Path.range_ofContinuousOnIoo`); the endpoints `u` and `v` need not themselves be values
of `g`. Compute with it through `TauCeti.Path.ofContinuousOnIoo_apply` rather than through the
definition. -/
noncomputable def ofContinuousOnIoo (hab : a < b) (hg : ContinuousOn g (Ioo a b))
    (hu : Tendsto g (𝓝[>] a) (𝓝 u)) (hv : Tendsto g (𝓝[<] b) (𝓝 v)) : Path u v where
  toFun t := extendIoo a b u v g (AffineMap.lineMap a b (t : ℝ))
  continuous_toFun :=
    (continuousOn_Icc_extendIoo hab hg hu hv).comp_continuous
      (by simp only [AffineMap.lineMap_apply_ring]; fun_prop)
      fun t => lineMap_mem_Icc hab.le t
  source' := by simp
  target' := by simp [hab]

/-- The path traced by `g` is the extension of `g` across the two ends of `Ioo a b`, read along the
affine parametrisation of `Icc a b` by the unit interval. -/
@[grind =]
theorem ofContinuousOnIoo_apply (hab : a < b) (hg : ContinuousOn g (Ioo a b))
    (hu : Tendsto g (𝓝[>] a) (𝓝 u)) (hv : Tendsto g (𝓝[<] b) (𝓝 v)) (t : I) :
    ofContinuousOnIoo hab hg hu hv t = extendIoo a b u v g (AffineMap.lineMap a b (t : ℝ)) :=
  -- Parenthesised: the bare-`rfl` elaborator additionally demands that `ofContinuousOnIoo` be
  -- `@[expose]`d, which it cannot be while its proof fields use private lemmas of this file.
  (rfl)

/-- **On the interior of the unit interval the path traced by `g` is `g` itself**, along the affine
parametrisation. The endpoints are excluded because there the values of `g` are unconstrained: they
need not be the limits `u` and `v`, which is what makes the construction more than a
reparametrisation. -/
@[simp]
theorem ofContinuousOnIoo_apply_of_mem_Ioo (hab : a < b) (hg : ContinuousOn g (Ioo a b))
    (hu : Tendsto g (𝓝[>] a) (𝓝 u)) (hv : Tendsto g (𝓝[<] b) (𝓝 v)) {t : I}
    (ht : t ∈ Ioo (0 : I) 1) :
    ofContinuousOnIoo hab hg hu hv t = g (AffineMap.lineMap a b (t : ℝ)) := by
  rw [ofContinuousOnIoo_apply, extendIoo_apply_of_mem_Ioo (lineMap_mem_Ioo hab ht)]

/-- **The range of the path traced by `g` is the closure of the curve.** The path traverses the
closed interval `Icc a b`, which is the closure of `Ioo a b` and compact, so its image under a map
continuous there is the closure of the image of `Ioo a b`. In particular the closure of a curve
defined on an open interval and converging at both ends is path-connected. -/
theorem range_ofContinuousOnIoo [T2Space X] (hab : a < b) (hg : ContinuousOn g (Ioo a b))
    (hu : Tendsto g (𝓝[>] a) (𝓝 u)) (hv : Tendsto g (𝓝[<] b) (𝓝 v)) :
    range (ofContinuousOnIoo hab hg hu hv) = closure (g '' Ioo a b) := by
  have hcl : closure (Ioo a b) = Icc a b := closure_Ioo hab.ne
  have hparam : range (fun t : I => AffineMap.lineMap a b (t : ℝ)) = Icc a b := by
    rw [← image_eq_range, ← segment_eq_image_lineMap, segment_eq_Icc hab.le]
  have hcont : ContinuousOn (extendIoo a b u v g) (closure (Ioo a b)) :=
    hcl ▸ continuousOn_Icc_extendIoo hab hg hu hv
  have heq : EqOn (extendIoo a b u v g) g (Ioo a b) := fun _ hx => extendIoo_apply_of_mem_Ioo hx
  have hfun : ⇑(ofContinuousOnIoo hab hg hu hv)
      = extendIoo a b u v g ∘ fun t : I => AffineMap.lineMap a b (t : ℝ) :=
    funext (ofContinuousOnIoo_apply hab hg hu hv)
  rw [hfun, range_comp, hparam, ← hcl, image_closure_of_isCompact (hcl ▸ isCompact_Icc) hcont,
    heq.image_eq]

end Path

end TauCeti
