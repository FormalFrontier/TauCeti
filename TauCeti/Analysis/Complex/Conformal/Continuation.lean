/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Analytic continuation along a path

An **analytic continuation along a path** `γ` is the classical device that turns a single
holomorphic germ into a multi-valued function: one carries the germ along `γ`, re-expanding it at
each parameter time. This file introduces that notion and proves its fundamental property, that a
continuation is **determined by its initial germ**.

A continuation is recorded as a family `f : X → ℂ → ℂ` of functions indexed by the path parameter,
subject to the requirement that `f t` be analytic at `γ t` and that the germ of `f u` at `γ u`
agree with the germ of `f t` at `γ u` for all `u` near `t`. Equivalently — and this is the way to
read the definition — the assignment `t ↦ (germ of f t at γ t)` is a *continuous lift* of `γ` to
the étale space of holomorphic germs. The classical "chain of overlapping discs" definition is the
same condition written with explicit discs; the germ formulation avoids carrying the discs around.

The parameter space `X` is an arbitrary topological space, and the parameter set `s : Set X` is
constrained only by `IsPreconnected` where the mathematics needs it. Nothing here uses the order or
the field structure of the reals, so the usual `X = ℝ` with `s = Set.Icc 0 1` and Mathlib's
`Path`, whose parameter space is `unitInterval`, are both directly available.

## The uniqueness theorem

`TauCeti.IsAnalyticContinuationAlong.eventuallyEq`: two continuations along the same path over a
preconnected parameter set whose germs agree at one parameter time agree at every parameter time.

The proof is the standard connectedness argument. Germ agreement is a *locally constant* property
of the parameter: at a time `t`, both `f t` and `g t` are analytic on a common disc `D` about
`γ t`, so by the identity principle (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) their
germs agree at one point of `D` exactly when they agree at every point of `D` — and for `u` near
`t` the point `γ u` lies in `D` while the germs of `f u, g u` at `γ u` are those of `f t, g t`.
A locally constant property on a preconnected parameter set is constant
(`IsLocallyConstant.apply_eq_of_preconnectedSpace`).

## Relation to the monodromy theorem

This is the L4 prerequisite that the monodromy theorem of the conformal-mapping roadmap needs:
uniqueness of the continuation along a *fixed* path. The monodromy theorem itself compares
continuations along *homotopic* paths, and in the étale-space picture is an instance of Mathlib's
abstract `IsLocalHomeomorph.monodromy_theorem` (`Mathlib/Topology/Homotopy/Lifting.lean`), whose
docstring describes exactly this application; the uniqueness proved here is the concrete form of
the separatedness hypothesis that abstract theorem consumes. Building the étale space of
holomorphic germs and deducing monodromy from it is left to a follow-up.

## Main definitions and results

* `TauCeti.IsAnalyticContinuationAlong` — `f` is an analytic continuation along `γ` over the
  parameter set `s`.
* `TauCeti.IsAnalyticContinuationAlong.const`, `.of_differentiableOn` — a holomorphic function
  continues itself along any path in its domain.
* `TauCeti.IsAnalyticContinuationAlong.congr` — only the carried germs matter.
* `TauCeti.IsAnalyticContinuationAlong.deriv`, `.add`, `.mul` — continuations are closed under the
  germ-wise operations.
* `TauCeti.IsAnalyticContinuationAlong.eventuallyEq` — **uniqueness**: a continuation over a
  preconnected parameter set is determined by its germ at a single time.
* `TauCeti.IsAnalyticContinuationAlong.eventuallyEq_of_mapsTo` — continuing a holomorphic function
  along a path that stays inside its domain gives that function back.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 8 §1.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX §2–3.
* W. Rudin, *Real and Complex Analysis*, Ch. 16.
-/

public section

namespace TauCeti

open Filter Metric Topology

variable {X : Type*} [TopologicalSpace X] {f g : X → ℂ → ℂ} {γ : X → ℂ} {s : Set X}

/-! ### Germ agreement is a locally constant property -/

/-- Two functions analytic on a ball whose germs agree at one point of the ball have equal germs
at every point of the ball. This is the identity principle in germ form: the ball is preconnected,
so agreement near one of its points propagates to all of it, and the ball is open, so agreement on
it is agreement near each of its points. -/
theorem eventuallyEq_nhds_of_analyticOnNhd_ball {F G : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball c r)) (hG : AnalyticOnNhd ℂ G (ball c r)) {z w : ℂ}
    (hz : z ∈ ball c r) (hw : w ∈ ball c r) (h : F =ᶠ[𝓝 z] G) :
    F =ᶠ[𝓝 w] G :=
  eventually_of_mem (isOpen_ball.mem_nhds hw)
    (hF.eqOn_of_preconnected_of_eventuallyEq hG (convex_ball c r).isPreconnected hz h)

/-- **Germ agreement is locally constant.** If `F` and `G` are both analytic at `z`, then for all
`w` near `z` the germs of `F` and `G` agree at `w` exactly when they agree at `z`. -/
theorem eventually_eventuallyEq_iff_of_analyticAt {F G : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z)
    (hG : AnalyticAt ℂ G z) :
    ∀ᶠ w in 𝓝 z, ((F =ᶠ[𝓝 w] G) ↔ (F =ᶠ[𝓝 z] G)) := by
  obtain ⟨r₁, hr₁, hF'⟩ := hF.exists_ball_analyticOnNhd
  obtain ⟨r₂, hr₂, hG'⟩ := hG.exists_ball_analyticOnNhd
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have hFr : AnalyticOnNhd ℂ F (ball z (min r₁ r₂)) :=
    hF'.mono (ball_subset_ball (min_le_left _ _))
  have hGr : AnalyticOnNhd ℂ G (ball z (min r₁ r₂)) :=
    hG'.mono (ball_subset_ball (min_le_right _ _))
  have hz : z ∈ ball z (min r₁ r₂) := mem_ball_self hr
  filter_upwards [ball_mem_nhds z hr] with w hw
  exact ⟨fun h => eventuallyEq_nhds_of_analyticOnNhd_ball hFr hGr hw hz h,
    fun h => eventuallyEq_nhds_of_analyticOnNhd_ball hFr hGr hz hw h⟩

/-- A property that is locally constant along a preconnected set is constant along it.

This is `IsLocallyConstant.apply_eq_of_preconnectedSpace` transported to the subspace `s`; it is
kept private because the general-topology statement belongs upstream rather than in a
complex-analysis file. -/
private theorem eq_of_isPreconnected_of_eventually_iff (hs : IsPreconnected s) {P : X → Prop}
    (hP : ∀ t ∈ s, ∀ᶠ u in 𝓝[s] t, (P u ↔ P t)) {a b : X} (ha : a ∈ s) (hb : b ∈ s) (hPa : P a) :
    P b := by
  have hlc : IsLocallyConstant fun x : s => P x.1 := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨t, ht⟩
    rw [nhds_subtype_eq_comap_nhdsWithin]
    exact Filter.Eventually.comap ((hP t ht).mono fun _ hu => propext hu) _
  haveI : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  rw [hlc.apply_eq_of_preconnectedSpace ⟨b, hb⟩ ⟨a, ha⟩]
  exact hPa

/-! ### Analytic continuation along a path -/

/-- `IsAnalyticContinuationAlong f γ s` says that the family `f` is an **analytic continuation
along the path `γ`** over the parameter set `s`: for each parameter time `t ∈ s` the function `f t`
is analytic at the point `γ t`, and the germ carried at time `t` is locally constant in `t`, in the
sense that `f u` and `f t` have the same germ at `γ u` for every `u ∈ s` close enough to `t`.

Only the germ of `f t` at `γ t` matters; the values of `f t` away from `γ t` are unconstrained.
Reading the germs as points of the étale space of holomorphic germs over `ℂ`, the condition says
precisely that `t ↦ (germ of f t at γ t)` is a continuous lift of `γ`. -/
structure IsAnalyticContinuationAlong (f : X → ℂ → ℂ) (γ : X → ℂ) (s : Set X) : Prop where
  /-- The path is continuous on the parameter set. -/
  continuousOn : ContinuousOn γ s
  /-- At each parameter time the carried function is analytic at the corresponding path point. -/
  analyticAt : ∀ t ∈ s, AnalyticAt ℂ (f t) (γ t)
  /-- The carried germ varies continuously: nearby parameter times carry the same germ. -/
  locallyEq : ∀ t ∈ s, ∀ᶠ u in 𝓝[s] t, f u =ᶠ[𝓝 (γ u)] f t

namespace IsAnalyticContinuationAlong

/-- A continuation restricts to any smaller parameter set. -/
theorem mono (hf : IsAnalyticContinuationAlong f γ s) {s' : Set X} (hs' : s' ⊆ s) :
    IsAnalyticContinuationAlong f γ s' where
  continuousOn := hf.continuousOn.mono hs'
  analyticAt t ht := hf.analyticAt t (hs' ht)
  locallyEq t ht := (hf.locallyEq t (hs' ht)).filter_mono (nhdsWithin_mono t hs')

/-- The constant family is a continuation: a function analytic at every point of the path
continues itself along it. -/
theorem const {F : ℂ → ℂ} (hγ : ContinuousOn γ s) (hF : ∀ t ∈ s, AnalyticAt ℂ F (γ t)) :
    IsAnalyticContinuationAlong (fun _ => F) γ s where
  continuousOn := hγ
  analyticAt := hF
  locallyEq _ _ := .of_forall fun _ => .rfl

/-- A holomorphic function on an open set continues itself along any path that stays in that
set. This is the source of the continuations that a single-valued function admits. -/
theorem of_differentiableOn {U : Set ℂ} {F : ℂ → ℂ} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hγ : ContinuousOn γ s) (hmem : ∀ t ∈ s, γ t ∈ U) :
    IsAnalyticContinuationAlong (fun _ => F) γ s :=
  const hγ fun t ht => hF.analyticOnNhd hU _ (hmem t ht)

/-- **A continuation depends only on the germs it carries.** Replacing each `f t` by a function
with the same germ at `γ t` again gives a continuation along `γ`. -/
protected theorem congr (hf : IsAnalyticContinuationAlong f γ s) {f' : X → ℂ → ℂ}
    (h : ∀ t ∈ s, f' t =ᶠ[𝓝 (γ t)] f t) : IsAnalyticContinuationAlong f' γ s where
  continuousOn := hf.continuousOn
  analyticAt t ht := (hf.analyticAt t ht).congr (h t ht).symm
  locallyEq t ht := by
    have hball := eventually_eventuallyEq_iff_of_analyticAt
      ((hf.analyticAt t ht).congr (h t ht).symm) (hf.analyticAt t ht)
    filter_upwards [(hf.continuousOn t ht).eventually hball, hf.locallyEq t ht,
      self_mem_nhdsWithin] with u hiff hfu hu
    exact ((h u hu).trans hfu).trans (hiff.mpr (h t ht)).symm

/-- Differentiating a continuation term by term gives a continuation of the derivative germ. -/
protected theorem deriv (hf : IsAnalyticContinuationAlong f γ s) :
    IsAnalyticContinuationAlong (fun t => _root_.deriv (f t)) γ s where
  continuousOn := hf.continuousOn
  analyticAt t ht := (hf.analyticAt t ht).deriv
  locallyEq t ht := (hf.locallyEq t ht).mono fun _ hu => hu.deriv

/-- Continuations add: the pointwise sum family `f + g` continues along `γ` as well. -/
protected theorem add (hf : IsAnalyticContinuationAlong f γ s)
    (hg : IsAnalyticContinuationAlong g γ s) :
    IsAnalyticContinuationAlong (f + g) γ s where
  continuousOn := hf.continuousOn
  analyticAt t ht := (hf.analyticAt t ht).add (hg.analyticAt t ht)
  locallyEq t ht := by
    filter_upwards [hf.locallyEq t ht, hg.locallyEq t ht] with u hu hu' using hu.add hu'

/-- Continuations multiply: the pointwise product family `f * g` continues along `γ` as well. -/
protected theorem mul (hf : IsAnalyticContinuationAlong f γ s)
    (hg : IsAnalyticContinuationAlong g γ s) :
    IsAnalyticContinuationAlong (f * g) γ s where
  continuousOn := hf.continuousOn
  analyticAt t ht := (hf.analyticAt t ht).mul (hg.analyticAt t ht)
  locallyEq t ht := by
    filter_upwards [hf.locallyEq t ht, hg.locallyEq t ht] with u hu hu' using hu.mul hu'

/-! ### Uniqueness -/

/-- Agreement of two continuations along the same path is a locally constant property of the
parameter. This is the local step of the uniqueness theorem. -/
theorem eventually_eventuallyEq_iff (hf : IsAnalyticContinuationAlong f γ s)
    (hg : IsAnalyticContinuationAlong g γ s) {t : X} (ht : t ∈ s) :
    ∀ᶠ u in 𝓝[s] t, ((f u =ᶠ[𝓝 (γ u)] g u) ↔ (f t =ᶠ[𝓝 (γ t)] g t)) := by
  have hball := eventually_eventuallyEq_iff_of_analyticAt (hf.analyticAt t ht) (hg.analyticAt t ht)
  filter_upwards [(hf.continuousOn t ht).eventually hball, hf.locallyEq t ht, hg.locallyEq t ht]
    with u hiff hfu hgu
  exact ⟨fun h => hiff.mp (hfu.symm.trans (h.trans hgu)),
    fun h => hfu.trans ((hiff.mpr h).trans hgu.symm)⟩

/-- **Uniqueness of analytic continuation along a path.** Two analytic continuations along the same
path, over a preconnected parameter set, that carry the same germ at one parameter time carry the
same germ at every parameter time.

Preconnectedness of the parameter set cannot be dropped: over a two-point parameter set the
hypotheses put no relation at all between the germs carried at its two points. -/
theorem eventuallyEq (hf : IsAnalyticContinuationAlong f γ s)
    (hg : IsAnalyticContinuationAlong g γ s) (hs : IsPreconnected s) {a b : X} (ha : a ∈ s)
    (hb : b ∈ s) (hab : f a =ᶠ[𝓝 (γ a)] g a) :
    f b =ᶠ[𝓝 (γ b)] g b :=
  eq_of_isPreconnected_of_eventually_iff hs
    (P := fun t => f t =ᶠ[𝓝 (γ t)] g t) (fun _ ht => hf.eventually_eventuallyEq_iff hg ht) ha hb
    hab

/-- Two continuations along the same path that carry the same germ at one parameter time take the
same value at every parameter time. -/
theorem eq_of_eventuallyEq (hf : IsAnalyticContinuationAlong f γ s)
    (hg : IsAnalyticContinuationAlong g γ s) (hs : IsPreconnected s) {a b : X} (ha : a ∈ s)
    (hb : b ∈ s) (hab : f a =ᶠ[𝓝 (γ a)] g a) :
    f b (γ b) = g b (γ b) :=
  (hf.eventuallyEq hg hs ha hb hab).eq_of_nhds

/-- **A single-valued function is its own continuation.** If a path stays inside an open set on
which `F` is holomorphic, then any continuation along that path which starts at the germ of `F`
carries the germ of `F` throughout. So continuing a holomorphic function inside its domain never
produces a new branch: new branches can only appear once the path leaves the domain. -/
theorem eventuallyEq_of_mapsTo {U : Set ℂ} {F : ℂ → ℂ} (hf : IsAnalyticContinuationAlong f γ s)
    (hs : IsPreconnected s) (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    (hmem : ∀ t ∈ s, γ t ∈ U) {a b : X} (ha : a ∈ s) (hb : b ∈ s) (hab : f a =ᶠ[𝓝 (γ a)] F) :
    f b =ᶠ[𝓝 (γ b)] F :=
  hf.eventuallyEq (of_differentiableOn hU hF hf.continuousOn hmem) hs ha hb hab

end IsAnalyticContinuationAlong

end TauCeti
